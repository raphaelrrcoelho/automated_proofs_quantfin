"""Central coordinator for hybrid verification."""

from __future__ import annotations

import asyncio
import logging
import time
from concurrent.futures import ThreadPoolExecutor
from typing import Any

from .confidence import annotate_cross_validation, compute_overall_confidence
from .lean_backend import LeanBackend
from .models import (
    Backend,
    BackendResult,
    TheoremStatement,
    VerificationResult,
    VerificationStatus,
)
from .router import Router
from .sympy_verifier import SymPyVerifier

logger = logging.getLogger(__name__)


class Orchestrator:
    """Dispatches verification to backends based on routing decisions."""

    def __init__(
        self,
        router: Router | None = None,
        lean: LeanBackend | None = None,
        sympy: SymPyVerifier | None = None,
        max_workers: int = 3,
        default_timeout: float = 60.0,
    ):
        self._router = router or Router()
        self._backends: dict[Backend, Any] = {}
        self._default_timeout = default_timeout
        self._executor = ThreadPoolExecutor(max_workers=max_workers)

        # Register available backends. Lean is the only formal backend;
        # SymPy is kept as a legacy/manual fallback (no active route uses it).
        if lean is not None:
            self._backends[Backend.LEAN] = lean
        else:
            self._backends[Backend.LEAN] = LeanBackend()

        if sympy is not None:
            self._backends[Backend.SYMPY] = sympy
        else:
            self._backends[Backend.SYMPY] = SymPyVerifier()

    async def verify(
        self,
        theorem: TheoremStatement,
        timeout: float | None = None,
    ) -> VerificationResult:
        """Verify a single theorem using routed backends."""
        timeout = timeout or self._default_timeout
        decision = self._router.route(theorem.domain)
        result = VerificationResult(theorem=theorem)

        if decision.parallel:
            await self._dispatch_parallel(theorem, decision.backends, result, timeout)
        else:
            await self._dispatch_sequential(theorem, decision.backends, result, timeout)

        result.overall_confidence = compute_overall_confidence(result)
        annotate_cross_validation(result)
        return result

    async def _dispatch_sequential(
        self,
        theorem: TheoremStatement,
        backends: list[Backend],
        result: VerificationResult,
        timeout: float,
    ) -> None:
        """Try backends in order, stop on first success."""
        for backend_key in backends:
            backend = self._backends.get(backend_key)
            if backend is None:
                continue

            # Skip if no code for this backend
            if backend_key not in theorem.code:
                result.results[backend_key] = BackendResult(
                    backend=backend_key,
                    status=VerificationStatus.NOT_ATTEMPTED,
                    error_message=f"No {backend_key.value} code provided",
                )
                continue

            if not backend.is_available():
                result.results[backend_key] = BackendResult(
                    backend=backend_key,
                    status=VerificationStatus.UNAVAILABLE,
                    error_message=f"{backend_key.value} backend not available",
                )
                continue

            logger.info(
                "Verifying %s with %s", theorem.name, backend_key.value
            )
            backend_result = await backend.verify(theorem, timeout)
            result.results[backend_key] = backend_result

            if backend_result.status == VerificationStatus.SUCCESS:
                logger.info(
                    "%s succeeded for %s", backend_key.value, theorem.name
                )
                break  # Early exit on success

    async def _dispatch_parallel(
        self,
        theorem: TheoremStatement,
        backends: list[Backend],
        result: VerificationResult,
        timeout: float,
    ) -> None:
        """Dispatch to all backends in parallel."""
        tasks = []
        for backend_key in backends:
            backend = self._backends.get(backend_key)
            if backend is None:
                continue
            if backend_key not in theorem.code:
                result.results[backend_key] = BackendResult(
                    backend=backend_key,
                    status=VerificationStatus.NOT_ATTEMPTED,
                    error_message=f"No {backend_key.value} code provided",
                )
                continue
            if not backend.is_available():
                result.results[backend_key] = BackendResult(
                    backend=backend_key,
                    status=VerificationStatus.UNAVAILABLE,
                    error_message=f"{backend_key.value} backend not available",
                )
                continue

            tasks.append((backend_key, backend.verify(theorem, timeout)))

        if tasks:
            coros = [coro for _, coro in tasks]
            keys = [key for key, _ in tasks]
            results = await asyncio.gather(*coros, return_exceptions=True)

            for key, res in zip(keys, results):
                if isinstance(res, Exception):
                    result.results[key] = BackendResult(
                        backend=key,
                        status=VerificationStatus.FAILED,
                        error_message=str(res),
                    )
                else:
                    result.results[key] = res

    async def verify_batch(
        self,
        theorems: list[TheoremStatement],
        timeout: float | None = None,
    ) -> list[VerificationResult]:
        """Verify a list of theorems sequentially."""
        results = []
        for theorem in theorems:
            result = await self.verify(theorem, timeout)
            results.append(result)
        return results

    async def verify_batch_parallel(
        self,
        theorems: list[TheoremStatement],
        timeout: float | None = None,
    ) -> list[VerificationResult]:
        """Verify a list of theorems in parallel."""
        coros = [self.verify(t, timeout) for t in theorems]
        return list(await asyncio.gather(*coros, return_exceptions=False))

    def shutdown(self) -> None:
        """Shut down all backends and the thread pool."""
        for backend in self._backends.values():
            try:
                backend.shutdown()
            except Exception as e:
                logger.warning("Error shutting down backend: %s", e)
        self._executor.shutdown(wait=False)
        logger.info("Orchestrator shut down")

"""Lean 4 verification backend using lean-interact."""

from __future__ import annotations

import logging
import shutil
import threading
import time
from typing import Any

from .models import (
    Backend,
    BackendResult,
    ConfidenceLevel,
    TheoremStatement,
    VerificationStatus,
)

logger = logging.getLogger(__name__)


class LeanBackend:
    """Lean 4 backend driving lean-interact's AutoLeanServer against the
    in-repo Lake project (repo root by default).

    All authoritative project state lives in the Lake project: ``lakefile.lean``
    declares the dependency set, ``lake-manifest.json`` freezes transitive
    revisions, ``lean-toolchain`` pins the Lean version, and
    ``QuantFin/*.lean`` holds the proof library. Benchmark snippets only
    typecheck against the prebuilt library, so complex derivations live as
    real Lean files (full ``lake build`` memory budget + incremental
    compilation + LSP authoring) and benchmarks just import + reference them
    by name.
    """

    def __init__(
        self,
        local_project: str = ".",
        *,
        memory_hard_limit_mb: int | None = None,
        max_total_memory: float = 0.8,
        max_process_memory: float | None = 0.8,
    ):
        """
        Args:
            local_project: Lake project directory.
            memory_hard_limit_mb: OS-enforced hard cap on the Lean process's
                resident memory. ``None`` (default) = no cap. Long-lived
                daemons should set this (e.g. ``8000``) so heavy proofs
                cannot OOM the host.
            max_total_memory: Soft cap on *system-wide* memory before the
                Lean server auto-restarts (proportion in [0,1]). Default
                0.8. Daemons should raise to ~0.9 to avoid mid-work restarts.
            max_process_memory: Soft cap on the Lean process memory (as a
                fraction of ``memory_hard_limit_mb``) before auto-restart.
                ``None`` disables. Daemons doing long sessions should set
                this to ``None`` so a slow leak doesn't kill the session.
        """
        self._local_project = local_project
        self._server: Any = None
        self._project: Any = None
        self._lock = threading.Lock()
        self._memory_hard_limit_mb = memory_hard_limit_mb
        self._max_total_memory = max_total_memory
        self._max_process_memory = max_process_memory

    @property
    def name(self) -> str:
        return "lean"

    def is_available(self) -> bool:
        try:
            import lean_interact  # noqa: F401
        except ImportError:
            return False
        return shutil.which("lake") is not None

    def _ensure_server(self) -> None:
        if self._server is not None:
            return

        from lean_interact import (
            AutoLeanServer,
            LeanREPLConfig,
            LocalProject,
        )

        self._project = LocalProject(
            directory=self._local_project,
            auto_build=True,
        )
        config = LeanREPLConfig(
            project=self._project,
            verbose=False,
            memory_hard_limit_mb=self._memory_hard_limit_mb,
            # `enable_incremental_optimization` and `enable_parallel_elaboration`
            # are True by default — keep them; both help per-request latency
            # at modest memory cost.
        )
        self._server = AutoLeanServer(
            config,
            max_total_memory=self._max_total_memory,
            max_process_memory=self._max_process_memory,
        )
        logger.info(
            "Lean server initialized (LocalProject=%s, hard_cap=%sMB, "
            "soft_total=%.2f, soft_proc=%s)",
            self._local_project,
            self._memory_hard_limit_mb,
            self._max_total_memory,
            self._max_process_memory,
        )

    async def verify(
        self,
        theorem: TheoremStatement,
        timeout: float = 60.0,
    ) -> BackendResult:
        """Verify a theorem using Lean 4."""
        start = time.monotonic()

        if not self.is_available():
            return BackendResult(
                backend=Backend.LEAN,
                status=VerificationStatus.UNAVAILABLE,
                error_message="lean-interact not installed",
            )

        code = theorem.code.get(Backend.LEAN)
        if not code:
            return BackendResult(
                backend=Backend.LEAN,
                status=VerificationStatus.NOT_ATTEMPTED,
                error_message="No Lean code provided for this theorem",
            )

        with self._lock:
            try:
                self._ensure_server()
                return self._run_verification(code, start)
            except Exception as e:
                elapsed = time.monotonic() - start
                logger.error("Lean verification failed: %s", e)
                return BackendResult(
                    backend=Backend.LEAN,
                    status=VerificationStatus.FAILED,
                    error_message=str(e),
                    elapsed_seconds=elapsed,
                )

    def _run_verification(self, code: str, start: float) -> BackendResult:
        """Execute Lean code and parse the response."""
        from lean_interact import Command

        response = self._server.run(Command(cmd=code))
        elapsed = time.monotonic() - start
        raw = str(response)

        messages = getattr(response, "messages", []) or []
        error_msgs = [
            m for m in messages
            if getattr(m, "severity", None) == "error"
        ]

        legacy_errors = getattr(response, "errors", None)
        if not error_msgs and legacy_errors:
            error_msgs = legacy_errors

        has_errors_attr = getattr(response, "has_errors", None)
        if callable(has_errors_attr):
            errored = has_errors_attr()
        else:
            errored = bool(error_msgs)

        sorries = getattr(response, "sorries", [])
        sorry_count = len(sorries) if isinstance(sorries, list) else 0

        if errored:
            error_strs = []
            for m in error_msgs:
                data = getattr(m, "data", None)
                pos = getattr(m, "start_pos", None)
                if data is not None:
                    if pos is not None:
                        error_strs.append(f"line {getattr(pos, 'line', '?')}: {data}")
                    else:
                        error_strs.append(str(data))
                else:
                    error_strs.append(str(m))
            return BackendResult(
                backend=Backend.LEAN,
                status=VerificationStatus.FAILED,
                confidence=ConfidenceLevel.L0,
                raw_output=raw,
                error_message="; ".join(error_strs) if error_strs else "(unknown error)",
                elapsed_seconds=elapsed,
            )

        if sorry_count > 0:
            confidence = (
                ConfidenceLevel.L4 if sorry_count == 1 else ConfidenceLevel.L3
            )
            return BackendResult(
                backend=Backend.LEAN,
                status=VerificationStatus.PARTIAL,
                confidence=confidence,
                raw_output=raw,
                sorry_count=sorry_count,
                elapsed_seconds=elapsed,
            )

        return BackendResult(
            backend=Backend.LEAN,
            status=VerificationStatus.SUCCESS,
            confidence=ConfidenceLevel.L5,
            raw_output=raw,
            elapsed_seconds=elapsed,
        )

    def shutdown(self) -> None:
        """Shut down the Lean server and clean up."""
        with self._lock:
            if self._server is not None:
                try:
                    self._server.close()
                except Exception:
                    pass
                self._server = None

            if self._project is not None:
                try:
                    self._project.cleanup()
                except Exception:
                    pass
                self._project = None

        logger.info("Lean backend shut down")

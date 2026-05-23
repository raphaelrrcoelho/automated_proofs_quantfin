"""CLI entry point for the Lean verification runner.

Usage:
    python -m tools.verify.cli benchmarks/stochastic_calculus.json [-v] [--config hybrid_verify.toml] [--timeout 120]
"""

from __future__ import annotations

import argparse
import asyncio
import json
import logging
import sys
from pathlib import Path

from .config import load_config
from .lean_backend import LeanBackend
from .models import Backend, TheoremStatement, VerificationStatus
from .orchestrator import Orchestrator
from .router import Router
from .sympy_verifier import SymPyVerifier


def load_theorems(path: str | Path) -> list[TheoremStatement]:
    """Load theorems from a JSON file."""
    with open(path) as f:
        data = json.load(f)

    if isinstance(data, list):
        return [TheoremStatement.from_dict(t) for t in data]

    # Support {"theorems": [...]} wrapper
    if "theorems" in data:
        return [TheoremStatement.from_dict(t) for t in data["theorems"]]

    raise ValueError(f"Unexpected JSON structure in {path}")


def format_result(vr) -> str:
    """Format a VerificationResult for display."""
    lines = [
        f"\n{'='*60}",
        f"Theorem: {vr.theorem.name}",
        f"  ID: {vr.theorem.id}",
        f"  Domain: {vr.theorem.domain.value}",
        f"  Overall confidence: {vr.overall_confidence.name} ({vr.overall_confidence.value}/5)",
        f"  Verified: {vr.is_verified}",
    ]

    for backend, result in vr.results.items():
        status_icon = {
            VerificationStatus.SUCCESS: "[OK]",
            VerificationStatus.PARTIAL: "[~~]",
            VerificationStatus.FAILED: "[FAIL]",
            VerificationStatus.TIMEOUT: "[TIME]",
            VerificationStatus.UNAVAILABLE: "[N/A]",
            VerificationStatus.NOT_ATTEMPTED: "[SKIP]",
        }.get(result.status, "[??]")

        lines.append(
            f"  {status_icon} {backend.value}: "
            f"{result.status.value} "
            f"(confidence={result.confidence.name}, "
            f"elapsed={result.elapsed_seconds:.2f}s)"
        )
        if result.error_message:
            lines.append(f"       Error: {result.error_message}")
        if result.sorry_count > 0:
            lines.append(f"       Sorries: {result.sorry_count}")

    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="hybrid-verify",
        description="Lean 4 verification runner for the HybridVerify quant-finance library",
    )
    parser.add_argument(
        "theorems",
        type=str,
        help="Path to JSON file with theorem definitions",
    )
    parser.add_argument(
        "--config",
        type=str,
        default=None,
        help="Path to TOML config file",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=None,
        help="Per-theorem timeout in seconds",
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Enable verbose logging",
    )
    parser.add_argument(
        "--parallel",
        action="store_true",
        help="Verify all theorems in parallel",
    )

    args = parser.parse_args(argv)

    # Setup logging
    log_level = logging.DEBUG if args.verbose else logging.WARNING
    logging.basicConfig(
        level=log_level,
        format="%(asctime)s %(name)s %(levelname)s %(message)s",
    )

    # Load config
    config = load_config(args.config)
    timeout = args.timeout or config.orchestrator.default_timeout

    # Load theorems
    theorem_path = Path(args.theorems)
    if not theorem_path.exists():
        print(f"Error: theorem file not found: {theorem_path}", file=sys.stderr)
        return 1

    theorems = load_theorems(theorem_path)
    print(f"Loaded {len(theorems)} theorems from {theorem_path}")

    # Create backends. Lean is the only formal backend; SymPy is kept as a
    # legacy/manual fallback (no active route uses it).
    lean = LeanBackend(local_project=config.lean.local_project)
    sympy_backend = SymPyVerifier()

    # Create orchestrator
    orchestrator = Orchestrator(
        router=Router(),
        lean=lean,
        sympy=sympy_backend,
        max_workers=config.orchestrator.max_workers,
        default_timeout=timeout,
    )

    # Run verification
    try:
        if args.parallel:
            results = asyncio.run(
                orchestrator.verify_batch_parallel(theorems, timeout)
            )
        else:
            results = asyncio.run(
                orchestrator.verify_batch(theorems, timeout)
            )
    finally:
        orchestrator.shutdown()

    # Print results
    successes = 0
    partials = 0
    failures = 0

    for vr in results:
        print(format_result(vr))
        if vr.is_verified:
            successes += 1
        elif any(
            r.status == VerificationStatus.PARTIAL for r in vr.results.values()
        ):
            partials += 1
        else:
            failures += 1

    print(f"\n{'='*60}")
    print(f"Summary: {successes} verified, {partials} partial, {failures} failed")
    print(f"Total theorems: {len(results)}")

    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

# AGENTS.md

This file provides guidance to Codex (Codex.ai/code) when working with code in this repository.

## Commands

Preferred all-backends runner is Docker:

```bash
docker compose -f docker/docker-compose.yml build verify
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/<file>.json -v --config hybrid_verify.toml --timeout 120
```

The default compose command runs `benchmarks/cross_validated.json`:

```bash
docker compose -f docker/docker-compose.yml run --rm verify
```

Use the local Python CLI only for quick checks or when the local Lean/Isabelle toolchains are known to be configured:

```bash
python -m python.cli benchmarks/<file>.json [-v] [--config hybrid_verify.toml] [--timeout 120] [--parallel]
```

`-v` enables debug logging. `--parallel` verifies all theorems concurrently (otherwise sequential per-theorem; intra-theorem dispatch is governed by the router).

Install:

```bash
pip install -r requirements.txt                       # SymPy only (Lean/Isabelle skipped if missing)
pip install -e ".[all]"                               # adds lean-interact + isabelle-client
pip install -e ".[dev]"                               # pytest + pytest-asyncio
```

Fast regression checks:

```bash
python3 -m pytest tests/test_router.py
python3 -m python.coverage_report
```

`tests/test_router.py` enforces formal-only routing, no active `code.sympy`, no active `sorry`/`admit`, and a declared formalization-faithfulness status for every benchmark theorem.

Delivery/status docs:
- `FORMALIZATION_STATUS.md`: authoritative current audit, safe claim wording, verification evidence, and remaining placeholders.
- `QUANTFIN_ROADMAP.md`: next-steps roadmap for the unblocked quant-finance work.

Docker notes for future agents:
- `docker/Dockerfile.verify` is intended to be the canonical reproducible environment for Python + SymPy + Lean + Isabelle.
- It installs the project with `pip install -e ".[all]"`, so both `lean-interact` and `isabelle-client` are present.
- It installs Isabelle 2025-2, prebuilds `HOL-Probability` with a `-Xmx2g` build cap, then raises the runtime JVM cap to `-Xmx3g` for `isabelle-client`; the default `-Xmx4g` caused OS-level `Killed` failures on an 8 GB Ubuntu host, while `-Xmx1g`/`-Xmx2g` were too small for different Isabelle phases.
- `hybrid_verify.toml` uses Isabelle session mode (`use_connector = false`) so verification starts the prebuilt `HOL-Probability` session directly. Connector mode starts `Main` and imports the probability stack dynamically, which can OOM even when the heap is already built.
- It installs and sets the repo-pinned Lean toolchain from `lean/lean-toolchain`. Do not run `lake update` against `mathlib` `master` in the Docker build unless the Lean project is intentionally being maintained; that previously pulled a newer Lean release and made the build inconsistent with `hybrid_verify.toml`.
- Compose bind-mounts `python/`, `benchmarks/`, and `hybrid_verify.toml`, and persists `lean-interact`'s Mathlib cache in the `lean_interact_cache` Docker volume. Python/config/benchmark edits should not require rebuilding the Isabelle image; the first Lean run may still populate the named cache.
- The current verifier image prebuilds Isabelle `HOL-Probability`, not the local `HybridVerify` session. The Python Isabelle backend verifies temporary benchmark theories that import `HOL-Probability.Probability`; the local session is not required for CLI verification.
- If Docker build fails under Codex because it cannot write under `~/.docker`, rerun the same `docker compose ...` command with elevated permissions.

## Architecture

Three verification backends (Lean 4, Isabelle/HOL, SymPy) are coordinated by a Python orchestrator. Each theorem in a benchmark JSON file carries a `code` map keyed by backend; the router decides which backends to attempt and in what order, based on the theorem's `domain`.

**Dispatch flow** (`orchestrator.py`):
1. `Router.route(domain)` returns a `RoutingDecision` (ordered backend list + parallel flag).
2. Sequential mode tries backends in order and stops on first SUCCESS (early exit).
3. Parallel mode (only for `MEASURE_THEORY` and `POISSON_PROCESSES`) dispatches to all backends via `asyncio.gather` to enable cross-validation.
4. `compute_overall_confidence` picks the best backend confidence; `annotate_cross_validation` mutates `theorem.metadata` if both Lean and Isabelle succeeded.

**Confidence tiers** (`models.ConfidenceLevel`, scoring in `confidence.py`):
- L5 = formal prover SUCCESS (Lean/Isabelle, no sorries)
- L4 = formal prover PARTIAL with 1 sorry; L3 = >1 sorry
- L2 = SymPy symbolic SUCCESS (cap for SymPy backend)
- L1 = SymPy numerical SUCCESS
- L0 = nothing succeeded

SymPy never returns L3+ even on success — this is intentional, encoding that CAS checks are not formal proofs.

**Routing table** (`router.DEFAULT_ROUTING`) — based on real formalization coverage, not arbitrary:
- Lean-first, then Isabelle where available: `markov_chains`, `ergodic_theory` reduced cores; Isabelle remains available for AFP/HOL-Probability checks.
- Isabelle-first: `central_limit_theorem` (AFP/HOL-Probability libraries)
- Lean-first: `martingales`, `stopping_times`, `brownian_motion` (Mathlib)
- Lean+Isabelle in parallel, no SymPy: `measure_theory`, `poisson_processes` (`PARALLEL_DOMAINS`). Keep this path formal-only unless a benchmark explicitly lacks both formal backends.
- Lean-first, then Isabelle where available, no SymPy fallback: `stochastic_calculus`, `stochastic_differential_equations`, `mathematical_finance`. These Lean entries formalize the symbolic/algebraic proof obligations previously checked by SymPy; they are not full Itô/Girsanov/Black-Scholes library formalizations unless the benchmark metadata says otherwise.
- Historical SymPy snippets may remain under `metadata.cas_reference.sympy`, but active benchmark code must be formal-only. Run `python3 -m pytest tests/test_router.py` after routing or benchmark-code edits.
- Historical SymPy snippets are quarantined under `metadata.cas_reference.sympy`, not active `code.sympy`. Run `python3 -m python.coverage_report` for a static formal coverage summary.
- Every benchmark theorem must declare `metadata.formalization_status`: `full`, `library_wrapper`, `reduced_core`, or `placeholder`. Delivery claims count only `full + library_wrapper`; see `FORMALIZATION_STATUS.md`.
- Do not tell a collaborator that all course theorems are formally proved. Run `python3 -m python.coverage_report` for the current `full / library_wrapper / reduced_core / placeholder` split; delivery claims count only `full + library_wrapper`.

**Backends are lazily initialized**. `LeanBackend._ensure_server` and `IsabelleBackend._ensure_connector`/`_ensure_session` defer the expensive Mathlib/HOL-Probability bootstrap to the first `verify()` call. Both hold a `threading.Lock` since the underlying servers are not thread-safe — async `verify()` calls serialize through the lock.

**SymPy backend dispatch** (`sympy_verifier.py`):
- SymPy is not used by default routing and should not appear as active `code.sympy` in benchmark JSON. Treat it as an explicit/manual backend only.
- If `theorem.metadata["sympy_check_kind"]` is set, dispatches to a typed handler (`ALGEBRAIC_IDENTITY` expects `lhs`/`rhs`; `MOMENT_COMPUTATION` expects `expected`/`computed`; `DERIVATIVE_CHECK` expects `expr`/`var`/`expected`; `INTEGRAL_CHECK` expects `integrand`/`var`/`limits`/`expected`; etc.).
- Otherwise `_eval_code` execs the code and reads a `result` dict (must contain `"verified"`).
- **Convention**: if a benchmark's SymPy code already builds its own `result` dict, do NOT also set `sympy_check_kind` — the typed handlers will look for handler-specific variables (`lhs`/`rhs`/etc.) and fail. Pick one or the other.
- All execution uses `exec()` with a controlled namespace; treat benchmark JSON as trusted input.

**Config** (`config.py`): TOML loader using stdlib `tomllib` (Python 3.11+). Searches `hybrid_verify.toml` then `pyproject.toml` (`[tool.hybrid-verify]`). Defaults are baked into the dataclasses, so a missing file is fine.

**Models** (`models.py`): `TheoremStatement` is a frozen dataclass — but `metadata` is a mutable dict by reference, which is how `annotate_cross_validation` writes back results. `code` is keyed by `Backend` enum (not strings); `from_dict` does the conversion at load time.

## Benchmark JSON shape

Either a top-level list of theorem dicts, or `{"theorems": [...], "description": "..."}`. Each theorem requires `id`, `name`, `domain` (must match a `Domain` enum value), and a `code` map with active formal backend-name keys (`"lean"`, `"isabelle"`). Optional: `description`, `metadata`. Historical CAS snippets, if retained, belong under `metadata.cas_reference.sympy`, never active `code.sympy`. Files are organized by Saporito stochastic-processes textbook chapters.

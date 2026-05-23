# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repo is

A Lean 4 library of formally verified quant-finance theorems, built on Mathlib
and Degenne's BrownianMotion package. The Lean library is the artifact; the
Python runner under `tools/verify/` is a CLI harness that drives
`lean-interact` against benchmark JSONs. The library is self-sufficient: a
plain `lake build` from the repo root is the canonical verification.

The repo was previously framed as a "hybrid Lean + Isabelle + SymPy
verification framework." That framing is gone — Isabelle has been removed
and SymPy is retained only as a legacy fallback (no active route uses it).
See `docs/superpowers/specs/2026-05-23-repo-reorganization-design.md` for
the structural rationale.

## Commands

Preferred runner is Docker. The image is hosted on GHCR
(`ghcr.io/raphaelrrcoelho/quantfin-verify`, private). Pull-first,
build-fallback:

```bash
# First time on a machine — log in to GHCR with your gh OAuth token:
TOKEN=$(grep -E '^[[:space:]]+oauth_token:' ~/.config/gh/hosts.yml | head -1 | awk '{print $2}')
echo "$TOKEN" | docker login ghcr.io -u raphaelrrcoelho --password-stdin
# (gh auth must include `read:packages` scope; refresh with
#  `gh auth refresh -h github.com -s read:packages` if needed.)

# Refresh the image to the latest published version:
docker compose -f docker/docker-compose.yml pull verify

# Run a benchmark:
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/<file>.json -v --config hybrid_verify.toml --timeout 120

# Force a local rebuild (only when changing Dockerfile/Lean toolchain):
docker compose -f docker/docker-compose.yml build verify
# Then re-publish; see docker/docker-compose.yml header for the docker push commands.
```

The default compose command runs `benchmarks/cross_validated.json`:

```bash
docker compose -f docker/docker-compose.yml run --rm verify
```

Do NOT run `python -m tools.verify ...` against the host toolchain. Always go
through the docker `verify` service so Mathlib/Lean versions are pinned and
reproducible.

`-v` enables debug logging. `--parallel` verifies all theorems concurrently
(otherwise sequential per-theorem; intra-theorem dispatch is governed by the
router).

Install (only needed if running outside Docker):

```bash
pip install -r requirements.txt                # SymPy only (Lean skipped if missing)
pip install -e ".[all]"                        # adds lean-interact
pip install -e ".[dev]"                        # pytest + pytest-asyncio
```

Fast regression checks (run inside the verify container so versions match):

```bash
docker compose -f docker/docker-compose.yml run --rm \
    --entrypoint python3 verify -m pytest tests/test_router.py -q
docker compose -f docker/docker-compose.yml run --rm \
    --entrypoint python3 verify -m tools.verify.coverage_report
```

`tests/test_router.py` enforces formal-only routing, no active `code.sympy`,
no active `sorry`/`admit`, and a declared formalization-faithfulness status
for every benchmark theorem.

Delivery/status docs:
- `docs/coverage.md`: per-theorem audit, safe claim wording, verification evidence, and remaining placeholders.
- `docs/roadmap.md`: next-steps roadmap (strategic depth-vs-breadth framing + tactical phase log).
- `docs/bridges.md`: catalogue of Foundations/ → pricing-module bridges.
- `docs/patterns.md`: distilled Lean proof patterns from prior phases.

Docker notes:
- `docker/Dockerfile.verify` installs Lean (via elan), prebuilds the
  `HybridVerify` library against pinned Mathlib + BrownianMotion via
  `lake exe cache get && lake build`, then layers Python + the
  `tools.verify` package.
- Compose bind-mounts `tools/`, `benchmarks/`, `tests/`,
  `hybrid_verify.toml`, and the Lake project pieces at repo root
  (`HybridVerify/`, `HybridVerify.lean`, `lakefile.lean`,
  `lake-manifest.json`, `lean-toolchain`). The Lake bind mount is RW so
  authoring `HybridVerify/*.lean` on host (VS Code + Lean LSP) propagates
  without a rebuild; `.lake/` lives on the host and survives between runs.
- `lean-interact`'s own cache is in the `lean_interact_cache` Docker volume.
- If Docker build fails under Claude/Codex because it cannot write under
  `~/.docker`, rerun the same `docker compose ...` command with elevated
  permissions.

## Architecture

Single Lean 4 verification backend, driven by a thin Python orchestrator.
Each theorem in a benchmark JSON file carries a `code` map keyed by backend;
the router decides which backends to attempt and in what order, based on the
theorem's `domain`. SymPy is kept as a legacy/manual backend but no active
route uses it.

**Dispatch flow** (`tools/verify/orchestrator.py`):
1. `Router.route(domain)` returns a `RoutingDecision` (ordered backend list + parallel flag).
2. Sequential mode tries backends in order and stops on first SUCCESS (early exit).
3. Parallel mode dispatches to all backends via `asyncio.gather` (legacy from the hybrid era; with one active backend it degenerates to single-backend dispatch).
4. `compute_overall_confidence` picks the best backend confidence.

**Confidence tiers** (`tools/verify/models.py` + scoring in `confidence.py`):
- L5 = Lean SUCCESS (no sorries)
- L4 = Lean PARTIAL with 1 sorry; L3 = >1 sorry
- L2 = SymPy symbolic SUCCESS (cap for SymPy backend)
- L1 = SymPy numerical SUCCESS
- L0 = nothing succeeded

SymPy never returns L3+ even on success — this is intentional, encoding that
CAS checks are not formal proofs.

**Routing table** (`router.DEFAULT_ROUTING`) — all routes are Lean-first or
Lean-only; the historical Isabelle entries have been removed:
- Lean-only: `martingales`, `stopping_times`, `brownian_motion`, `measure_theory`, `poisson_processes`, `stochastic_calculus`, `stochastic_differential_equations`, `mathematical_finance`.
- Historical SymPy snippets, if retained, live under `metadata.cas_reference.sympy` — never active `code.sympy`. Run `python3 -m pytest tests/test_router.py` after routing or benchmark-code edits.
- Every benchmark theorem must declare `metadata.formalization_status`: `full`, `library_wrapper`, `reduced_core`, or `placeholder`. Delivery claims count only `full + library_wrapper`; see `docs/coverage.md`.
- Do not tell a collaborator that all course theorems are formally proved. Run `python3 -m tools.verify.coverage_report` for the current `full / library_wrapper / reduced_core / placeholder` split.

**Lean proofs live in `HybridVerify/<Section>/<Module>.lean`, not in JSON
strings**. The library is organized into thematic subdirectories under the
repo-root `HybridVerify/`: `Foundations/`, `BlackScholes/`, `Futures/`,
`Binomial/`, `FixedIncome/`, `Portfolio/`, `Performance/`, `RiskMeasures/`,
`Actuarial/`, `DeFi/`. The Lean backend uses `lean-interact.LocalProject`
pointing at the repo root (configured via `hybrid_verify.toml`
`local_project = "."`). `lakefile.lean` + `lake-manifest.json` +
`lean-toolchain` are authoritative for Mathlib/Lean versions and transitive
deps. Non-trivial proofs (multi-step derivations, helper lemmas, structures)
**must** live as real Lean files under `HybridVerify/<Section>/` so they
get the full `lake build` memory budget + incremental compilation + LSP
authoring; benchmark snippets `import HybridVerify.<Section>.<Module>` and
re-export the named lemma in 5–25 lines. Trivial library wrappers
(single-line `:= someLemma`) can stay inline in the JSON. To author a new
proof: edit `HybridVerify/<Section>/<Module>.lean` on host with VS Code +
Lean LSP (`loogle`/`leansearch%`/`apply?` are transitively available
via Mathlib's `LeanSearchClient`), `lake build` to validate, then update the
benchmark JSON to import + reference.

**Fast authoring iteration via persistent REPL daemon (`docker compose
service lean-repl`)**. The daemon (`tools/verify/lean_repl.py`) boots a
`lean-interact` server pointing at the repo root once per session, paying
the ~5-min Mathlib + BrownianMotion + HybridVerify olean-load cost a single
time. It then listens on TCP `127.0.0.1:7878` and processes each "check this
file" request in 5-30 sec — vs. 5-15 min for the `docker compose run --rm
verify` cold path. This is the LSP-equivalent for non-editor authoring
(Claude Code edits via the Edit tool, not VS Code).

Workflow:
```bash
# one-time per session: bring up the daemon, wait for "READY" in its logs
docker compose -f docker/docker-compose.yml up -d lean-repl
docker compose -f docker/docker-compose.yml logs -f lean-repl | grep -m1 READY

# per iteration: edit a .lean file, then check it via the wrapper
./scripts/lean-check.sh HybridVerify/Foundations/BrownianMartingale.lean
# Returns JSON: {"success": bool, "errors": [...], "warnings": [...], "sorry_count": N}

# tear down at end of session
docker compose -f docker/docker-compose.yml down lean-repl
```

`scripts/lean-check.sh` auto-detects whether the daemon is up (probes
`127.0.0.1:7878`); falls back to `lake env lean <file>` inside a fresh
`verify` container if not (slow but reliable, with live stdout — no
`| tail` buffering). Daemon's TCP port is bound to localhost only (no
external exposure).

Caveats:
- Daemon serializes requests through `LeanBackend._lock` (Lean isn't reentrant). Concurrent connections queue.
- Daemon does not write `.olean`s for downstream imports; once a proof works in the daemon, run a final `lake build` (or restart the daemon) before relying on the oleans for cross-file imports.
- If you bump Mathlib pin or the lakefile, restart the daemon to pick up new project state.

For multi-iteration sessions, prefer keeping
`Foundations/BrownianMartingale.lean`-class files small (one theorem + its
private helpers per file) so Lean only re-elaborates the changed file.

**Lean backend is lazily initialized**. `LeanBackend._ensure_server` defers
the expensive Mathlib bootstrap to the first `verify()` call. It holds a
`threading.Lock` since `lean-interact`'s server is not thread-safe — async
`verify()` calls serialize through the lock.

**SymPy backend dispatch** (`tools/verify/sympy_verifier.py`, legacy):
- SymPy is not used by default routing and should not appear as active `code.sympy` in benchmark JSON. Treat it as an explicit/manual backend only.
- If `theorem.metadata["sympy_check_kind"]` is set, dispatches to a typed handler (`ALGEBRAIC_IDENTITY` expects `lhs`/`rhs`; `MOMENT_COMPUTATION` expects `expected`/`computed`; `DERIVATIVE_CHECK` expects `expr`/`var`/`expected`; `INTEGRAL_CHECK` expects `integrand`/`var`/`limits`/`expected`; etc.).
- Otherwise the verifier evaluates the code and reads a `result` dict (must contain `"verified"`).
- **Convention**: if a benchmark's SymPy code already builds its own `result` dict, do NOT also set `sympy_check_kind` — the typed handlers will look for handler-specific variables (`lhs`/`rhs`/etc.) and fail. Pick one or the other.
- All evaluation uses Python's runtime evaluator with a controlled namespace; treat benchmark JSON as trusted input.

**Config** (`tools/verify/config.py`): TOML loader using stdlib `tomllib`
(Python 3.11+). Searches `hybrid_verify.toml` then `pyproject.toml`
(`[tool.hybrid-verify]`). Defaults are baked into the dataclasses, so a
missing file is fine.

**Models** (`tools/verify/models.py`): `TheoremStatement` is a frozen
dataclass — but `metadata` is a mutable dict by reference, which is how
`annotate_cross_validation` writes back results. `code` is keyed by
`Backend` enum (not strings); `from_dict` does the conversion at load time.

## Benchmark JSON shape

Either a top-level list of theorem dicts, or
`{"theorems": [...], "description": "..."}`. Each theorem requires `id`,
`name`, `domain` (must match a `Domain` enum value), and a `code` map with
active formal backend-name keys (`"lean"`). Optional: `description`,
`metadata`. Historical CAS snippets, if retained, belong under
`metadata.cas_reference.sympy`, never active `code.sympy`. Files are
organized by Saporito stochastic-processes textbook chapters.

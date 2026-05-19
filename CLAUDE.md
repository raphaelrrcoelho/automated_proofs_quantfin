# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

Preferred all-backends runner is Docker. The image is hosted on GHCR
(`ghcr.io/raphaelrrcoelho/quantfin-verify`, private). Pull-first, build-fallback:

```bash
# First time on a machine — log in to GHCR with your gh OAuth token:
TOKEN=$(grep -E '^[[:space:]]+oauth_token:' ~/.config/gh/hosts.yml | head -1 | awk '{print $2}')
echo "$TOKEN" | docker login ghcr.io -u raphaelrrcoelho --password-stdin
# (gh auth must include `read:packages` scope; refresh with
#  `gh auth refresh -h github.com -s read:packages` if needed.)

# Refresh the image to the latest published version (3-min pull vs 50-min build):
docker compose -f docker/docker-compose.yml pull verify

# Run a benchmark:
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/<file>.json -v --config hybrid_verify.toml --timeout 120

# Force a local rebuild (only when changing Dockerfile/Isabelle/Lean toolchain):
docker compose -f docker/docker-compose.yml build verify
# Then re-publish; see docker/docker-compose.yml header for the docker push commands.
```

The default compose command runs `benchmarks/cross_validated.json`:

```bash
docker compose -f docker/docker-compose.yml run --rm verify
```

Do NOT run `python -m python.cli ...` against the host toolchain. Always go through the
docker `verify` service so Mathlib/Lean/Isabelle versions are pinned and reproducible.

`-v` enables debug logging. `--parallel` verifies all theorems concurrently (otherwise sequential per-theorem; intra-theorem dispatch is governed by the router).

Install:

```bash
pip install -r requirements.txt                       # SymPy only (Lean/Isabelle skipped if missing)
pip install -e ".[all]"                               # adds lean-interact + isabelle-client
pip install -e ".[dev]"                               # pytest + pytest-asyncio
```

Fast regression checks (run inside the verify container so the Python /
pytest versions match the verifier — host invocations risk env drift and
should be avoided):

```bash
docker compose -f docker/docker-compose.yml run --rm \
    --entrypoint python3 verify -m pytest tests/test_router.py -q
docker compose -f docker/docker-compose.yml run --rm \
    --entrypoint python3 verify -m python.coverage_report
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
- Compose bind-mounts `python/`, `benchmarks/`, `tests/`, `hybrid_verify.toml`, and `lean/`. The `lean/` bind mount is RW so authoring `lean/HybridVerify/*.lean` on host (VS Code + Lean LSP) propagates without a rebuild; `.lake/` lives on the host and survives between runs. `Dockerfile.verify` runs `lake exe cache get && lake build` to bake a precompiled olean tree into the image at `/app/lean/.lake/`. To make the prebuilt cache survive the bind mount on a future image rebuild, add a named-volume shadow on `/app/lean/.lake/` to compose at that point. `lean-interact`'s own cache is in the `lean_interact_cache` Docker volume.
- The current verifier image prebuilds Isabelle `HOL-Probability`, not the local `HybridVerify` session. The Python Isabelle backend verifies temporary benchmark theories that import `HOL-Probability.Probability`; the local session is not required for CLI verification.
- If Docker build fails under Claude/Codex because it cannot write under `~/.docker`, rerun the same `docker compose ...` command with elevated permissions.

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

**Lean proofs live in `lean/HybridVerify/*.lean`, not in JSON strings**. The Lean backend always uses `lean-interact.LocalProject` pointing at the in-repo `lean/` Lake project (configured via `hybrid_verify.toml` `local_project = "lean"`). `lakefile.lean` + `lake-manifest.json` + `lean-toolchain` are authoritative for Mathlib/Lean versions and transitive deps. Non-trivial proofs (multi-step derivations, helper lemmas, structures) **must** live as real Lean files under `lean/HybridVerify/` so they get the full `lake build` memory budget + incremental compilation + LSP authoring; benchmark snippets `import HybridVerify.<Module>` and re-export the named lemma in 5–25 lines. Trivial library wrappers (single-line `:= someLemma`) can stay inline in the JSON. The earlier `TempRequireProject` mode was removed (commit 2026-05-09) — REPL elaboration could not handle the BM-martingale class of proofs without OOM. To author a new proof: edit `lean/HybridVerify/<Module>.lean` on host with VS Code + Lean LSP (`loogle`/`leansearch%`/`exact?`/`apply?` are transitively available via Mathlib's `LeanSearchClient`), `lake build` to validate, then update the benchmark JSON to import + reference. Existing migrated examples: `BrownianMartingale`, `MartingaleTransform`, `FTAP`, `CondExpJensen`, `ExpMin`.

**Fast authoring iteration via persistent REPL daemon (`docker compose service lean-repl`)**. The daemon (`python/lean_repl.py`) boots a `lean-interact` server pointing at `lean/` once per session, paying the ~5-min Mathlib + BrownianMotion + HybridVerify olean-load cost a single time. It then listens on TCP `127.0.0.1:7878` and processes each "check this file" request in 5-30 sec — vs. 5-15 min for the `docker compose run --rm verify` cold path. This is the LSP-equivalent for non-editor authoring (Claude Code edits via the Edit tool, not VS Code).

Workflow:
```bash
# one-time per session: bring up the daemon, wait for "READY" in its logs
docker compose -f docker/docker-compose.yml up -d lean-repl
docker compose -f docker/docker-compose.yml logs -f lean-repl | grep -m1 READY

# per iteration: edit a .lean file, then check it via the wrapper
./scripts/lean-check.sh lean/HybridVerify/BrownianMartingale.lean
# Returns JSON: {"success": bool, "errors": [...], "warnings": [...], "sorry_count": N}

# tear down at end of session
docker compose -f docker/docker-compose.yml down lean-repl
```

`scripts/lean-check.sh` auto-detects whether the daemon is up (probes `127.0.0.1:7878`); falls back to `lake env lean <file>` inside a fresh `verify` container if not (slow but reliable, with live stdout — no `| tail` buffering). Daemon's TCP port is bound to localhost only (no external exposure).

Caveats:
- Daemon serializes requests through `LeanBackend._lock` (Lean isn't reentrant). Concurrent connections queue.
- Daemon does not write `.olean`s for downstream imports; once a proof works in the daemon, run a final `lake build` (or restart the daemon) before relying on the oleans for cross-file imports.
- If you bump Mathlib pin or the lakefile, restart the daemon to pick up new project state.

For multi-iteration sessions, prefer keeping `BrownianMartingale.lean`-class files small (one theorem + its private helpers per file) so Lean only re-elaborates the changed file.

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

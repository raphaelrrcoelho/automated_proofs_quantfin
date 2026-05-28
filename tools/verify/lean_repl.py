"""Persistent Lean-interact REPL daemon.

Listens on TCP 7878 (inside the container; mapped to host by the
``lean-repl`` service in ``docker/docker-compose.yml``). Each connection
sends a single Lean code blob (typically a full ``.lean`` file's content);
the daemon elaborates it through the lean-interact server and returns a JSON
response with errors / warnings / sorry count.

The Lean server is initialized ONCE at daemon startup. The expensive bit
(loading Mathlib + BrownianMotion + QuantFin oleans, ~5 min on a cold
cache) is paid once per daemon lifetime; subsequent checks just elaborate
the new file against the loaded environment (~5-30 sec).

This converts the authoring loop from "edit → docker compose run --rm → wait
5-15 min → parse errors" to "edit → nc localhost 7878 → 5-30 sec → parse
errors", which is the LSP-equivalent for an LLM author who edits via a Tool
rather than via a graphical editor.

Usage from host:
    # one-time per session: start the daemon (waits ~5min for Mathlib load)
    docker compose -f docker/docker-compose.yml up -d lean-repl
    docker compose -f docker/docker-compose.yml logs -f lean-repl  # watch for READY

    # per iteration: send a file, read the JSON response
    cat QuantFin/Foo.lean | nc localhost 7878
    # or via the wrapper:
    ./scripts/lean-check.sh QuantFin/Foo.lean

    # tear down
    docker compose -f docker/docker-compose.yml down lean-repl

The daemon serializes requests through ``LeanBackend._lock`` since the
underlying Lean server is not thread-safe. Multiple concurrent connections
queue.
"""

from __future__ import annotations

import json
import logging
import socket
import sys

from .config import load_config
from .lean_backend import LeanBackend

HOST = "0.0.0.0"
PORT = 7878

logger = logging.getLogger(__name__)


def parse_response(response) -> dict:
    """Extract errors / sorry-count from a lean-interact response."""
    messages = getattr(response, "messages", []) or []
    error_msgs = [m for m in messages if getattr(m, "severity", None) == "error"]
    warning_msgs = [m for m in messages if getattr(m, "severity", None) == "warning"]
    legacy_errors = getattr(response, "errors", None)
    if not error_msgs and legacy_errors:
        error_msgs = legacy_errors

    sorries = getattr(response, "sorries", [])
    sorry_count = len(sorries) if isinstance(sorries, list) else 0

    def fmt(m) -> str:
        data = getattr(m, "data", None)
        pos = getattr(m, "start_pos", None)
        if data is not None:
            if pos is not None:
                line = getattr(pos, "line", "?")
                col = getattr(pos, "column", "?")
                return f"line {line}:{col}: {data}"
            return str(data)
        return str(m)

    return {
        "success": not error_msgs and sorry_count == 0,
        "errors": [fmt(m) for m in error_msgs],
        "warnings": [fmt(m) for m in warning_msgs],
        "sorry_count": sorry_count,
    }


def handle(conn: socket.socket, backend: LeanBackend, addr) -> None:
    """Handle one connection: read code, run, return JSON result."""
    try:
        chunks: list[bytes] = []
        while True:
            data = conn.recv(65536)
            if not data:
                break
            chunks.append(data)
        code = b"".join(chunks).decode("utf-8")
        if not code.strip():
            conn.sendall(b'{"success": false, "errors": ["empty input"]}\n')
            return
        logger.info("check from %s: %d bytes", addr, len(code))

        from lean_interact import Command

        with backend._lock:
            response = backend._server.run(Command(cmd=code))
        result = parse_response(response)
        logger.info(
            "result: success=%s errors=%d warnings=%d sorries=%d",
            result["success"],
            len(result["errors"]),
            len(result["warnings"]),
            result["sorry_count"],
        )
        conn.sendall((json.dumps(result, indent=2) + "\n").encode("utf-8"))
    except Exception as e:
        logger.exception("daemon error")
        err = {"success": False, "errors": [f"daemon error: {e!r}"]}
        try:
            conn.sendall((json.dumps(err) + "\n").encode("utf-8"))
        except Exception:
            pass
    finally:
        try:
            conn.close()
        except Exception:
            pass


def main() -> int:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(name)s %(levelname)s %(message)s",
    )

    config = load_config("quantfin.toml")

    # Daemon-tuned memory + thread settings (long-lived session, heavier
    # workload than ad-hoc verify pathway). See `LeanBackend.__init__`
    # docstring for the semantics. Rationale:
    #   - hard_cap=None: RLIMIT_AS is omitted. Set 8000 MB initially, but
    #     it interacts badly with Lean's olean mmap + multi-thread stack
    #     allocation (RLIMIT_AS=8000 + LEAN_NUM_THREADS=4 → "failed to
    #     create thread" on first ItoIntegralL2 import). The container's
    #     cgroup memory limit (11.68 GB on the host) is the real backstop.
    #   - soft_total=0.90: only restart on system-wide pressure if we cross
    #     90% (instead of the conservative default 0.80). Avoids spurious
    #     mid-session restarts from buffer-cache fluctuations.
    #   - soft_proc=None: disable in-session auto-restart based on Lean
    #     process memory. We'd rather see an OOM (cgroup kill, observable)
    #     than lose mid-session state silently.
    backend = LeanBackend(
        local_project=config.lean.local_project,
        memory_hard_limit_mb=None,
        max_total_memory=0.90,
        max_process_memory=None,
    )

    print("Initializing Lean server (Mathlib + QuantFin load, ~3-5 min cold "
          "with persistent .lake volume; ~10-15 min cold on first ever start)...",
          flush=True)
    backend._ensure_server()
    print(f"READY: listening on {HOST}:{PORT}", flush=True)

    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    sock.bind((HOST, PORT))
    sock.listen(4)

    try:
        while True:
            conn, addr = sock.accept()
            handle(conn, backend, addr)
    except KeyboardInterrupt:
        print("Shutting down...", flush=True)
    finally:
        sock.close()
        backend.shutdown()
    return 0


if __name__ == "__main__":
    sys.exit(main())

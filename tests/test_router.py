import json
from pathlib import Path

from tools.verify.models import Backend, Domain
from tools.verify.router import Router


ALLOWED_FORMALIZATION_STATUSES = {
    "full",
    "library_wrapper",
    "reduced_core",
    "placeholder",
}

PLACEHOLDER_PATTERNS = (
    "example : true := trivial",
    "∀ (b :",
    "∀ (x :",
    "(0 : ℝ) = 0",
    "formal placeholder",
)

EXPECTED_FULL_THEOREMS = {
    "bm-def-5.1.1",
    "cv-poisson-def",
    "mc-def-1.1.1",
    "mc-prop-1.2.3",
    "mc-prop-1.4.13",
    "pp-thm-3.3.5",
}

EXPECTED_NON_PLACEHOLDER_THEOREMS = {
    "bm-cor-5.3.4",
}


def _iter_theorems():
    for path in Path("benchmarks").glob("*.json"):
        data = json.loads(path.read_text())
        theorems = data.get("theorems", data)
        for theorem in theorems:
            yield path, theorem


def test_default_routes_do_not_use_sympy() -> None:
    router = Router()

    for domain in Domain:
        decision = router.route(domain)
        assert Backend.SYMPY not in decision.backends


def test_benchmarks_do_not_expose_sympy_as_active_code() -> None:
    for path, theorem in _iter_theorems():
        assert "sympy" not in theorem.get("code", {}), (
            path,
            theorem["id"],
        )


def test_benchmarks_do_not_contain_sorry_or_admit() -> None:
    for path, theorem in _iter_theorems():
        for backend, code in theorem.get("code", {}).items():
            lowered = code.lower()
            assert "sorry" not in lowered, (path, theorem["id"], backend)
            assert "admit" not in lowered, (path, theorem["id"], backend)


def test_benchmarks_declare_formalization_status() -> None:
    for path, theorem in _iter_theorems():
        status = theorem.get("metadata", {}).get("formalization_status")
        assert status in ALLOWED_FORMALIZATION_STATUSES, (
            path,
            theorem["id"],
            status,
        )


def test_full_statuses_do_not_use_obvious_placeholders() -> None:
    for path, theorem in _iter_theorems():
        status = theorem.get("metadata", {}).get("formalization_status")
        code = "\n".join(theorem.get("code", {}).values())
        lowered = code.lower()
        has_placeholder = any(pattern.lower() in lowered for pattern in PLACEHOLDER_PATTERNS)

        if has_placeholder:
            assert status == "placeholder", (path, theorem["id"], status)
        if status in {"full", "library_wrapper"}:
            assert not has_placeholder, (path, theorem["id"], status)


def test_expected_promotions_are_full_theorems() -> None:
    statuses = {
        theorem["id"]: theorem.get("metadata", {}).get("formalization_status")
        for _, theorem in _iter_theorems()
    }

    for theorem_id in EXPECTED_FULL_THEOREMS:
        assert statuses.get(theorem_id) == "full", (
            theorem_id,
            statuses.get(theorem_id),
        )


def test_expected_placeholder_removals_are_not_placeholders() -> None:
    statuses = {
        theorem["id"]: theorem.get("metadata", {}).get("formalization_status")
        for _, theorem in _iter_theorems()
    }

    for theorem_id in EXPECTED_NON_PLACEHOLDER_THEOREMS:
        assert statuses.get(theorem_id) != "placeholder", (
            theorem_id,
            statuses.get(theorem_id),
        )

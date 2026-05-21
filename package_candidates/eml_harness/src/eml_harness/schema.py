from __future__ import annotations

REQUIRED_KEYS = {"record_id", "status"}
ALLOWED_STATUS = {"PASS", "FAIL", "SKIP"}


def validate_result(result: dict[str, object]) -> list[str]:
    errors: list[str] = []
    missing = sorted(REQUIRED_KEYS - set(result))
    if missing:
        errors.append(f"missing required keys: {', '.join(missing)}")
    status = result.get("status")
    if status is not None and status not in ALLOWED_STATUS:
        errors.append(f"invalid status: {status}")
    return errors

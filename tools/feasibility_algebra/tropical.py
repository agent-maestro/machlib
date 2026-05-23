from __future__ import annotations


def tropical_add(left: float, right: float) -> float:
    return min(left, right)


def tropical_multiply(left: float, right: float) -> float:
    return left + right


def choose_min_plus(paths: list[tuple[str, float]]) -> tuple[str, float]:
    if not paths:
        raise ValueError("paths must not be empty")
    return min(paths, key=lambda item: item[1])

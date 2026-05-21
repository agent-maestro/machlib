from __future__ import annotations

from collections import Counter


def increments(values: list[float]) -> list[float]:
    return [right - left for left, right in zip(values, values[1:])]


def transitions(states: list[str]) -> list[tuple[str, str]]:
    return list(zip(states, states[1:]))


def transition_counts(states: list[str]) -> dict[str, int]:
    counts = Counter(f"{left}->{right}" for left, right in transitions(states))
    return dict(sorted(counts.items()))

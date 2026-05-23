from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class ResourceProfile:
    profile_id: str
    name: str
    operation_budget: float
    memory_budget_bytes: float
    time_budget_seconds: float
    energy_budget_optional: float | None
    notes: str

    def to_dict(self) -> dict[str, object]:
        return {
            "profile_id": self.profile_id,
            "name": self.name,
            "operation_budget": self.operation_budget,
            "memory_budget_bytes": self.memory_budget_bytes,
            "time_budget_seconds": self.time_budget_seconds,
            "energy_budget_optional": self.energy_budget_optional,
            "notes": self.notes,
        }


def default_resource_profiles() -> list[ResourceProfile]:
    return [
        ResourceProfile("laptop_small", "Small laptop", 1e9, 8 * 2**30, 10, None, "Interactive local budget."),
        ResourceProfile("workstation", "Workstation", 1e12, 64 * 2**30, 600, None, "Single strong workstation."),
        ResourceProfile("gpu_box", "GPU box", 1e15, 80 * 2**30, 3600, None, "Accelerated but finite local machine."),
        ResourceProfile("cluster_small", "Small cluster", 1e18, 2 * 2**40, 86400, None, "Internal cluster-scale budget."),
        ResourceProfile("hypothetical_large_cluster", "Hypothetical large cluster", 1e24, 1024 * 2**40, 604800, None, "Huge planning budget, not a guarantee."),
        ResourceProfile("silicon_toy_budget", "Silicon toy budget", 1e6, 256 * 1024, 0.02, None, "Trace0-scale toy hardware estimate."),
        ResourceProfile("browser_interactive_budget", "Browser interactive budget", 1e7, 256 * 2**20, 0.1, None, "Smooth public UI budget."),
        ResourceProfile("capcard_review_budget", "CapCard review budget", 1e8, 1 * 2**30, 30, None, "Internal human review packet budget."),
    ]

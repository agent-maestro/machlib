"""Local CapCard Lab engine.

The package is intentionally standard-library only and local-only. It builds
internal draft evidence cards, mutation fixtures, trust scores, and static
HTML previews without touching production marketplace surfaces.
"""

from .schema import FALSE_ACTION_FIELDS, REQUIRED_CANDIDATES

__all__ = ["FALSE_ACTION_FIELDS", "REQUIRED_CANDIDATES"]

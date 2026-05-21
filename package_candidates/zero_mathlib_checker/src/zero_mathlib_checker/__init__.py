"""Pre-alpha zero-Mathlib dependency-boundary checker."""

from .scanner import ScanResult, scan_path, scan_root

__all__ = ["ScanResult", "scan_path", "scan_root"]

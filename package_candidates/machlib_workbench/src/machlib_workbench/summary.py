from __future__ import annotations

from dataclasses import asdict, dataclass
from pathlib import Path


@dataclass(frozen=True)
class WorkbenchSummary:
    root: str
    file_count: int
    markdown_count: int
    json_count: int
    other_count: int

    def to_dict(self) -> dict[str, int | str]:
        return asdict(self)


def summarize_path(root: str | Path) -> WorkbenchSummary:
    path = Path(root)
    if not path.exists():
        raise FileNotFoundError(str(path))

    files = [entry for entry in path.rglob("*") if entry.is_file()]
    markdown_count = sum(1 for entry in files if entry.suffix.lower() == ".md")
    json_count = sum(1 for entry in files if entry.suffix.lower() == ".json")
    return WorkbenchSummary(
        root=str(path),
        file_count=len(files),
        markdown_count=markdown_count,
        json_count=json_count,
        other_count=len(files) - markdown_count - json_count,
    )

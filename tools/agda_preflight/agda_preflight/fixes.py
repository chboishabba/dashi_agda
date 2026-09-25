from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Tuple


@dataclass(frozen=True)
class TextEdit:
    path: Path
    start_line: int
    start_column: int
    end_line: int
    end_column: int
    replacement: str
    start_byte: int | None = None
    end_byte: int | None = None

    def as_dict(self) -> dict:
        return {
            "path": str(self.path),
            "start_line": self.start_line,
            "start_column": self.start_column,
            "end_line": self.end_line,
            "end_column": self.end_column,
            "replacement": self.replacement,
            "start_byte": self.start_byte,
            "end_byte": self.end_byte,
        }


@dataclass(frozen=True)
class SuggestedFix:
    title: str
    applicability: str
    rationale: str
    validation: str
    edits: Tuple[TextEdit, ...] = field(default_factory=tuple)

    def as_dict(self) -> dict:
        return {
            "title": self.title,
            "applicability": self.applicability,
            "rationale": self.rationale,
            "validation": self.validation,
            "edits": [edit.as_dict() for edit in self.edits],
        }

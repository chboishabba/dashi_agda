from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Protocol, runtime_checkable

from .model import SemanticGraph


@runtime_checkable
class LanguageAdapter(Protocol):
    """Language-specific source -> semantic graph frontend."""

    name: str
    suffixes: tuple[str, ...]

    def extract_file(self, path: str, source: bytes) -> Any:
        ...

    def build_graph(self, files: list[Any]) -> SemanticGraph:
        ...


@dataclass(frozen=True)
class AdapterSpec:
    name: str
    suffixes: tuple[str, ...]

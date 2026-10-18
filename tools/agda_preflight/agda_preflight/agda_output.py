from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
from typing import Iterable, List


_HEADER = re.compile(
    r"^(?P<path>.+?):(?P<line>\d+)\.(?P<column>\d+)"
    r"(?:-(?:(?P<end_line>\d+)\.)?(?P<end_column>\d+))?"
    r": (?P<severity>warning|error): (?P<tag>.*)$"
)
_WARNING_TAG = re.compile(r"^-W\[no\](?P<name>[A-Za-z0-9_'-]+)$")
_ERROR_TAG = re.compile(r"^\[(?P<name>[^\]]+)\]$")
_PROGRESS = re.compile(r"^\(\s*\d+/\d+\) Checking ")

_WARNING_CODES = {
    "PatternShadowsConstructor": "TSAGDA300",
    "RewritesNothing": "TSAGDA301",
    "UserWarning": "TSAGDA302",
}
_ERROR_CODES = {
    "ParseError": "TSAGDA390",
}


@dataclass(frozen=True)
class NativeAgdaDiagnostic:
    code: str
    message: str
    path: Path
    line: int
    column: int
    severity: str
    agda_class: str


def _class_and_code(severity: str, tag: str) -> tuple[str, str]:
    if severity == "warning":
        match = _WARNING_TAG.match(tag.strip())
        agda_class = match.group("name") if match else (tag.strip() or "Warning")
        return agda_class, _WARNING_CODES.get(agda_class, "TSAGDA399")

    match = _ERROR_TAG.match(tag.strip())
    agda_class = match.group("name") if match else (tag.strip() or "Error")
    return agda_class, _ERROR_CODES.get(agda_class, "TSAGDA398")


def _is_progress_or_wrapper(line: str) -> bool:
    stripped = line.strip()
    return (
        bool(_PROGRESS.match(stripped))
        or stripped.startswith("Checking: ")
        or stripped.startswith("Checking ")
        or stripped.startswith("Agda failed for:")
        or stripped.startswith("Logging Agda output to:")
        or stripped.startswith("Agda RSS guard:")
    )


def _message(lines: Iterable[str]) -> str:
    cleaned = [line.strip() for line in lines if line.strip()]
    return "\n".join(cleaned)


def parse_agda_diagnostics(output: str) -> List[NativeAgdaDiagnostic]:
    """Parse native Agda warnings/errors out of mixed compiler/progress output.

    Agda diagnostics begin with a source location header and may have multiline
    bodies. Parallel-check progress and wrapper status lines delimit, but are
    never absorbed into, the diagnostic message.
    """

    result: List[NativeAgdaDiagnostic] = []
    current = None
    body: List[str] = []

    def flush() -> None:
        nonlocal current, body
        if current is None:
            return
        agda_class, code = _class_and_code(current["severity"], current["tag"])
        message = _message(body)
        if not message:
            message = current["tag"].strip() or agda_class
        result.append(
            NativeAgdaDiagnostic(
                code=code,
                message=message,
                path=Path(current["path"]),
                line=int(current["line"]),
                column=int(current["column"]),
                severity=current["severity"],
                agda_class=agda_class,
            )
        )
        current = None
        body = []

    for raw_line in output.splitlines():
        header = _HEADER.match(raw_line.strip())
        if header:
            flush()
            current = header.groupdict()
            continue

        if current is None:
            continue

        if _is_progress_or_wrapper(raw_line):
            flush()
            continue

        body.append(raw_line)

    flush()
    return result

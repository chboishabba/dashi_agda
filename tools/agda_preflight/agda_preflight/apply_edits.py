from __future__ import annotations

from collections import defaultdict
import os
from pathlib import Path
import tempfile
from typing import Iterable, List

from .fixes import TextEdit


class EditApplicationError(RuntimeError):
    pass


def _validate_non_overlapping(edits: List[TextEdit], byte_length: int) -> None:
    ordered = sorted(edits, key=lambda edit: (edit.start_byte, edit.end_byte))
    previous_end = -1
    for edit in ordered:
        if edit.start_byte is None or edit.end_byte is None:
            raise EditApplicationError(
                "suggested edit has no exact byte span and cannot be machine-applied"
            )
        if not (0 <= edit.start_byte <= edit.end_byte <= byte_length):
            raise EditApplicationError("suggested edit byte span is outside the file")
        if edit.start_byte < previous_end:
            raise EditApplicationError("suggested edits overlap")
        previous_end = edit.end_byte


def apply_text_edits(edits: Iterable[TextEdit]) -> List[Path]:
    grouped = defaultdict(list)
    for edit in edits:
        grouped[edit.path.resolve()].append(edit)

    changed = []
    for path, path_edits in grouped.items():
        source = path.read_bytes()
        _validate_non_overlapping(path_edits, len(source))

        updated = source
        for edit in sorted(
            path_edits,
            key=lambda item: item.start_byte if item.start_byte is not None else -1,
            reverse=True,
        ):
            assert edit.start_byte is not None
            assert edit.end_byte is not None
            replacement = edit.replacement.encode("utf-8")
            updated = (
                updated[: edit.start_byte]
                + replacement
                + updated[edit.end_byte :]
            )

        if updated == source:
            continue

        mode = path.stat().st_mode
        with tempfile.NamedTemporaryFile(
            dir=path.parent,
            prefix=f".{path.name}.dashi-",
            delete=False,
        ) as handle:
            temporary = Path(handle.name)
            handle.write(updated)
            handle.flush()
            os.fsync(handle.fileno())
        try:
            os.chmod(temporary, mode)
            os.replace(temporary, path)
        finally:
            if temporary.exists():
                temporary.unlink()
        changed.append(path)

    return sorted(changed)

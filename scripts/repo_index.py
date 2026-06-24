#!/usr/bin/env python3
"""Build and query a conservative repo-local Agda/Markdown symbol index.

This first pass is deliberately static and read-only:

- Agda source is the authority.
- Markdown contributes doc mentions and doc links.
- The index is versioned JSON.
- Queries work from the index file and fall back to source scanning only when
  the index is missing.

The parser is intentionally conservative. It prefers stable, mechanically
discoverable facts over inference.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterable


SCHEMA_VERSION = "1.0.0"
DEFAULT_INDEX_PATH = Path(".repo-index/index.json")
LANG_AGDA = "agda"
LANG_MD = "md"
KNOWN_STATUS_VALUES = {
    "promoted",
    "candidate-only",
    "blocked",
    "external-authority-required",
    "false-promotion",
    "deprecated",
    "unknown",
}


MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z][A-Za-z0-9'.]*)\s+where\b")
AGDA_IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z][A-Za-z0-9'.]*)")
AGDA_DECL_RE = re.compile(r"^(data|record|postulate)\s+([A-Za-z][A-Za-z0-9']*)\b")
AGDA_SIGNATURE_RE = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*:")
AGDA_ASSIGN_RE = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*=")
IDENT_RE = re.compile(r"[A-Za-z][A-Za-z0-9']*(?:\.[A-Za-z][A-Za-z0-9']*)*")
MARKDOWN_LINK_RE = re.compile(r"\[[^\]]+\]\(([^)]+)\)")
COMMENT_RE = re.compile(r"^\s*--(.*)$")
SECTION_DIVIDER_RE = re.compile(r"^\s*-{8,}\s*$")


@dataclass(slots=True)
class SymbolRecord:
    symbol_id: str
    name: str
    kind: str
    language: str
    module: str | None
    file: str
    line_start: int
    line_end: int
    signature: str
    snippet: str
    doc: str
    status: dict[str, str]
    tags: list[str] = field(default_factory=list)
    requirements: dict[str, list[dict[str, str]]] = field(default_factory=dict)


@dataclass(slots=True)
class FileRecord:
    path: str
    language: str
    module: str | None
    imports: list[str] = field(default_factory=list)
    doc_links: list[str] = field(default_factory=list)
    symbols: list[str] = field(default_factory=list)


@dataclass(slots=True)
class RefRecord:
    from_symbol: str
    to_symbol: str
    ref_kind: str
    file: str
    line: int
    snippet: str


@dataclass(slots=True)
class RepoIndex:
    schema_version: str
    root: str
    generated_at: str
    files: list[FileRecord]
    symbols: list[SymbolRecord]
    references: list[RefRecord]

    def to_json(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "root": self.root,
            "generated_at": self.generated_at,
            "files": [asdict(item) for item in self.files],
            "symbols": [asdict(item) for item in self.symbols],
            "references": [asdict(item) for item in self.references],
        }

    @classmethod
    def from_json(cls, payload: dict[str, Any]) -> "RepoIndex":
        return cls(
            schema_version=payload.get("schema_version", SCHEMA_VERSION),
            root=payload.get("root", "."),
            generated_at=payload.get("generated_at", ""),
            files=[FileRecord(**item) for item in payload.get("files", [])],
            symbols=[SymbolRecord(**item) for item in payload.get("symbols", [])],
            references=[RefRecord(**item) for item in payload.get("references", [])],
        )


def _relpath(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def _read_text(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return None


def _stable_unique(items: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def _normalize_kind(kind: str) -> str:
    return kind.lower().strip()


def _status_from_text(text: str) -> dict[str, str]:
    lowered = text.lower()
    promotion = "unknown"
    authority = "unknown"
    truth = "unknown"

    if any(marker in lowered for marker in ("candidate-only", "candidateonly", "candidate only", "checkedcandidateonly")):
        promotion = "candidate-only"
    if "promotedistrue" in lowered or "promoted ≡ true" in lowered or "promoted true" in lowered:
        promotion = "promoted"
    if "promotionimpossible" in lowered or "blocked" in lowered or "fail-closed" in lowered:
        promotion = "blocked"
    if "external-authority-required" in lowered:
        authority = "external-authority-required"
    if any(
        marker in lowered
        for marker in (
            "noruntimeauthorityisfalse",
            "no-runtime-authority",
            "runtimeauthorityisfalse",
            "runtime authority is false",
        )
    ):
        authority = "no-runtime-authority"
    if any(
        marker in lowered
        for marker in (
            "notruthpromotion",
            "no-truth-promotion",
            "carrystruthisfalse",
            "truthisfalse",
        )
    ):
        truth = "no-truth-promotion"
    if "truthpromotion" in lowered or "carrystruthistrue" in lowered or "truth is true" in lowered:
        truth = "truth-promotion"

    return {
        "promotion": promotion if promotion in KNOWN_STATUS_VALUES else "unknown",
        "authority": authority if authority in KNOWN_STATUS_VALUES else "unknown",
        "truth": truth if truth in KNOWN_STATUS_VALUES else "unknown",
        "source": "agda",
    }


def _snippet_from_lines(lines: list[str], start: int, end: int, limit: int = 220) -> str:
    compact = " ".join(line.strip() for line in lines[start:end] if line.strip())
    compact = re.sub(r"\s+", " ", compact).strip()
    if len(compact) <= limit:
        return compact
    return compact[: limit - 1] + "…"


def _collect_doc_block(lines: list[str], start_index: int) -> str:
    collected: list[str] = []
    idx = start_index - 1
    while idx >= 0:
        line = lines[idx]
        if not line.strip():
            if collected:
                break
            idx -= 1
            continue
        if SECTION_DIVIDER_RE.match(line):
            idx -= 1
            continue
        match = COMMENT_RE.match(line)
        if match:
            text = match.group(1).strip()
            if text:
                collected.append(text)
            idx -= 1
            continue
        break

    collected.reverse()
    meaningful = [item for item in collected if item and not SECTION_DIVIDER_RE.match(item)]
    return " ".join(meaningful).strip()


def _candidate_names(token: str) -> list[str]:
    parts = token.split(".")
    out = [token]
    if parts:
        out.append(parts[-1])
    return _stable_unique(out)


def _best_owner_symbol(symbols: list[SymbolRecord], file_path: str, line_no: int) -> str | None:
    containing = [
        item
        for item in symbols
        if item.file == file_path and item.line_start <= line_no <= item.line_end
    ]
    if not containing:
        return None
    containing.sort(key=lambda item: (item.line_end - item.line_start, item.line_start))
    return containing[0].symbol_id


def _match_lookup_keys(
    token: str,
    by_symbol_id: dict[str, list[str]],
    by_module: dict[str, list[str]],
    by_name: dict[str, list[str]],
) -> list[str]:
    matches: list[str] = []
    if token in by_symbol_id:
        matches.extend(by_symbol_id[token])
    if token in by_module:
        matches.extend(by_module[token])
    for candidate in _candidate_names(token):
        if candidate in by_name:
            matches.extend(by_name[candidate])
    return _stable_unique(matches)


def _iter_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        rel = path.relative_to(root)
        parts = rel.parts
        if any(part in {".git", ".repo-index", "node_modules", ".venv", "__pycache__"} for part in parts):
            continue
        if path.suffix == ".agda" or path.suffix == ".md":
            files.append(path)
    return sorted(files)


def _parse_agda_file(path: Path, root: Path) -> tuple[FileRecord, list[SymbolRecord]]:
    text = _read_text(path)
    if text is None:
        return FileRecord(path=_relpath(path, root), language=LANG_AGDA, module=None), []

    lines = text.splitlines()
    module_name: str | None = None
    imports: list[str] = []
    symbols: list[SymbolRecord] = []

    module_line_no = 1
    for idx, line in enumerate(lines):
        module_match = MODULE_RE.match(line)
        if module_match:
            module_name = module_match.group(1)
            module_line_no = idx + 1
            break

    if module_name:
        doc = _collect_doc_block(lines, module_line_no - 1)
        signature = f"module {module_name} where"
        symbols.append(
            SymbolRecord(
                symbol_id=module_name,
                name=module_name.split(".")[-1],
                kind="module",
                language=LANG_AGDA,
                module=module_name,
                file=_relpath(path, root),
                line_start=module_line_no,
                line_end=module_line_no,
                signature=signature,
                snippet=signature,
                doc=doc,
                status={"promotion": "unknown", "authority": "unknown", "truth": "unknown", "source": "agda"},
                tags=["module"],
                requirements={},
            )
        )

    for idx, line in enumerate(lines):
        import_match = AGDA_IMPORT_RE.match(line)
        if import_match:
            imports.append(import_match.group(1))

    top_level_starts: list[int] = []
    for idx, line in enumerate(lines):
        stripped = line.strip()
        if not stripped or stripped.startswith("--") or SECTION_DIVIDER_RE.match(line):
            continue
        if line[: len(line) - len(line.lstrip())]:
            continue
        if MODULE_RE.match(line) or AGDA_DECL_RE.match(line) or AGDA_SIGNATURE_RE.match(line) or AGDA_ASSIGN_RE.match(line):
            top_level_starts.append(idx)

    top_level_starts = _stable_unique(top_level_starts)
    top_level_starts.append(len(lines))

    for pos, start in enumerate(top_level_starts[:-1]):
        end = top_level_starts[pos + 1]
        line = lines[start]
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue

        name: str | None = None
        kind = "value"
        signature = stripped

        decl_match = AGDA_DECL_RE.match(stripped)
        if decl_match:
            kind = decl_match.group(1).lower()
            name = decl_match.group(2)
        else:
            sig_match = AGDA_SIGNATURE_RE.match(stripped)
            assign_match = AGDA_ASSIGN_RE.match(stripped)
            if sig_match:
                name = sig_match.group(1)
                kind = "function"
            elif assign_match:
                name = assign_match.group(1)
                kind = "value"

        if not name:
            continue

        block_text = "\n".join(lines[start:end])
        doc = _collect_doc_block(lines, start)
        snippet = _snippet_from_lines(lines, start, min(end, start + 4))
        status = _status_from_text(f"{name}\n{signature}\n{doc}\n{block_text}")
        symbol_id = f"{module_name}.{name}" if module_name else name
        requirements = {
            "syntactic_requirements": [
                {"kind": "import", "symbol": item, "source": "parsed-import"} for item in imports
            ],
        }
        symbols.append(
            SymbolRecord(
                symbol_id=symbol_id,
                name=name,
                kind=_normalize_kind(kind),
                language=LANG_AGDA,
                module=module_name,
                file=_relpath(path, root),
                line_start=start + 1,
                line_end=end,
                signature=signature,
                snippet=snippet,
                doc=doc,
                status=status,
                tags=[module_name.split(".")[0]] if module_name else [],
                requirements=requirements,
            )
        )

        # Conservative field/constructor capture for record/data blocks.
        if kind == "record":
            field_lines = []
            for inner_idx in range(start + 1, end):
                inner = lines[inner_idx]
                inner_stripped = inner.strip()
                if not inner_stripped:
                    continue
                if inner.lstrip().startswith("field"):
                    continue
                field_match = re.match(r"^\s+([A-Za-z][A-Za-z0-9']*)\s*:", inner)
                if field_match:
                    field_lines.append((inner_idx, field_match.group(1), "field"))
            for inner_idx, field_name, field_kind in field_lines:
                field_signature = lines[inner_idx].strip()
                symbols.append(
                    SymbolRecord(
                        symbol_id=f"{symbol_id}.{field_name}",
                        name=field_name,
                        kind=field_kind,
                        language=LANG_AGDA,
                        module=module_name,
                        file=_relpath(path, root),
                        line_start=inner_idx + 1,
                        line_end=inner_idx + 1,
                        signature=field_signature,
                        snippet=field_signature,
                        doc="",
                        status=_status_from_text(f"{field_name}\n{field_signature}\n{block_text}"),
                        tags=["record-field"],
                        requirements={
                            "syntactic_requirements": [
                                {"kind": "record", "symbol": symbol_id, "source": "local-record-field"}
                            ]
                        },
                    )
                )

        if kind == "data":
            for inner_idx in range(start + 1, end):
                inner = lines[inner_idx]
                inner_match = re.match(r"^\s+([A-Za-z][A-Za-z0-9']*)\b", inner)
                if not inner_match:
                    continue
                constructor = inner_match.group(1)
                if constructor in {"data", "record", "field", "where"}:
                    continue
                if not inner.lstrip().startswith(constructor):
                    continue
                symbols.append(
                    SymbolRecord(
                        symbol_id=f"{symbol_id}.{constructor}",
                        name=constructor,
                        kind="constructor",
                        language=LANG_AGDA,
                        module=module_name,
                        file=_relpath(path, root),
                        line_start=inner_idx + 1,
                        line_end=inner_idx + 1,
                        signature=inner.strip(),
                        snippet=inner.strip(),
                        doc="",
                        status=_status_from_text(f"{constructor}\n{inner.strip()}\n{block_text}"),
                        tags=["constructor"],
                        requirements={
                            "syntactic_requirements": [
                                {"kind": "data", "symbol": symbol_id, "source": "local-data-constructor"}
                            ]
                        },
                    )
                )

    file_record = FileRecord(
        path=_relpath(path, root),
        language=LANG_AGDA,
        module=module_name,
        imports=_stable_unique(imports),
        doc_links=[],
        symbols=[symbol.symbol_id for symbol in symbols],
    )
    return file_record, symbols


def _parse_markdown_file(path: Path, root: Path) -> tuple[FileRecord, list[SymbolRecord]]:
    text = _read_text(path)
    if text is None:
        return FileRecord(path=_relpath(path, root), language=LANG_MD, module=None), []

    lines = text.splitlines()
    doc_links = _stable_unique(MARKDOWN_LINK_RE.findall(text))
    title = path.stem
    symbols: list[SymbolRecord] = []
    file_record = FileRecord(
        path=_relpath(path, root),
        language=LANG_MD,
        module=None,
        imports=[],
        doc_links=doc_links,
        symbols=[],
    )

    # Surface the document itself as a symbol-like node for doc-mentions and graph queries.
    symbols.append(
        SymbolRecord(
            symbol_id=f"docs:{_relpath(path, root)}",
            name=title,
            kind="document",
            language=LANG_MD,
            module=None,
            file=_relpath(path, root),
            line_start=1,
            line_end=max(1, len(lines)),
            signature=title,
            snippet=_snippet_from_lines(lines, 0, min(len(lines), 3)),
            doc="",
            status={"promotion": "unknown", "authority": "unknown", "truth": "unknown", "source": "docs"},
            tags=["doc"],
            requirements={},
        )
    )
    file_record.symbols = [symbols[0].symbol_id]
    return file_record, symbols


def _build_lookup(symbols: list[SymbolRecord]) -> tuple[dict[str, list[str]], dict[str, list[str]], dict[str, list[str]]]:
    by_symbol_id: dict[str, list[str]] = defaultdict(list)
    by_module: dict[str, list[str]] = defaultdict(list)
    by_name: dict[str, list[str]] = defaultdict(list)
    for symbol in symbols:
        by_symbol_id[symbol.symbol_id].append(symbol.symbol_id)
        if symbol.module:
            by_module[symbol.module].append(symbol.symbol_id)
        by_name[symbol.name].append(symbol.symbol_id)
    return by_symbol_id, by_module, by_name


def _build_references(root: Path, files: list[FileRecord], symbols: list[SymbolRecord]) -> list[RefRecord]:
    by_symbol_id, by_module, by_name = _build_lookup(symbols)
    symbol_index = {symbol.symbol_id: symbol for symbol in symbols}
    refs: list[RefRecord] = []
    seen: set[tuple[str, str, str, str, int]] = set()

    for file_record in files:
        path = root / file_record.path
        text = _read_text(path)
        if text is None:
            continue
        lines = text.splitlines()

        if file_record.language == LANG_AGDA:
            for line_no, line in enumerate(lines, start=1):
                stripped = line.strip()
                if not stripped or stripped.startswith("--"):
                    continue

                owner = _best_owner_symbol(symbols, file_record.path, line_no)
                for token in IDENT_RE.findall(line):
                    for target in _match_lookup_keys(token, by_symbol_id, by_module, by_name):
                        if owner and target == owner:
                            continue
                        key = (owner or file_record.path, target, "definition-use", file_record.path, line_no)
                        if key in seen:
                            continue
                        seen.add(key)
                        refs.append(
                            RefRecord(
                                from_symbol=owner or file_record.path,
                                to_symbol=target,
                                ref_kind="definition-use",
                                file=file_record.path,
                                line=line_no,
                                snippet=line.strip(),
                            )
                        )

            if file_record.module:
                owner = file_record.module
                for line_no, line in enumerate(lines, start=1):
                    match = AGDA_IMPORT_RE.match(line)
                    if not match:
                        continue
                    target = match.group(1)
                    key = (owner, target, "import-use", file_record.path, line_no)
                    if key in seen:
                        continue
                    seen.add(key)
                    refs.append(
                        RefRecord(
                            from_symbol=owner,
                            to_symbol=target,
                            ref_kind="import-use",
                            file=file_record.path,
                            line=line_no,
                            snippet=line.strip(),
                        )
                    )
        else:
            owner = file_record.symbols[0] if file_record.symbols else file_record.path
            for line_no, line in enumerate(lines, start=1):
                for token in IDENT_RE.findall(line):
                    for target in _match_lookup_keys(token, by_symbol_id, by_module, by_name):
                        key = (owner, target, "doc-mention", file_record.path, line_no)
                        if key in seen:
                            continue
                        seen.add(key)
                        refs.append(
                            RefRecord(
                                from_symbol=owner,
                                to_symbol=target,
                                ref_kind="doc-mention",
                                file=file_record.path,
                                line=line_no,
                                snippet=line.strip(),
                            )
                        )

    # Add a small unknown bucket for direct symbol text that remains unresolved in docs.
    for file_record in files:
        if file_record.language != LANG_MD:
            continue
        path = root / file_record.path
        text = _read_text(path)
        if text is None:
            continue
        for line_no, line in enumerate(text.splitlines(), start=1):
            if "TODO" in line or "unknown" in line.lower():
                refs.append(
                    RefRecord(
                        from_symbol=file_record.symbols[0] if file_record.symbols else file_record.path,
                        to_symbol="unknown",
                        ref_kind="unknown",
                        file=file_record.path,
                        line=line_no,
                        snippet=line.strip(),
                    )
                )
                break

    return refs


def scan_repo(root: Path) -> RepoIndex:
    files: list[FileRecord] = []
    symbols: list[SymbolRecord] = []

    for path in _iter_files(root):
        if path.suffix == ".agda":
            file_record, file_symbols = _parse_agda_file(path, root)
        else:
            file_record, file_symbols = _parse_markdown_file(path, root)
        files.append(file_record)
        symbols.extend(file_symbols)

    references = _build_references(root, files, symbols)
    return RepoIndex(
        schema_version=SCHEMA_VERSION,
        root=root.as_posix(),
        generated_at="source-scan",
        files=files,
        symbols=symbols,
        references=references,
    )


def load_index(root: Path, index_path: Path) -> RepoIndex:
    if index_path.exists():
        payload = json.loads(index_path.read_text(encoding="utf-8"))
        return RepoIndex.from_json(payload)
    return scan_repo(root)


def write_index(index: RepoIndex, index_path: Path) -> None:
    index_path.parent.mkdir(parents=True, exist_ok=True)
    index_path.write_text(json.dumps(index.to_json(), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _symbol_score(symbol: SymbolRecord, query: str) -> tuple[int, int, int, int, str]:
    exact_id = int(symbol.symbol_id == query)
    exact_name = int(symbol.name == query)
    prefix_id = int(symbol.symbol_id.startswith(query))
    prefix_name = int(symbol.name.startswith(query))
    return (-exact_id, -exact_name, -prefix_id, -prefix_name, symbol.symbol_id)


def _filter_symbols(
    symbols: list[SymbolRecord],
    kind: str | None,
    source: str | None,
) -> list[SymbolRecord]:
    filtered = symbols
    if kind and kind != "all":
        filtered = [symbol for symbol in filtered if symbol.kind == kind]
    if source and source != "all":
        filtered = [symbol for symbol in filtered if symbol.language == source or (source == "docs" and symbol.language == LANG_MD)]
    return filtered


def _resolve_symbols(index: RepoIndex, query: str, kind: str | None, source: str | None) -> list[SymbolRecord]:
    symbols = _filter_symbols(index.symbols, kind, source)
    matches = [
        symbol
        for symbol in symbols
        if symbol.symbol_id == query or symbol.name == query or symbol.symbol_id.startswith(query) or symbol.name.startswith(query)
    ]
    matches.sort(key=lambda symbol: _symbol_score(symbol, query))
    return matches


def _refs_for_symbols(index: RepoIndex, symbols: list[SymbolRecord], source: str | None) -> list[RefRecord]:
    symbol_ids = {symbol.symbol_id for symbol in symbols}
    symbol_names = {symbol.name for symbol in symbols}
    module_names = {symbol.module for symbol in symbols if symbol.module}
    matches: list[RefRecord] = []
    for ref in index.references:
        if source and source != "all":
            if source == "agda" and ref.file.endswith(".md"):
                continue
            if source == "docs" and not ref.file.endswith(".md"):
                continue
        if ref.to_symbol in symbol_ids or ref.to_symbol in symbol_names or ref.to_symbol in module_names:
            matches.append(ref)
    return matches


def _pretty_symbol(symbol: SymbolRecord) -> str:
    pieces = [
        symbol.symbol_id,
        f"  kind: {symbol.kind}",
        f"  module: {symbol.module or 'unknown'}",
        f"  file: {symbol.file}:{symbol.line_start}",
        f"  status: {symbol.status.get('promotion', 'unknown')}",
    ]
    if symbol.doc:
        pieces.append(f"  doc: {symbol.doc}")
    if symbol.snippet:
        pieces.append(f"  summary: {symbol.snippet}")
    return "\n".join(pieces)


def _pretty_refs(refs: list[RefRecord]) -> str:
    buckets: dict[str, list[RefRecord]] = defaultdict(list)
    for ref in refs:
        buckets[ref.ref_kind].append(ref)
    lines: list[str] = []
    for bucket in sorted(buckets):
        lines.append(bucket)
        for ref in buckets[bucket][:40]:
            lines.append(f"  {ref.from_symbol} -> {ref.to_symbol} @ {ref.file}:{ref.line}")
            if ref.snippet:
                lines.append(f"    {ref.snippet}")
    return "\n".join(lines) if lines else "no references"


def _pretty_reqs(symbol: SymbolRecord) -> str:
    lines = [symbol.symbol_id]
    syntactic = symbol.requirements.get("syntactic_requirements", [])
    semantic = symbol.requirements.get("semantic_requirements", [])
    lines.append("  syntactic_requirements:")
    if syntactic:
        for item in syntactic:
            lines.append(f"    - {item.get('kind')}: {item.get('symbol')} ({item.get('source')})")
    else:
        lines.append("    - none")
    lines.append("  semantic_requirements:")
    if semantic:
        for item in semantic:
            lines.append(f"    - {item.get('kind')}: {item.get('symbol', item.get('value', ''))} ({item.get('source')})")
    else:
        lines.append("    - none")
    return "\n".join(lines)


def _pretty_hover(symbol: SymbolRecord) -> str:
    lines = [symbol.symbol_id, f"kind: {symbol.kind}", f"module: {symbol.module or 'unknown'}"]
    if symbol.doc:
        lines.append(f"doc: {symbol.doc}")
    if symbol.signature:
        lines.append(f"signature: {symbol.signature}")
    if symbol.snippet:
        lines.append(f"summary: {symbol.snippet}")
    lines.append(f"status: {symbol.status.get('promotion', 'unknown')}")
    return "\n".join(lines)


def _pretty_complete(symbols: list[SymbolRecord]) -> str:
    if not symbols:
        return "no matches"
    lines: list[str] = []
    for symbol in symbols[:80]:
        lines.append(f"{symbol.symbol_id} [{symbol.kind}]")
    return "\n".join(lines)


def _graph_node(symbol: SymbolRecord, refs: list[RefRecord], depth: int, index: RepoIndex, seen: set[str]) -> dict[str, Any]:
    node = {
        "symbol_id": symbol.symbol_id,
        "name": symbol.name,
        "kind": symbol.kind,
        "module": symbol.module,
        "file": symbol.file,
        "line_start": symbol.line_start,
        "status": symbol.status,
    }
    if depth <= 0 or symbol.symbol_id in seen:
        return node
    seen.add(symbol.symbol_id)

    outgoing: list[dict[str, Any]] = []
    req_targets = symbol.requirements.get("syntactic_requirements", [])
    for item in req_targets:
        target = item.get("symbol", "")
        match = next((candidate for candidate in index.symbols if candidate.symbol_id == target or candidate.name == target), None)
        if match is not None:
            outgoing.append(_graph_node(match, refs, depth - 1, index, seen.copy()))
        else:
            outgoing.append({"symbol_id": target, "kind": item.get("kind"), "unresolved": True})

    incoming = [
        {
            "from_symbol": ref.from_symbol,
            "ref_kind": ref.ref_kind,
            "file": ref.file,
            "line": ref.line,
        }
        for ref in refs
    ]
    node["outgoing"] = outgoing
    node["incoming"] = incoming[:40]
    return node


def _json_envelope(command: str, query: str | None, root: Path, index_path: Path) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "command": command,
        "query": query,
        "root": _relpath(root, root),
        "index": _relpath(index_path, root) if index_path.is_absolute() else index_path.as_posix(),
    }


def _render_command_payload(
    command: str,
    query: str | None,
    root: Path,
    index_path: Path,
    index: RepoIndex,
    args: argparse.Namespace,
) -> tuple[dict[str, Any], str]:
    kind = args.kind
    source = args.source

    if command == "build":
        payload = _json_envelope(command, None, root, index_path)
        payload["files"] = len(index.files)
        payload["symbols"] = len(index.symbols)
        payload["references"] = len(index.references)
        payload["status"] = "written" if index_path.exists() else "in-memory"
        return payload, (
            f"built {len(index.symbols)} symbols, {len(index.references)} references, {len(index.files)} files"
        )

    matches = _resolve_symbols(index, query or "", kind, source)
    payload = _json_envelope(command, query, root, index_path)
    if command == "defs":
        payload["matches"] = [asdict(symbol) for symbol in matches]
        text = "\n\n".join(_pretty_symbol(symbol) for symbol in matches[:20]) if matches else "no matches"
        return payload, text

    if command == "hover":
        payload["matches"] = [asdict(matches[0])] if matches else []
        return payload, _pretty_hover(matches[0]) if matches else "no matches"

    if command == "complete":
        payload["matches"] = [asdict(symbol) for symbol in matches]
        return payload, _pretty_complete(matches)

    if command == "status":
        payload["matches"] = [
            {"symbol_id": symbol.symbol_id, "status": symbol.status}
            for symbol in matches
        ]
        if not matches:
            return payload, "unknown"
        return payload, "\n".join(f"{symbol.symbol_id}: {symbol.status.get('promotion', 'unknown')}" for symbol in matches[:20])

    if command == "reqs":
        payload["matches"] = [asdict(symbol) for symbol in matches]
        if not matches:
            return payload, "no matches"
        return payload, _pretty_reqs(matches[0])

    if command == "refs":
        refs = _refs_for_symbols(index, matches, source)
        payload["matches"] = [asdict(ref) for ref in refs]
        return payload, _pretty_refs(refs)

    if command == "graph":
        refs = _refs_for_symbols(index, matches, source)
        depth = max(0, int(args.depth or 1))
        graph = [_graph_node(symbol, [ref for ref in refs if ref.to_symbol == symbol.symbol_id], depth, index, set()) for symbol in matches[:10]]
        payload["matches"] = graph
        return payload, json.dumps(graph, indent=2, sort_keys=True)

    raise SystemExit(f"unsupported command: {command}")


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of pretty text.")
    parser.add_argument("--pretty", action="store_true", help="Force pretty output.")
    parser.add_argument("--root", type=Path, default=Path("."), help="Repository root.")
    parser.add_argument("--index", type=Path, default=DEFAULT_INDEX_PATH, help="Index file path.")
    parser.add_argument("--depth", type=int, default=1, help="Graph traversal depth.")
    parser.add_argument("--kind", default="all", help="Filter by symbol kind.")
    parser.add_argument("--source", default="all", help="Filter by source: agda | docs | all.")

    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("build", help="Build the JSON index file.")
    for command in ("defs", "refs", "reqs", "hover", "complete", "graph", "status"):
        sub = subparsers.add_parser(command, help=f"{command} query")
        sub.add_argument("query")

    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    root = args.root.resolve()
    index_path = (root / args.index) if not args.index.is_absolute() else args.index

    if args.command == "build":
        index = scan_repo(root)
        write_index(index, index_path)
    else:
        index = load_index(root, index_path)

    query = getattr(args, "query", None)
    payload, pretty = _render_command_payload(args.command, query, root, index_path, index, args)

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(pretty)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

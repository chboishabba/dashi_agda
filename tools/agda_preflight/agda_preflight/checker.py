from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import re
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple

from tree_sitter import Language, Parser
import tree_sitter_agda

from .rules import extended_diagnostics


_IDENT = r"[A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*"


@dataclass(frozen=True)
class Diagnostic:
    code: str
    message: str
    path: Path
    line: int
    column: int = 1
    hint: Optional[str] = None
    severity: str = "error"
    confidence: str = "high"

    def as_dict(self) -> dict:
        return {
            "code": self.code,
            "message": self.message,
            "path": str(self.path),
            "line": self.line,
            "column": self.column,
            "hint": self.hint,
            "severity": self.severity,
            "confidence": self.confidence,
        }


@dataclass
class FieldInfo:
    name: str
    type_text: str
    line: int

    @property
    def terminal(self) -> Optional[str]:
        return terminal_type_head(self.type_text)

    @property
    def is_set_valued(self) -> bool:
        return self.terminal in {"Set", "Set₁", "Set₂", "Setω", "Prop", "Prop₁"}


@dataclass
class RecordInfo:
    name: str
    fields: Dict[str, FieldInfo] = field(default_factory=dict)
    line: int = 1


@dataclass
class SignatureInfo:
    names: Tuple[str, ...]
    type_text: str
    line: int


@dataclass
class ModuleSummary:
    path: Path
    module_name: str
    imports: Dict[str, str]
    opens: Set[str]
    records: Dict[str, RecordInfo]
    signatures: Dict[str, SignatureInfo]
    source: str


def _language() -> Language:
    return Language(tree_sitter_agda.language())


def _parser() -> Parser:
    return Parser(_language())


def walk(node) -> Iterator:
    yield node
    for child in node.children:
        yield from walk(child)


def _known_syntax_grammar_gap(node, source: str) -> bool:
    """Recognize only the known false ERROR nodes from tree-sitter-agda 1.3.3.

    The grammar's treatment of bare imports and standard record declarations
    yields ERROR nodes for valid Agda.  Filter the narrow artifact shapes, not
    arbitrary record contents, so TSAGDA000 remains useful for real syntax
    damage.
    """
    lines = source.splitlines()
    row, column = node.start_point
    if row >= len(lines):
        return False
    line = lines[row]
    text = source.encode("utf-8")[node.start_byte : node.end_byte].decode(
        "utf-8", "replace"
    )
    parent_type = node.parent.type if node.parent is not None else ""

    if parent_type == "source_file" and re.fullmatch(
        r"\s*import\s+[A-Za-z][A-Za-z0-9_.']*(?:\s+as\s+\S+)?\s*",
        line,
    ):
        return True

    record_header = re.compile(
        rf"^\s*record\s+{_IDENT}.*:\s*Set(?:[₀-₉ω]*)?\s+where\s*$"
    )
    if parent_type == "source_file" and record_header.match(line) and re.match(
        r"where\s*\n\s*constructor\b", text
    ):
        return True
    if parent_type == "record_signature" and re.match(
        r"Set(?:[₀-₉ω]*)?\s+where\s*\n\s*constructor\b", text
    ):
        return True
    if parent_type == "record_declarations_block" and re.fullmatch(
        rf"\s*constructor\s+{_IDENT}\s*", text
    ) and re.match(rf"\s*constructor\s+{_IDENT}\b", line):
        return True
    if parent_type == "source_file" and re.fullmatch(r"\s*field\s*", line):
        previous = lines[row - 1] if row else ""
        if re.match(rf"\s*constructor\s+{_IDENT}\b", previous):
            return True
    return False


def terminal_type_head(text: str) -> Optional[str]:
    """Return only an obvious terminal codomain head.

    This is intentionally conservative.  It understands enough to distinguish
    things such as '(n : Nat) → Set' from '(n : Nat) → ⊤' without pretending
    to normalize general dependent Agda types.
    """
    s = re.sub(r"--[^\n]*", " ", text)
    s = re.sub(r"\s+", " ", s).strip()
    if not s:
        return None
    # Strip a few balanced-looking trailing delimiters used around codomains.
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        s = s[1:-1].strip()
    pieces = re.split(r"\s*(?:→|->)\s*", s)
    tail = pieces[-1].strip()
    m = re.match(r"([A-Za-z_⊤⊥][A-Za-z0-9_'₀-₉⊤⊥ω]*)", tail)
    return m.group(1) if m else None


def _module_name(source: str, path: Path, root: Path) -> str:
    m = re.search(r"(?m)^\s*module\s+([A-Za-z0-9_.']+)\s+where\b", source)
    if m:
        return m.group(1)
    try:
        rel = path.resolve().relative_to(root.resolve())
        return ".".join(rel.with_suffix("").parts)
    except ValueError:
        return path.stem


def _imports(source: str) -> Dict[str, str]:
    out: Dict[str, str] = {}
    # Covers 'import M as X' and 'open import M ...'.
    pattern = re.compile(
        r"(?m)^\s*(?:open\s+)?import\s+([A-Za-z0-9_.']+)"
        r"(?:\s+as\s+([A-Za-z0-9_.']+))?"
    )
    for m in pattern.finditer(source):
        module = m.group(1)
        alias = m.group(2) or module.split(".")[-1]
        out[alias] = module
    return out


def _opens(source: str) -> Set[str]:
    out: Set[str] = set()
    for m in re.finditer(r"(?m)^\s*open\s+([A-Za-z0-9_.']+)(?!\s+import\b)", source):
        out.add(m.group(1).split(".")[-1])
    return out


def _collect_records(source: str) -> Dict[str, RecordInfo]:
    lines = source.splitlines()
    records: Dict[str, RecordInfo] = {}
    i = 0
    while i < len(lines):
        m = re.match(rf"^record\s+({_IDENT})\b.*", lines[i])
        if not m:
            i += 1
            continue
        name = m.group(1)
        rec = RecordInfo(name=name, line=i + 1)
        j = i + 1
        in_field_block = False
        while j < len(lines):
            line = lines[j]
            if line and not line[0].isspace():
                break
            if re.match(r"^\s+field\s*$", line):
                in_field_block = True
                j += 1
                continue
            if in_field_block:
                fm = re.match(rf"^\s+({_IDENT})\s*:\s*(.*)$", line)
                if fm:
                    fname = fm.group(1)
                    parts = [fm.group(2).strip()]
                    k = j + 1
                    # Continuation lines are more deeply indented and are not a
                    # new field declaration.
                    while k < len(lines):
                        nxt = lines[k]
                        if nxt and not nxt[0].isspace():
                            break
                        if re.match(rf"^\s+{_IDENT}\s*:", nxt):
                            break
                        if re.match(r"^\s+(?:field|open|constructor)\b", nxt):
                            break
                        if nxt.strip():
                            parts.append(nxt.strip())
                        k += 1
                    rec.fields[fname] = FieldInfo(
                        name=fname,
                        type_text=" ".join(parts),
                        line=j + 1,
                    )
                    j = k
                    continue
            j += 1
        records[name] = rec
        i = max(j, i + 1)
    return records


def _collect_signatures(source: str) -> Dict[str, SignatureInfo]:
    lines = source.splitlines()
    result: Dict[str, SignatureInfo] = {}
    i = 0
    excluded = {"module", "record", "data", "open", "import", "postulate", "private", "abstract"}
    while i < len(lines):
        line = lines[i]
        if line.startswith((" ", "\t")) or line.lstrip().startswith("--"):
            i += 1
            continue
        m = re.match(r"^(.+?)\s*:\s*(.*)$", line)
        if not m:
            i += 1
            continue
        lhs = m.group(1).strip()
        first = lhs.split()[0] if lhs.split() else ""
        if first in excluded:
            i += 1
            continue
        names = tuple(n for n in lhs.split() if re.fullmatch(_IDENT, n))
        if not names:
            i += 1
            continue
        parts = [m.group(2).strip()]
        j = i + 1
        while j < len(lines):
            nxt = lines[j]
            if nxt and not nxt[0].isspace():
                break
            if nxt.strip() and not nxt.lstrip().startswith("--"):
                parts.append(nxt.strip())
            j += 1
        info = SignatureInfo(names=names, type_text=" ".join(parts), line=i + 1)
        for name in names:
            result[name] = info
        i = max(j, i + 1)
    return result


def _binder_types(type_text: str) -> Dict[str, str]:
    out: Dict[str, str] = {}
    # Deliberately shallow: enough for '(A : AlignedModel C T)' binders.
    for m in re.finditer(rf"\(({_IDENT})\s*:\s*([^()]*)\)", type_text):
        out[m.group(1)] = m.group(2).strip()
    return out


def _record_blocks(source: str) -> Iterator[Tuple[str, int, str]]:
    lines = source.splitlines()
    i = 0
    while i < len(lines):
        m = re.match(rf"^({_IDENT})\b[^=]*=\s*(.*)$", lines[i])
        if not m:
            i += 1
            continue
        name = m.group(1)
        j = i
        chunk = [m.group(2)]
        # Read only this top-level definition.
        k = i + 1
        while k < len(lines):
            if lines[k] and not lines[k][0].isspace():
                break
            chunk.append(lines[k])
            k += 1
        text = "\n".join(chunk)
        pos = text.find("record")
        brace = text.find("{", pos + 6) if pos >= 0 else -1
        if pos >= 0 and brace >= 0:
            depth = 0
            end = None
            for off, ch in enumerate(text[brace:], start=brace):
                if ch == "{":
                    depth += 1
                elif ch == "}":
                    depth -= 1
                    if depth == 0:
                        end = off
                        break
            if end is not None:
                yield name, i + 1, text[brace + 1 : end]
        i = max(k, i + 1)


def _assignments(body: str) -> Dict[str, str]:
    # Record syntax in this repository consistently separates fields with ';'.
    chunks = re.split(r"(?m)^\s*;\s*", body)
    out: Dict[str, str] = {}
    for chunk in chunks:
        chunk = chunk.strip()
        if not chunk:
            continue
        m = re.match(rf"({_IDENT})\s*=\s*(.*)", chunk, flags=re.S)
        if m:
            out[m.group(1)] = m.group(2).strip()
    return out


class Checker:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.parser = _parser()
        self._summary_cache: Dict[Path, ModuleSummary] = {}

    def module_path(self, module: str) -> Path:
        return self.root.joinpath(*module.split(".")).with_suffix(".agda")

    def parse_summary(self, path: Path) -> ModuleSummary:
        path = path.resolve()
        cached = self._summary_cache.get(path)
        if cached is not None:
            return cached
        source = path.read_text(encoding="utf-8")
        summary = ModuleSummary(
            path=path,
            module_name=_module_name(source, path, self.root),
            imports=_imports(source),
            opens=_opens(source),
            records=_collect_records(source),
            signatures=_collect_signatures(source),
            source=source,
        )
        self._summary_cache[path] = summary
        return summary

    def imported_summaries(self, summary: ModuleSummary) -> Dict[str, ModuleSummary]:
        out: Dict[str, ModuleSummary] = {}
        for alias, module in summary.imports.items():
            path = self.module_path(module)
            if path.exists():
                out[alias] = self.parse_summary(path)
        return out

    def check(self, path: Path) -> List[Diagnostic]:
        path = path.resolve()
        summary = self.parse_summary(path)
        diagnostics: List[Diagnostic] = []
        diagnostics.extend(self._syntax_diagnostics(summary))
        diagnostics.extend(self._projection_sort_diagnostics(summary))
        diagnostics.extend(self._implicit_projection_receiver_diagnostics(summary))
        diagnostics.extend(self._record_shape_diagnostics(summary))
        diagnostics.extend(extended_diagnostics(self, summary, Diagnostic))

        # Some catalogue entries are intentionally more specific views of the
        # same high-confidence structural event. Emit aliases centrally so the
        # documented diagnostic surface stays synchronized across rule engines.
        aliases = {
            "TSAGDA002": ("TSAGDA171",),
            "TSAGDA003": ("TSAGDA065", "TSAGDA067"),
            "TSAGDA012": ("TSAGDA175",),
            "TSAGDA045": ("TSAGDA110",),
            "TSAGDA042": ("TSAGDA112",),
        }
        for diagnostic in list(diagnostics):
            for code in aliases.get(diagnostic.code, ()):
                diagnostics.append(
                    Diagnostic(
                        code,
                        diagnostic.message,
                        diagnostic.path,
                        diagnostic.line,
                        diagnostic.column,
                        diagnostic.hint,
                        diagnostic.severity,
                        diagnostic.confidence,
                    )
                )
        # Stable de-duplication.
        seen = set()
        unique = []
        for d in diagnostics:
            key = (d.code, d.line, d.column, d.message)
            if key not in seen:
                seen.add(key)
                unique.append(d)
        return sorted(unique, key=lambda d: (d.line, d.column, d.code))

    def _syntax_diagnostics(self, summary: ModuleSummary) -> List[Diagnostic]:
        data = summary.source.encode("utf-8")
        tree = self.parser.parse(data)
        result: List[Diagnostic] = []
        for node in walk(tree.root_node):
            if node.type == "ERROR" or getattr(node, "is_missing", False):
                if node.type == "ERROR" and _known_syntax_grammar_gap(node, summary.source):
                    continue
                row, col = node.start_point
                result.append(
                    Diagnostic(
                        "TSAGDA000",
                        f"tree-sitter syntax node {node.type!r}",
                        summary.path,
                        row + 1,
                        col + 1,
                        "Fix syntax before semantic preflight; Agda may report a later, noisier error.",
                    )
                )
        return result

    def _projection_sort_diagnostics(self, summary: ModuleSummary) -> List[Diagnostic]:
        result: List[Diagnostic] = []
        opened_records = {
            name: rec for name, rec in summary.records.items() if name in summary.opens
        }
        if not opened_records:
            return result

        set_fields: Dict[str, Tuple[str, FieldInfo]] = {}
        for rname, rec in opened_records.items():
            for fname, finfo in rec.fields.items():
                if finfo.is_set_valued:
                    set_fields[fname] = (rname, finfo)

        for sig in summary.signatures.values():
            for field_name, (record_name, _) in set_fields.items():
                # A bare projection immediately before an arrow/end/delimiter is
                # being used as the type itself.  'Parameter M' does not match.
                pat = re.compile(
                    rf"(?<![.A-Za-z0-9_'])\b{re.escape(field_name)}\b"
                    rf"\s*(?=(?:→|->|$|\)|\}}|\]))"
                )
                m = pat.search(sig.type_text)
                if not m:
                    continue
                result.append(
                    Diagnostic(
                        "TSAGDA001",
                        (
                            f"{field_name} is a projection of {record_name}, so its "
                            f"outer shape is {record_name} → Set; it is used here unapplied."
                        ),
                        summary.path,
                        sig.line,
                        1,
                        f"Apply the projection to the model, e.g. {field_name} M.",
                    )
                )
        return result

    def _implicit_projection_receiver_diagnostics(
        self, summary: ModuleSummary
    ) -> List[Diagnostic]:
        """Find a projection receiver written as ``_`` despite a matching binder.

        Agda can often infer a projection receiver, so this rule reports only
        when the containing signature has a named binder whose record exposes
        that same projection.  This catches the common ``Alias.field _`` form
        that leaves an otherwise available record receiver as a metavariable.
        """
        imported = self.imported_summaries(summary)
        signatures = sorted(
            {info.line: info for info in summary.signatures.values()}.values(),
            key=lambda info: info.line,
        )
        result: List[Diagnostic] = []
        call = re.compile(rf"\b({_IDENT})\.({_IDENT})\s+_")
        binder = re.compile(rf"[({{]\s*({_IDENT})\s*:\s*([^(){{}}]*)[)}}]")

        for line_number, line in enumerate(summary.source.splitlines(), start=1):
            signature = None
            for candidate in signatures:
                if candidate.line <= line_number:
                    signature = candidate
                else:
                    break
            if signature is None:
                continue

            for match in call.finditer(line):
                alias, field_name = match.groups()
                imported_summary = imported.get(alias)
                if imported_summary is None:
                    continue
                for binder_match in binder.finditer(signature.type_text):
                    binder_name, binder_type = binder_match.groups()
                    matching_record = next(
                        (
                            record
                            for record_name, record in imported_summary.records.items()
                            if field_name in record.fields
                            and re.search(
                                rf"\b{re.escape(alias)}\.{re.escape(record_name)}\b",
                                binder_type,
                            )
                        ),
                        None,
                    )
                    if matching_record is None:
                        continue
                    result.append(
                        Diagnostic(
                            "TSAGDA002",
                            (
                                f"{alias}.{field_name} uses `_` for its "
                                f"{matching_record.name} receiver, although "
                                f"{binder_name} is a matching binder in scope; "
                                "this leaves a projection receiver metavariable."
                            ),
                            summary.path,
                            line_number,
                            match.start() + 1,
                            (
                                f"Pass the receiver explicitly, e.g. "
                                f"{alias}.{field_name} {binder_name} … ."
                            ),
                        )
                    )
                    break
        return result

    def _known_records(
        self, summary: ModuleSummary
    ) -> Tuple[Dict[str, RecordInfo], Dict[str, Dict[str, RecordInfo]]]:
        local = dict(summary.records)
        imported: Dict[str, Dict[str, RecordInfo]] = {}
        for alias, imp in self.imported_summaries(summary).items():
            imported[alias] = imp.records
        return local, imported

    def _resolve_record(
        self,
        type_text: str,
        local: Dict[str, RecordInfo],
        imported: Dict[str, Dict[str, RecordInfo]],
    ) -> Optional[RecordInfo]:
        # A record result is the terminal codomain of a signature.  Resolve
        # that head first, rather than returning the first record name that
        # happens to occur in a binder earlier in the signature.
        terminal = terminal_type_head(type_text)
        if terminal is not None:
            local_match = local.get(terminal)
            if local_match is not None:
                return local_match

        # Prefer qualified references.
        for alias, records in imported.items():
            for rname, rec in records.items():
                if re.search(rf"\b{re.escape(alias)}\.{re.escape(rname)}\b", type_text):
                    return rec
        return None

    def _record_shape_diagnostics(self, summary: ModuleSummary) -> List[Diagnostic]:
        local, imported = self._known_records(summary)
        result: List[Diagnostic] = []

        for def_name, def_line, body in _record_blocks(summary.source):
            sig = summary.signatures.get(def_name)
            if sig is None:
                continue
            target = self._resolve_record(sig.type_text, local, imported)
            if target is None:
                continue
            binders = _binder_types(sig.type_text)
            assigns = _assignments(body)

            for field_name, rhs in assigns.items():
                expected = target.fields.get(field_name)
                if expected is None:
                    continue
                expected_terminal = expected.terminal
                if expected_terminal is None:
                    continue

                # High-confidence pattern:
                #   field = λ n → projection A n
                lm = re.match(
                    rf"λ\s+({_IDENT})\s*→\s*({_IDENT})\s+({_IDENT})\s+\1\b",
                    re.sub(r"\s+", " ", rhs),
                )
                if not lm:
                    continue
                projection, record_var = lm.group(2), lm.group(3)
                binder_type = binders.get(record_var)
                if binder_type is None:
                    continue
                source_record = self._resolve_record(binder_type, local, imported)
                if source_record is None:
                    continue
                actual_field = source_record.fields.get(projection)
                if actual_field is None:
                    continue
                actual_terminal = actual_field.terminal
                if actual_terminal is None or actual_terminal == expected_terminal:
                    continue

                # Only report terminal heads that clearly denote a sort/type
                # boundary.  Avoid guessing on arbitrary mathematical carriers.
                sortish = {"Set", "Set₁", "Set₂", "Setω", "Prop", "Prop₁"}
                if expected_terminal not in sortish and actual_terminal not in sortish:
                    continue

                result.append(
                    Diagnostic(
                        "TSAGDA003",
                        (
                            f"record field {field_name} expects terminal codomain "
                            f"{expected_terminal}, but {projection} from "
                            f"{source_record.name} has terminal codomain {actual_terminal}."
                        ),
                        summary.path,
                        def_line,
                        1,
                        (
                            "Align the source record field kind with the destination "
                            "gate instead of coercing the record assignment."
                        ),
                    )
                )
        return result

    def dependency_graph(self) -> Dict[str, Set[str]]:
        """Return module -> direct imported modules for repository Agda files."""
        graph: Dict[str, Set[str]] = {}
        for path in self.root.rglob("*.agda"):
            # Skip generated/cache/vendor trees when possible.
            parts = set(path.relative_to(self.root).parts)
            if parts & {".cache", "build", "dist", "vendor", "third_party", "tmp"}:
                continue
            try:
                source = path.read_text(encoding="utf-8")
            except (UnicodeDecodeError, OSError):
                continue
            module = _module_name(source, path, self.root)
            graph[module] = set(_imports(source).values())
        return graph

    def affected_modules(self, path: Path) -> List[str]:
        summary = self.parse_summary(path)
        start = summary.module_name
        graph = self.dependency_graph()
        reverse: Dict[str, Set[str]] = {}
        for module, deps in graph.items():
            for dep in deps:
                reverse.setdefault(dep, set()).add(module)

        # Breadth-first order is a useful compile frontier: changed module first,
        # then its nearest consumers, then progressively higher aggregate users.
        order: List[str] = []
        seen = {start}
        frontier = [start]
        while frontier:
            nxt: List[str] = []
            for module in sorted(frontier):
                order.append(module)
                for consumer in sorted(reverse.get(module, ())):
                    if consumer not in seen:
                        seen.add(consumer)
                        nxt.append(consumer)
            frontier = nxt
        return order

    def check_closure(self, path: Path) -> List[Diagnostic]:
        diagnostics: List[Diagnostic] = []
        for module in self.affected_modules(path):
            module_path = self.module_path(module)
            if module_path.exists():
                diagnostics.extend(self.check(module_path))
        return diagnostics

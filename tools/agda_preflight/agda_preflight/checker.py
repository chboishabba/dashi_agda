from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple

from tree_sitter import Language, Parser
import tree_sitter_agda

from .rules import extended_diagnostics
from .ast_index import AstIndex, build_ast_index, significant_tokens, typed_binders
from .shapes import shape_from_node, terminal_head, explicit_arity



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
    type_node: object | None = None
    terminal: Optional[str] = None

    @property
    def is_set_valued(self) -> bool:
        return self.terminal in {"Set", "Set₀", "Set₁", "Set₂", "Setω", "Prop", "Prop₁"}


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
    type_node: object | None = None


@dataclass
class ModuleSummary:
    path: Path
    module_name: str
    imports: Dict[str, str]
    opens: Set[str]
    records: Dict[str, RecordInfo]
    signatures: Dict[str, SignatureInfo]
    source: str
    ast: AstIndex


def _language() -> Language:
    return Language(tree_sitter_agda.language())


def _parser() -> Parser:
    return Parser(_language())


def walk(node) -> Iterator:
    yield node
    for child in node.children:
        yield from walk(child)


def _known_syntax_grammar_gap(node, source: str) -> bool:
    """Recognize only known tree-sitter-agda 1.3.3 grammar artifacts."""
    source_bytes = source.encode("utf-8")
    tokens = significant_tokens(source_bytes, node)
    texts = [token.text for token in tokens]
    parent_type = node.parent.type if node.parent is not None else ""

    if parent_type == "source_file" and "import" in texts:
        return True
    if parent_type in {"source_file", "record_signature"}:
        if "record" in texts and "where" in texts and "constructor" in texts:
            return True
    if parent_type == "record_declarations_block" and texts[:1] == ["constructor"]:
        return True
    if parent_type == "source_file" and texts == ["field"]:
        previous = node.prev_named_sibling
        if previous is not None:
            prev_tokens = [token.text for token in significant_tokens(source_bytes, previous)]
            if prev_tokens[:1] == ["constructor"]:
                return True
    return False


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
        ast = build_ast_index(self.parser, path, self.root, source)
        records: Dict[str, RecordInfo] = {}
        for name, record in ast.records.items():
            records[name] = RecordInfo(
                name=name,
                line=record.line,
                fields={
                    field_name: FieldInfo(
                        name=field_name,
                        type_text=field.type_text,
                        line=field.line,
                        type_node=field.type_node,
                        terminal=(
                            terminal_head(shape_from_node(ast.source_bytes, field.type_node))
                            if field.type_node is not None else None
                        ),
                    )
                    for field_name, field in record.fields.items()
                },
            )
        signatures: Dict[str, SignatureInfo] = {
            name: SignatureInfo(
                names=signature.names,
                type_text=signature.type_text,
                line=signature.line,
                type_node=signature.type_node,
            )
            for name, signature in ast.signatures.items()
        }
        summary = ModuleSummary(
            path=path,
            module_name=ast.module_name,
            imports=ast.import_map,
            opens=ast.opened_namespaces,
            records=records,
            signatures=signatures,
            source=source,
            ast=ast,
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

        for name, ast_sig in summary.ast.signatures.items():
            if ast_sig.type_node is None:
                continue
            tokens = significant_tokens(summary.ast.source_bytes, ast_sig.type_node)
            for index, token in enumerate(tokens):
                entry = set_fields.get(token.text)
                if entry is None:
                    continue
                record_name, _ = entry
                following = tokens[index + 1] if index + 1 < len(tokens) else None
                # A type-valued projection is suspicious only when it terminates
                # a type atom instead of receiving its record value.
                if following is not None and following.text not in {"→", "->", ")", "}", "}}", "⦄", "]"}:
                    continue
                result.append(
                    Diagnostic(
                        "TSAGDA001",
                        (
                            f"{token.text} is a projection of {record_name}, so its "
                            f"outer shape is {record_name} → Set; it is used here unapplied."
                        ),
                        summary.path,
                        token.line,
                        token.column,
                        f"Apply the projection to the model, e.g. {token.text} M.",
                    )
                )
        return result

    def _implicit_projection_receiver_diagnostics(
        self, summary: ModuleSummary
    ) -> List[Diagnostic]:
        """Find a projection receiver written as '_' despite a matching binder."""
        imported = self.imported_summaries(summary)
        result: List[Diagnostic] = []

        for function_name, clauses in summary.ast.clauses.items():
            signature = summary.ast.signatures.get(function_name)
            if signature is None or signature.type_node is None:
                continue
            binders = typed_binders(summary.ast.source_bytes, signature.type_node)
            if not binders:
                continue

            for clause in clauses:
                if clause.rhs_node is None:
                    continue
                tokens = significant_tokens(summary.ast.source_bytes, clause.rhs_node)
                for i, token in enumerate(tokens[:-1]):
                    if "." not in token.text or tokens[i + 1].text != "_":
                        continue
                    alias, field_name = token.text.rsplit(".", 1)
                    imported_summary = imported.get(alias)
                    if imported_summary is None:
                        continue
                    matching_record = None
                    matching_binder = None
                    for record_name, record in imported_summary.records.items():
                        if field_name not in record.fields:
                            continue
                        qualified = f"{alias}.{record_name}"
                        for binder in binders:
                            words = binder.type_text.replace("(", " ").replace(")", " ").split()
                            if qualified in words or record_name in words:
                                matching_record = record
                                matching_binder = binder
                                break
                        if matching_binder is not None:
                            break
                    if matching_record is None or matching_binder is None:
                        continue
                    result.append(
                        Diagnostic(
                            "TSAGDA002",
                            (
                                f"{alias}.{field_name} uses '_' for its "
                                f"{matching_record.name} receiver, although "
                                f"{matching_binder.name} is a matching binder in scope; "
                                "this leaves a projection receiver metavariable."
                            ),
                            summary.path,
                            token.line,
                            token.column,
                            (
                                f"Pass the receiver explicitly, e.g. "
                                f"{alias}.{field_name} {matching_binder.name} … ."
                            ),
                        )
                    )
        return result

    def _record_shape_diagnostics(self, summary: ModuleSummary) -> List[Diagnostic]:
        result: List[Diagnostic] = []
        imported = self.imported_summaries(summary)

        def resolve_record_from_signature(signature):
            if signature is None or signature.type_node is None:
                return None
            head = terminal_head(shape_from_node(summary.ast.source_bytes, signature.type_node))
            if not head:
                return None
            if "." in head:
                alias, record_name = head.rsplit(".", 1)
                owner = imported.get(alias)
                if owner is not None:
                    record = owner.ast.records.get(record_name)
                    if record is not None:
                        return owner, record
            record = summary.ast.records.get(head)
            if record is not None:
                return summary, record
            return None

        def resolve_binder_record(signature, binder_name):
            if signature is None or signature.type_node is None:
                return None
            for binder in typed_binders(summary.ast.source_bytes, signature.type_node):
                if binder.name != binder_name:
                    continue
                words = (
                    binder.type_text
                    .replace("(", " ")
                    .replace(")", " ")
                    .replace("{", " ")
                    .replace("}", " ")
                    .split()
                )
                for word in words:
                    clean = word.strip(",")
                    if "." in clean:
                        alias, record_name = clean.rsplit(".", 1)
                        owner = imported.get(alias)
                        if owner is not None and record_name in owner.ast.records:
                            return owner, owner.ast.records[record_name]
                    if clean in summary.ast.records:
                        return summary, summary.ast.records[clean]
            return None

        for record_expr in summary.ast.record_expressions:
            if not record_expr.owner_function:
                continue
            signature = summary.ast.signatures.get(record_expr.owner_function)
            target_ref = resolve_record_from_signature(signature)
            if target_ref is None:
                continue
            target_owner, target = target_ref
            target_bytes = target_owner.ast.source_bytes

            for assignment in record_expr.assignments:
                expected = target.fields.get(assignment.name)
                if expected is None or expected.type_node is None or assignment.expr_node is None:
                    continue
                expected_head = terminal_head(shape_from_node(target_bytes, expected.type_node))
                tokens = significant_tokens(summary.ast.source_bytes, assignment.expr_node)

                # High-confidence structural form:
                #   λ n → projection A n
                arrow_positions = [i for i, token in enumerate(tokens) if token.text in {"→", "->"}]
                body_tokens = tokens[arrow_positions[-1] + 1:] if arrow_positions else tokens
                if len(body_tokens) < 2:
                    continue
                projection = body_tokens[0].text
                receiver = body_tokens[1].text
                source_ref = resolve_binder_record(signature, receiver)
                if source_ref is None:
                    continue
                source_owner, source_record = source_ref
                actual = source_record.fields.get(projection)
                if actual is None or actual.type_node is None:
                    continue
                actual_head = terminal_head(
                    shape_from_node(source_owner.ast.source_bytes, actual.type_node)
                )
                if expected_head is None or actual_head is None or expected_head == actual_head:
                    continue
                sortish = {"Set", "Set₀", "Set₁", "Set₂", "Setω", "Prop", "Prop₁"}
                if expected_head not in sortish and actual_head not in sortish:
                    continue
                result.append(
                    Diagnostic(
                        "TSAGDA003",
                        (
                            f"record field {assignment.name} expects terminal codomain "
                            f"{expected_head}, but {projection} from "
                            f"{source_record.name} has terminal codomain {actual_head}."
                        ),
                        summary.path,
                        assignment.line,
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
                summary = self.parse_summary(path)
            except (UnicodeDecodeError, OSError):
                continue
            graph[summary.module_name] = set(summary.imports.values())
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

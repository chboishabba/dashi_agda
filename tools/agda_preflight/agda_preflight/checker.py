from __future__ import annotations

from dataclasses import dataclass, field, replace
from pathlib import Path
import hashlib
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple

from tree_sitter import Language, Parser
import tree_sitter_agda

from .rules import extended_diagnostics
from .ast_index import AstIndex, build_ast_index, significant_tokens, typed_binders
from .shapes import shape_from_node, terminal_head, explicit_arity
from .evidence import DIAGNOSTIC_ALIASES, EvidenceLevel, evidence_name, policy_for
from .timing import Profiler
from .fixes import SuggestedFix
from .fix_engine import enrich_diagnostics
from .interfaces import ModuleInterface, interface_from_summary



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
    evidence: str = "dashi-index"
    minimum_evidence: str = "dashi-index"
    evidence_sufficient: bool = True
    root_cause: Optional[str] = None
    explanation: Optional[str] = None
    expected: Optional[str] = None
    found: Optional[str] = None
    fixes: Tuple[SuggestedFix, ...] = field(default_factory=tuple)

    @property
    def diagnostic_id(self) -> str:
        payload = (
            f"{self.path.resolve()}\0{self.code}\0{self.line}\0"
            f"{self.column}\0{self.message}"
        ).encode("utf-8")
        return hashlib.sha256(payload).hexdigest()[:24]

    def as_dict(self) -> dict:
        return {
            "id": self.diagnostic_id,
            "code": self.code,
            "message": self.message,
            "path": str(self.path),
            "line": self.line,
            "column": self.column,
            "hint": self.hint,
            "severity": self.severity,
            "confidence": self.confidence,
            "evidence": self.evidence,
            "minimum_evidence": self.minimum_evidence,
            "evidence_sufficient": self.evidence_sufficient,
            "root_cause": self.root_cause,
            "explanation": self.explanation,
            "expected": self.expected,
            "found": self.found,
            "fixes": [fix.as_dict() for fix in self.fixes],
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

    @property
    def exported_names(self) -> Set[str]:
        names: Set[str] = (
            set(self.signatures)
            | set(self.records)
            | set(self.ast.data)
            | set(self.ast.nested_modules)
        )
        for record in self.ast.records.values():
            names.update(record.fields)
            if record.constructor:
                names.add(record.constructor)
        for data in self.ast.data.values():
            names.update(data.constructors)
        return names


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

    # tree-sitter-agda 1.3.3 may split valid record layout across ERROR /
    # sibling nodes: "where", "constructor", and "field" do not necessarily
    # appear in one ERROR node or next to each other.
    if parent_type in {"source_file", "record_signature", "record_declarations_block"}:
        if any(token in texts for token in ("where", "constructor", "field")):
            previous = node.prev_named_sibling
            following = node.next_named_sibling
            nearby_types = {
                sibling.type
                for sibling in (previous, following)
                if sibling is not None
            }
            if nearby_types & {
                "record",
                "record_signature",
                "record_constructor",
                "fields",
                "function",
                "ERROR",
            }:
                return True
            if texts[:1] in (["constructor"], ["field"], ["where"]):
                return True

    if parent_type == "record_declarations_block" and texts[:1] in (["constructor"], ["field"]):
        return True
    return False


class Checker:
    _REPOSITORY_SCAN_EXCLUDES = {
        ".cache",
        ".git",
        ".github",
        ".venv",
        "build",
        "dist",
        "vendor",
        "third_party",
        "tmp",
        "agda-toolchain",
        "cubical",
        "temp-DOWNLOADED",
        ".parse-smoke",
        ".real-eric-round2",
        ".autonomous-orchestrator",
    }

    def __init__(
        self,
        root: Path,
        *,
        evidence_level: EvidenceLevel = EvidenceLevel.DASHI_INDEX,
        scope_backend=None,
        profiler: Optional[Profiler] = None,
        interfaces: Optional[Dict[str, ModuleInterface]] = None,
    ):
        self.root = root.resolve()
        self.profiler = profiler
        if profiler is None:
            self.parser = _parser()
        else:
            with profiler.stage("startup.tree_sitter_parser"):
                self.parser = _parser()
        self._summary_cache: Dict[Path, ModuleSummary] = {}
        self._interface_cache: Dict[Path, ModuleInterface] = {}
        self._preloaded_interfaces = dict(interfaces or {})
        self._export_cache: Dict[Path, Set[str]] = {}
        self._diagnostic_cache: Dict[Path, List[Diagnostic]] = {}
        self.evidence_level = evidence_level
        self.scope_backend = scope_backend

    def repository_agda_files(self) -> Iterator[Path]:
        """Yield source Agda files while excluding generated/vendor/toolchain trees."""
        for path in self.root.rglob("*.agda"):
            try:
                parts = set(path.relative_to(self.root).parts)
            except ValueError:
                continue
            if parts & self._REPOSITORY_SCAN_EXCLUDES:
                continue
            yield path

    def module_path(self, module: str) -> Path:
        return self.root.joinpath(*module.split(".")).with_suffix(".agda")

    def parse_summary(self, path: Path) -> ModuleSummary:
        path = path.resolve()
        cached = self._summary_cache.get(path)
        if cached is not None:
            return cached
        if self.profiler is None:
            source = path.read_text(encoding="utf-8")
            ast = build_ast_index(self.parser, path, self.root, source)
        else:
            self.profiler.count("files_parsed")
            with self.profiler.stage("source.read"):
                source = path.read_text(encoding="utf-8")
            with self.profiler.stage("parse.tree_sitter"):
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

    @staticmethod
    def _apply_export_directives(
        names: Set[str],
        directives,
    ) -> Set[str]:
        visible = set(names)
        for directive in directives:
            if directive.kind == "using":
                visible.intersection_update(directive.names)
            elif directive.kind == "hiding":
                visible.difference_update(directive.names)
            elif directive.kind == "renaming":
                for old, new in directive.renamings:
                    if old in visible:
                        visible.remove(old)
                        visible.add(new)
        return visible

    def exported_names(
        self,
        summary,
        _seen: Optional[Set[Path]] = None,
    ) -> Set[str]:
        """Return local exports plus conservative public re-exports.

        This models only explicit public opens/imports. It deliberately avoids
        guessing about private/abstract visibility or unresolved module
        applications; those remain outside the hard structural contract.
        """
        if isinstance(summary, ModuleInterface):
            return set(summary.exports)

        cached = self._export_cache.get(summary.path)
        if cached is not None:
            return set(cached)

        seen = set() if _seen is None else set(_seen)
        path = summary.path.resolve()
        if path in seen:
            return set(summary.exported_names)
        seen.add(path)

        exports = set(summary.exported_names)

        for item in summary.ast.imports:
            if not (item.opened and item.public):
                continue
            target_path = self.module_path(item.module)
            if not target_path.exists():
                continue
            try:
                target = self.parse_summary(target_path)
            except (OSError, UnicodeDecodeError):
                continue
            remote = self.exported_names(target, seen)
            exports.update(self._apply_export_directives(remote, item.directives))

        for opened in summary.ast.opens:
            if not opened.public:
                continue
            module = summary.imports.get(opened.target)
            if module is None:
                candidate = self.module_path(opened.target)
                if candidate.exists():
                    module = opened.target
            if module is None:
                continue
            target_path = self.module_path(module)
            if not target_path.exists():
                continue
            try:
                target = self.parse_summary(target_path)
            except (OSError, UnicodeDecodeError):
                continue
            remote = self.exported_names(target, seen)
            exports.update(self._apply_export_directives(remote, opened.directives))

        self._export_cache[path] = set(exports)
        return exports

    def imported_summaries(self, summary: ModuleSummary) -> Dict[str, ModuleSummary]:
        out: Dict[str, ModuleSummary] = {}
        for alias, module in summary.imports.items():
            path = self.module_path(module)
            if path.exists():
                out[alias] = self.parse_summary(path)
        return out

    def module_interface(self, summary: ModuleSummary) -> ModuleInterface:
        path = summary.path.resolve()
        cached = self._interface_cache.get(path)
        if cached is not None:
            return cached
        interface = interface_from_summary(self.root, summary)
        self._interface_cache[path] = interface
        return interface

    def interface_for_module(
        self,
        module: str,
    ) -> Optional[ModuleInterface]:
        preloaded = self._preloaded_interfaces.get(module)
        if preloaded is not None:
            return preloaded
        path = self.module_path(module)
        if not path.exists():
            return None
        summary = self.parse_summary(path)
        interface = self.module_interface(summary)
        return replace(
            interface,
            resolved_exports=tuple(sorted(self.exported_names(summary))),
        )

    def imported_interfaces(
        self,
        summary: ModuleSummary,
    ) -> Dict[str, ModuleInterface]:
        out: Dict[str, ModuleInterface] = {}
        for alias, module in summary.imports.items():
            interface = self.interface_for_module(module)
            if interface is not None:
                out[alias] = interface
        return out

    def structural_check(self, path: Path) -> List[Diagnostic]:
        """Run and cache the cheap tree/index pass without external refinement."""
        path = path.resolve()
        cached = self._diagnostic_cache.get(path)
        if cached is not None:
            return list(cached)

        summary = self.parse_summary(path)
        diagnostics: List[Diagnostic] = []
        if self.profiler is None:
            diagnostics.extend(self._syntax_diagnostics(summary))
            diagnostics.extend(self._projection_sort_diagnostics(summary))
            diagnostics.extend(self._implicit_projection_receiver_diagnostics(summary))
            diagnostics.extend(self._record_shape_diagnostics(summary))
            diagnostics.extend(extended_diagnostics(self, summary, Diagnostic))
        else:
            self.profiler.count("diagnostics_recomputed")
            with self.profiler.stage("diagnostics.local"):
                diagnostics.extend(self._syntax_diagnostics(summary))
                diagnostics.extend(self._projection_sort_diagnostics(summary))
                diagnostics.extend(self._implicit_projection_receiver_diagnostics(summary))
                diagnostics.extend(self._record_shape_diagnostics(summary))
                diagnostics.extend(extended_diagnostics(self, summary, Diagnostic))

        # Apply evidence provenance without invoking an external backend.
        backend = self.scope_backend
        self.scope_backend = None
        try:
            diagnostics = self._apply_evidence_policy(summary, diagnostics)
        finally:
            self.scope_backend = backend

        for diagnostic in list(diagnostics):
            for code in DIAGNOSTIC_ALIASES.get(diagnostic.code, ()):
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
                        diagnostic.evidence,
                        diagnostic.minimum_evidence,
                        diagnostic.evidence_sufficient,
                    )
                )

        seen = set()
        unique = []
        for d in diagnostics:
            key = (d.code, d.line, d.column, d.message)
            if key not in seen:
                seen.add(key)
                unique.append(d)
        if self.profiler is None:
            unique = enrich_diagnostics(self, summary, unique)
        else:
            with self.profiler.stage("fixes.generate"):
                unique = enrich_diagnostics(self, summary, unique)
        result = sorted(unique, key=lambda d: (d.line, d.column, d.code))
        self._diagnostic_cache[path] = list(result)
        return result

    def check(self, path: Path) -> List[Diagnostic]:
        path = path.resolve()
        diagnostics = self.structural_check(path)
        if self.scope_backend is None:
            return diagnostics
        summary = self.parse_summary(path)
        return self.scope_backend.refine(summary, list(diagnostics))

    def _apply_evidence_policy(
        self,
        summary: ModuleSummary,
        diagnostics: List[Diagnostic],
    ) -> List[Diagnostic]:
        """Attach provenance and prevent unsupported hard conclusions.

        Structural rules currently run with at most DASHI_INDEX evidence.
        Scope-dependent diagnostics therefore remain warnings unless an optional
        backend explicitly refines/validates them at AGDA_SCOPE or stronger.
        """
        structural_level = min(self.evidence_level, EvidenceLevel.DASHI_INDEX)
        normalized: List[Diagnostic] = []

        for diagnostic in diagnostics:
            policy = policy_for(diagnostic.code)
            actual = (
                EvidenceLevel.TREE_SITTER
                if policy.minimum == EvidenceLevel.TREE_SITTER
                else structural_level
            )
            sufficient = actual >= policy.minimum
            severity = diagnostic.severity
            confidence = diagnostic.confidence
            hint = diagnostic.hint

            if not sufficient and severity == "error":
                severity = "warning"
                confidence = "insufficient-evidence"
                requirement = evidence_name(policy.minimum)
                extra = (
                    f"Hard conclusion deferred: {diagnostic.code} requires "
                    f"{requirement} evidence."
                )
                hint = f"{hint} {extra}".strip() if hint else extra

            normalized.append(
                Diagnostic(
                    diagnostic.code,
                    diagnostic.message,
                    diagnostic.path,
                    diagnostic.line,
                    diagnostic.column,
                    hint,
                    severity,
                    confidence,
                    evidence_name(actual),
                    evidence_name(policy.minimum),
                    sufficient,
                )
            )

        if self.scope_backend is not None:
            normalized = self.scope_backend.refine(summary, normalized)

        return normalized

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
        imported = self.imported_interfaces(summary)
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
                    for record_name, record in imported_summary.record_map.items():
                        if field_name not in record.field_map:
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
        imported = self.imported_interfaces(summary)

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
                    record = owner.record_map.get(record_name)
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
                        if owner is not None and record_name in owner.record_map:
                            return owner, owner.record_map[record_name]
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

            for assignment in record_expr.assignments:
                target_fields = (
                    target.field_map
                    if isinstance(target_owner, ModuleInterface)
                    else target.fields
                )
                expected = target_fields.get(assignment.name)
                if expected is None or assignment.expr_node is None:
                    continue
                if isinstance(target_owner, ModuleInterface):
                    expected_head = expected.terminal_head
                else:
                    if expected.type_node is None:
                        continue
                    expected_head = terminal_head(
                        shape_from_node(
                            target_owner.ast.source_bytes,
                            expected.type_node,
                        )
                    )
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
                source_fields = (
                    source_record.field_map
                    if isinstance(source_owner, ModuleInterface)
                    else source_record.fields
                )
                actual = source_fields.get(projection)
                if actual is None:
                    continue
                if isinstance(source_owner, ModuleInterface):
                    actual_head = actual.terminal_head
                else:
                    if actual.type_node is None:
                        continue
                    actual_head = terminal_head(
                        shape_from_node(
                            source_owner.ast.source_bytes,
                            actual.type_node,
                        )
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
        for path in self.repository_agda_files():
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

    def dependency_modules(self, path: Path) -> List[str]:
        """Return recursive imports in dependency-first order.

        This deliberately follows only the target's reachable import cone.
        Building the repository-wide dependency graph here made aggregate
        collection parse tens of thousands of unrelated Agda files.
        """
        start_summary = self.parse_summary(path)
        order: List[str] = []
        permanent: Set[str] = set()
        temporary: Set[str] = set()

        def visit(module: str, summary: Optional[ModuleSummary] = None) -> None:
            if module in permanent:
                return
            if module in temporary:
                # TSAGDA029 reports the cycle. Collection itself must remain
                # finite and cheap.
                return

            module_path = self.module_path(module)
            if summary is None:
                if not module_path.exists():
                    return
                try:
                    summary = self.parse_summary(module_path)
                except (OSError, UnicodeDecodeError):
                    return

            temporary.add(module)
            for dependency in sorted(set(summary.imports.values())):
                dependency_path = self.module_path(dependency)
                if dependency_path.exists():
                    visit(dependency)
            temporary.remove(module)
            permanent.add(module)
            order.append(module)

        visit(start_summary.module_name, start_summary)
        return order


    def check_closure(self, path: Path) -> List[Diagnostic]:
        diagnostics: List[Diagnostic] = []
        for module in self.affected_modules(path):
            module_path = self.module_path(module)
            if module_path.exists():
                diagnostics.extend(self.check(module_path))
        return diagnostics

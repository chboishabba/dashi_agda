from __future__ import annotations

from dataclasses import dataclass, field, replace
from importlib.resources import files as resource_files
from pathlib import Path
from typing import Any, Iterable

from tree_sitter import Language, Parser
import tree_sitter_agda

from .model import Relation, SemanticGraph, SourceSpan, Symbol, stable_hash


AGDA_LANGUAGE = Language(tree_sitter_agda.language())

CAPTURE_QUERY = (
    resource_files("dashi_repo_history.queries")
    .joinpath("agda_symbols.scm")
    .read_text(encoding="utf-8")
)


def _make_parser() -> Parser:
    try:
        return Parser(AGDA_LANGUAGE)
    except TypeError:
        parser = Parser()
        if hasattr(parser, "set_language"):
            parser.set_language(AGDA_LANGUAGE)
        else:
            parser.language = AGDA_LANGUAGE
        return parser


PARSER = _make_parser()


def _query_captures(root: Any) -> dict[str, list[Any]]:
    query = AGDA_LANGUAGE.query(CAPTURE_QUERY)
    raw = query.captures(root)
    if isinstance(raw, dict):
        return {str(k): list(v) for k, v in raw.items()}
    captures: dict[str, list[Any]] = {}
    for node, name in raw:
        captures.setdefault(str(name), []).append(node)
    return captures


def _node_text(source: bytes, node: Any) -> str:
    return source[node.start_byte : node.end_byte].decode("utf-8", "replace")


def _span(path: str, node: Any) -> SourceSpan:
    return SourceSpan(
        path=path,
        start_byte=node.start_byte,
        end_byte=node.end_byte,
        start_row=node.start_point[0],
        start_column=node.start_point[1],
        end_row=node.end_point[0],
        end_column=node.end_point[1],
    )


def _ancestors(node: Any) -> Iterable[Any]:
    current = node.parent
    while current is not None:
        yield current
        current = current.parent


def _first_ancestor(node: Any, kinds: set[str]) -> Any | None:
    for ancestor in _ancestors(node):
        if ancestor.type in kinds:
            return ancestor
    return None


def _first_descendant(
    node: Any,
    kinds: set[str],
) -> Any | None:
    stack = [node]
    while stack:
        current = stack.pop()
        if current.type in kinds:
            return current
        stack.extend(reversed(current.children))
    return None


def _first_descendant_name(source: bytes, node: Any) -> str | None:
    found = _first_descendant(
        node,
        {"qid", "id", "field_name", "data_name", "record_name"},
    )
    if found is None:
        return None
    value = _node_text(source, found).strip()
    return value or None


def _identifier_leaves(
    source: bytes,
    node: Any,
    *,
    stop_ancestor_types: set[str] | None = None,
) -> list[tuple[str, Any]]:
    stop_ancestor_types = stop_ancestor_types or set()
    out: list[tuple[str, Any]] = []
    stack = [node]

    while stack:
        current = stack.pop()
        if current is not node and current.type in stop_ancestor_types:
            continue
        if current.child_count == 0 and current.type in {"qid", "id", "bid"}:
            value = _node_text(source, current).strip()
            if value:
                out.append((value, current))
            continue
        stack.extend(reversed(current.children))

    out.sort(key=lambda item: item[1].start_byte)
    return out


def _binding_names(source: bytes, node: Any) -> list[tuple[str, Any]]:
    """Return binder names while excluding the bound type."""

    source_slice = source[node.start_byte : node.end_byte]
    colon = source_slice.find(b":")
    absolute_colon = None if colon < 0 else node.start_byte + colon

    out: list[tuple[str, Any]] = []
    seen: set[str] = set()
    for value, current in _identifier_leaves(source, node):
        if absolute_colon is not None and current.start_byte > absolute_colon:
            continue
        leaf = value.split(".")[-1]
        if leaf and leaf != "_" and leaf not in seen:
            seen.add(leaf)
            out.append((leaf, current))
    return out


def _declaration_fingerprint(
    source: bytes,
    declaration: "RawDeclaration",
) -> str:
    parts: list[str] = []
    for start, end in sorted(declaration.owner_ranges):
        raw = source[start:end].decode("utf-8", "replace")
        masked = raw.replace(declaration.symbol.label, "<SELF>")
        normalized = " ".join(masked.split())
        parts.append(normalized)
    return stable_hash(
        {
            "kind": declaration.symbol.kind,
            "parts": parts,
        }
    )


def _prefix_application_head(node: Any) -> bool:
    """Conservative prefix-application evidence from Tree-sitter structure.

    The nearest enclosing expr must have at least two named children, and the
    reference must occur in the first one. This intentionally does not try to
    reinterpret Agda mixfix/infix syntax.
    """

    expr = _first_ancestor(node, {"expr"})
    if expr is None:
        return False

    child = node
    while child.parent is not None and child.parent is not expr:
        child = child.parent
    if child.parent is not expr:
        return False

    named_children = list(expr.named_children)
    if len(named_children) < 2:
        return False
    return named_children[0] is child


def _reference_kind(source: bytes, node: Any) -> str:
    for ancestor in _ancestors(node):
        if ancestor.type == "rhs":
            rhs_text = _node_text(source, ancestor).lstrip()
            if rhs_text.startswith(":"):
                return "type-depends"
            if rhs_text.startswith("="):
                return "body-depends"
            return "depends"
        if ancestor.type in {
            "type_signature",
            "data_signature",
            "record_signature",
            "typed_binding",
            "fields",
            "postulate",
        }:
            return "type-depends"
        if ancestor.type in {"function", "data", "record"}:
            break
    return "depends"


@dataclass
class PatternCandidate:
    value: str
    span: SourceSpan
    scope: str


@dataclass(frozen=True)
class OpenScope:
    module: str
    using: frozenset[str] | None = None
    hiding: frozenset[str] = frozenset()
    renaming: tuple[tuple[str, str], ...] = ()

    def resolve(self, visible_name: str) -> str | None:
        rename_map = {
            new: old
            for new, old in self.renaming
        }
        original = rename_map.get(visible_name, visible_name)

        # Renamed source spellings are not re-admitted under the old name.
        renamed_away = {
            old
            for new, old in self.renaming
            if new != old
        }
        if (
            visible_name == original
            and visible_name in renamed_away
        ):
            return None

        if (
            self.using is not None
            and visible_name not in self.using
            and original not in self.using
        ):
            return None
        if visible_name in self.hiding or original in self.hiding:
            return None
        return original


@dataclass
class RawReference:
    value: str
    span: SourceSpan
    kind: str
    scope: str
    prefix_application_head: bool = false


@dataclass
class RawDeclaration:
    symbol: Symbol
    owner_ranges: list[tuple[int, int]]
    binders: dict[tuple[str, str], Symbol] = field(default_factory=dict)
    pattern_candidates: list[PatternCandidate] = field(default_factory=list)
    references: list[RawReference] = field(default_factory=list)
    container_label: str | None = None
    container_relation: str | None = None


@dataclass
class FileExtraction:
    path: str
    module: str
    module_symbol: Symbol
    declarations: list[RawDeclaration]
    imports: list[str]
    open_scopes: list[OpenScope]
    parse_error: bool


DECLARATION_ANCESTORS = {
    "type_signature",
    "function",
    "data",
    "data_signature",
    "record",
    "record_signature",
}


def _owner_range(
    declaration: RawDeclaration,
    start: int,
    end: int,
) -> tuple[int, int] | None:
    matches = [
        owner_range
        for owner_range in declaration.owner_ranges
        if owner_range[0] <= start and end <= owner_range[1]
    ]
    if not matches:
        return None
    return min(matches, key=lambda item: item[1] - item[0])


def _scope_id(
    source: bytes,
    declaration: RawDeclaration,
    owner_range: tuple[int, int],
) -> str:
    start, end = owner_range
    raw = source[start:end].decode("utf-8", "replace")
    masked = raw.replace(declaration.symbol.label, "<SELF>")
    normalized = " ".join(masked.split())
    return f"{declaration.symbol.symbol_id}:{stable_hash(normalized)[:20]}"


def _smallest_owner(
    declarations: list[RawDeclaration],
    start: int,
    end: int,
) -> RawDeclaration | None:
    matches: list[tuple[int, RawDeclaration]] = []
    for declaration in declarations:
        owner_range = _owner_range(declaration, start, end)
        if owner_range is not None:
            matches.append(
                (owner_range[1] - owner_range[0], declaration)
            )
    if not matches:
        return None
    return min(matches, key=lambda item: item[0])[1]


def _scope_for_node(
    source: bytes,
    declaration: RawDeclaration,
    node: Any,
) -> str:
    owner_range = _owner_range(
        declaration,
        node.start_byte,
        node.end_byte,
    )
    if owner_range is None:
        return declaration.symbol.symbol_id
    return _scope_id(source, declaration, owner_range)


def _descendants(node: Any, kind: str) -> list[Any]:
    out: list[Any] = []
    stack = [node]
    while stack:
        current = stack.pop()
        if current is not node and current.type == kind:
            out.append(current)
        stack.extend(reversed(current.children))
    out.sort(key=lambda item: item.start_byte)
    return out


def _open_scope(source: bytes, open_node: Any) -> OpenScope | None:
    module_node = _first_descendant(open_node, {"module_name"})
    if module_node is None:
        return None
    module = _node_text(source, module_node).strip()
    if not module:
        return None

    using: set[str] | None = None
    hiding: set[str] = set()
    renaming: list[tuple[str, str]] = []

    for directive in _descendants(open_node, "import_directive"):
        directive_text = _node_text(source, directive).strip()
        ids = [
            _node_text(source, node).strip()
            for node in _descendants(directive, "id")
        ]
        ids = [value for value in ids if value]

        if directive_text.startswith("using"):
            using = set(ids)
            continue

        if directive_text.startswith("hiding"):
            hiding.update(ids)
            continue

        if directive_text.startswith("renaming"):
            for rename_node in _descendants(directive, "renaming"):
                rename_ids = [
                    _node_text(source, node).strip()
                    for node in _descendants(rename_node, "id")
                ]
                if len(rename_ids) >= 2:
                    old, new = rename_ids[0], rename_ids[1]
                    renaming.append((new, old))

    return OpenScope(
        module=module,
        using=None if using is None else frozenset(using),
        hiding=frozenset(hiding),
        renaming=tuple(renaming),
    )


def _container_name(
    source: bytes,
    node: Any,
    *,
    container_type: str,
    name_type: str,
) -> str | None:
    container = _first_ancestor(node, {container_type})
    if container is None:
        return None
    name_node = _first_descendant(container, {name_type})
    if name_node is None:
        return None
    value = _node_text(source, name_node).strip()
    return value or None


def _function_clause_name_and_patterns(
    source: bytes,
    function_node: Any,
) -> tuple[Any | None, list[tuple[str, Any]]]:
    lhs = _first_descendant(function_node, {"lhs"})
    if lhs is None:
        return None, []

    identifiers = _identifier_leaves(
        source,
        lhs,
        stop_ancestor_types={"rewrite_equations", "with_expressions"},
    )
    if not identifiers:
        return None, []

    name_node = identifiers[0][1]
    patterns = identifiers[1:]
    return name_node, patterns


def _function_is_definition(source: bytes, function_node: Any) -> bool:
    rhs = _first_descendant(function_node, {"rhs"})
    if rhs is None:
        return False
    return _node_text(source, rhs).lstrip().startswith("=")


def extract_file(path: str, source: bytes) -> FileExtraction:
    tree = PARSER.parse(source)
    captures = _query_captures(tree.root_node)

    module = Path(path).with_suffix("").as_posix().replace("/", ".")
    module_name_node = None
    for node in captures.get("module_name", []):
        ancestor = _first_ancestor(node, {"module"})
        if ancestor is not None:
            value = _node_text(source, node).strip()
            if value:
                module = value
                module_name_node = node
                break

    module_symbol = Symbol.create(
        label=module,
        kind="module",
        module=module,
        scope=None,
        span=_span(path, module_name_node or tree.root_node),
    )

    imports: list[str] = []
    for node in captures.get("module_name", []):
        if _first_ancestor(node, {"import"}) is not None:
            imports.append(_node_text(source, node).strip())

    open_scopes = [
        scope
        for scope in (
            _open_scope(source, node)
            for node in captures.get("open_decl", [])
        )
        if scope is not None
    ]

    declarations_by_key: dict[tuple[str, str], RawDeclaration] = {}

    def add_decl(
        label: str,
        kind: str,
        owner: Any,
        name_node: Any,
        *,
        container_label: str | None = None,
        container_relation: str | None = None,
    ) -> RawDeclaration | None:
        label = label.strip()
        if not label:
            return None

        symbol = Symbol.create(
            label=label,
            kind=kind,
            module=module,
            scope=None,
            span=_span(path, name_node),
        )
        key = (label, kind)
        existing = declarations_by_key.get(key)
        owner_range = (owner.start_byte, owner.end_byte)

        if existing is None:
            existing = RawDeclaration(
                symbol=symbol,
                owner_ranges=[owner_range],
                container_label=container_label,
                container_relation=container_relation,
            )
            declarations_by_key[key] = existing
        else:
            if owner_range not in existing.owner_ranges:
                existing.owner_ranges.append(owner_range)
            if existing.container_label is None:
                existing.container_label = container_label
            if existing.container_relation is None:
                existing.container_relation = container_relation

        return existing

    for node in captures.get("data_name", []):
        owner = _first_ancestor(node, {"data", "data_signature"})
        if owner is not None:
            add_decl(_node_text(source, node), "data", owner, node)

    for node in captures.get("record_name", []):
        owner = _first_ancestor(node, {"record", "record_signature"})
        if owner is not None:
            add_decl(_node_text(source, node), "record", owner, node)

    for node in captures.get("record_constructor_name", []):
        owner = _first_ancestor(node, {"record_constructor"})
        record_label = _container_name(
            source,
            node,
            container_type="record",
            name_type="record_name",
        )
        if owner is not None:
            add_decl(
                _node_text(source, node),
                "constructor",
                owner,
                node,
                container_label=record_label,
                container_relation="constructor-of",
            )

    for node in captures.get("field_name", []):
        owner = _first_ancestor(
            node,
            DECLARATION_ANCESTORS | {"fields", "postulate"},
        )
        if owner is None:
            continue

        label = _node_text(source, node)
        data_label = _container_name(
            source,
            node,
            container_type="data",
            name_type="data_name",
        )
        record_label = _container_name(
            source,
            node,
            container_type="record",
            name_type="record_name",
        )

        if _first_ancestor(node, {"postulate"}) is not None:
            kind = "postulate"
            container_label = None
            container_relation = None
        elif data_label is not None:
            kind = "constructor"
            container_label = data_label
            container_relation = "constructor-of"
        elif _first_ancestor(node, {"fields"}) is not None:
            kind = "field"
            container_label = record_label
            container_relation = "field-of"
        else:
            kind = "function"
            container_label = None
            container_relation = None

        add_decl(
            label,
            kind,
            owner,
            node,
            container_label=container_label,
            container_relation=container_relation,
        )

    for node in captures.get("function_name", []):
        owner = _first_ancestor(node, {"function"})
        if owner is None:
            continue
        label = _first_descendant_name(source, node)
        if label is not None:
            add_decl(label, "function", owner, node)

    # Function definitions do not carry the function_name alias in the grammar.
    # Recover the leading LHS identifier and collect the remaining identifiers
    # as pattern candidates; known constructors are resolved later, everything
    # else becomes a clause-scoped binder.
    for function_node in captures.get("function_clause", []):
        name_node, patterns = _function_clause_name_and_patterns(
            source,
            function_node,
        )
        if name_node is None:
            continue

        label = _node_text(source, name_node).strip()
        declaration = add_decl(
            label,
            "function",
            function_node,
            name_node,
        )
        if declaration is None or not _function_is_definition(
            source,
            function_node,
        ):
            continue

        scope = _scope_for_node(
            source,
            declaration,
            function_node,
        )
        for value, pattern_node in patterns:
            leaf = value.split(".")[-1]
            if not leaf or leaf == "_":
                continue
            declaration.pattern_candidates.append(
                PatternCandidate(
                    value=value,
                    span=_span(path, pattern_node),
                    scope=scope,
                )
            )

    declarations = list(declarations_by_key.values())

    for declaration in declarations:
        declaration.symbol = replace(
            declaration.symbol,
            fingerprint=_declaration_fingerprint(
                source,
                declaration,
            ),
        )

    for binding in (
        captures.get("typed_binding", [])
        + captures.get("untyped_binding", [])
    ):
        owner = _smallest_owner(
            declarations,
            binding.start_byte,
            binding.end_byte,
        )
        if owner is None:
            continue
        scope = _scope_for_node(source, owner, binding)

        for leaf, name_node in _binding_names(source, binding):
            key = (scope, leaf)
            owner.binders.setdefault(
                key,
                Symbol.create(
                    label=leaf,
                    kind="binder",
                    module=module,
                    scope=scope,
                    span=_span(path, name_node),
                ),
            )

    for ref in captures.get("reference", []):
        value = _node_text(source, ref).strip()
        if not value:
            continue

        owner = _smallest_owner(
            declarations,
            ref.start_byte,
            ref.end_byte,
        )
        if owner is None:
            continue

        # Function LHS identifiers are handled as the function name, constructor
        # patterns, or clause binders above. They are not ordinary dependencies.
        if _first_ancestor(ref, {"lhs"}) is not None:
            continue

        leaf = value.split(".")[-1]
        if leaf == owner.symbol.label:
            continue

        scope = _scope_for_node(source, owner, ref)
        local = owner.binders.get((scope, leaf))
        if local is not None:
            span = _span(path, ref)
            if (
                span.start_byte == local.span.start_byte
                and span.end_byte == local.span.end_byte
            ):
                continue

        owner.references.append(
            RawReference(
                value=value,
                span=_span(path, ref),
                kind=_reference_kind(source, ref),
                scope=scope,
                prefix_application_head=_prefix_application_head(ref),
            )
        )

    return FileExtraction(
        path=path,
        module=module,
        module_symbol=module_symbol,
        declarations=declarations,
        imports=sorted(set(imports)),
        open_scopes=open_scopes,
        parse_error=bool(tree.root_node.has_error),
    )


def build_semantic_graph(
    files: Iterable[FileExtraction],
) -> SemanticGraph:
    files = list(files)
    graph = SemanticGraph()

    declarations: list[RawDeclaration] = []
    modules: dict[str, Symbol] = {}
    imports_by_module: dict[str, list[str]] = {}
    open_scopes_by_module: dict[str, list[OpenScope]] = {}

    for file in files:
        modules[file.module] = file.module_symbol
        imports_by_module[file.module] = file.imports
        open_scopes_by_module[file.module] = file.open_scopes
        graph.nodes[file.module_symbol.symbol_id] = file.module_symbol
        declarations.extend(file.declarations)
        if file.parse_error:
            graph.parse_error_files.append(file.path)

    by_module_label: dict[tuple[str, str], Symbol] = {}
    by_label: dict[str, list[Symbol]] = {}

    for declaration in declarations:
        symbol = declaration.symbol
        graph.nodes[symbol.symbol_id] = symbol
        by_module_label[(symbol.module, symbol.label)] = symbol
        by_label.setdefault(symbol.label, []).append(symbol)

    # Resolve clause pattern candidates only after the declaration table exists.
    # A known constructor is a pattern dependency; otherwise the bare name is a
    # local binder in that clause scope.
    for declaration in declarations:
        for candidate in declaration.pattern_candidates:
            target = _resolve_reference(
                ref=candidate.value,
                owner_module=declaration.symbol.module,
                by_module_label=by_module_label,
                open_scopes=open_scopes_by_module.get(
                    declaration.symbol.module,
                    [],
                ),
            )
            if target is not None and target.kind == "constructor":
                relation = Relation(
                    source=target.symbol_id,
                    target=declaration.symbol.symbol_id,
                    kind="pattern-matches",
                    evidence=candidate.span,
                )
                graph.edges[relation.relation_id] = relation
                continue

            leaf = candidate.value.split(".")[-1]
            key = (candidate.scope, leaf)
            declaration.binders.setdefault(
                key,
                Symbol.create(
                    label=leaf,
                    kind="binder",
                    module=declaration.symbol.module,
                    scope=candidate.scope,
                    span=candidate.span,
                ),
            )

    for declaration in declarations:
        symbol = declaration.symbol
        module_symbol = modules[symbol.module]

        contains = Relation(
            source=module_symbol.symbol_id,
            target=symbol.symbol_id,
            kind="contains",
            evidence=symbol.span,
        )
        graph.edges[contains.relation_id] = contains

        if (
            declaration.container_label is not None
            and declaration.container_relation is not None
        ):
            container = by_module_label.get(
                (symbol.module, declaration.container_label)
            )
            if container is not None:
                relation = Relation(
                    source=symbol.symbol_id,
                    target=container.symbol_id,
                    kind=declaration.container_relation,
                    evidence=symbol.span,
                )
                graph.edges[relation.relation_id] = relation

        for binder in declaration.binders.values():
            graph.nodes[binder.symbol_id] = binder
            binds = Relation(
                source=binder.symbol_id,
                target=symbol.symbol_id,
                kind="binds",
                evidence=binder.span,
            )
            graph.edges[binds.relation_id] = binds

    for module, imported_modules in imports_by_module.items():
        consumer = modules[module]
        for imported in imported_modules:
            producer = modules.get(imported)
            if producer is None:
                continue
            relation = Relation(
                source=producer.symbol_id,
                target=consumer.symbol_id,
                kind="imports",
                evidence=None,
            )
            graph.edges[relation.relation_id] = relation

    for module, open_scopes in open_scopes_by_module.items():
        consumer = modules[module]
        for scope in open_scopes:
            producer = modules.get(scope.module)
            if producer is None:
                continue
            relation = Relation(
                source=producer.symbol_id,
                target=consumer.symbol_id,
                kind="opens",
                evidence=None,
            )
            graph.edges[relation.relation_id] = relation

    for declaration in declarations:
        owner = declaration.symbol

        for ref in declaration.references:
            leaf = ref.value.split(".")[-1]
            local = declaration.binders.get((ref.scope, leaf))

            if local is not None:
                relation_kind = (
                    "value-flows"
                    if ref.kind == "body-depends"
                    else ref.kind
                )
                relation = Relation(
                    source=local.symbol_id,
                    target=owner.symbol_id,
                    kind=relation_kind,
                    evidence=ref.span,
                )
                graph.edges[relation.relation_id] = relation
                continue

            target = _resolve_reference(
                ref=ref.value,
                owner_module=owner.module,
                by_module_label=by_module_label,
                open_scopes=open_scopes_by_module.get(
                    owner.module,
                    [],
                ),
            )
            if target is None:
                graph.unresolved_references.append(
                    {
                        "owner": owner.symbol_id,
                        "reference": ref.value,
                        "relation_kind": ref.kind,
                        "scope": ref.scope,
                        "evidence": ref.span.__dict__,
                    }
                )
                continue

            relation_kind = ref.kind
            if ref.kind == "body-depends":
                if target.kind == "constructor":
                    relation_kind = "constructs"
                elif (
                    ref.prefix_application_head
                    and target.kind in {
                        "function",
                        "field",
                        "postulate",
                        "theorem",
                    }
                ):
                    relation_kind = "calls"

            relation = Relation(
                source=target.symbol_id,
                target=owner.symbol_id,
                kind=relation_kind,
                evidence=ref.span,
            )
            graph.edges[relation.relation_id] = relation

    return graph


def _resolve_reference(
    *,
    ref: str,
    owner_module: str,
    by_module_label: dict[tuple[str, str], Symbol],
    open_scopes: list[OpenScope],
) -> Symbol | None:
    leaf = ref.split(".")[-1]

    same_module = by_module_label.get((owner_module, leaf))
    if same_module is not None:
        return same_module

    if "." in ref:
        pieces = ref.split(".")
        for i in range(len(pieces) - 1, 0, -1):
            module = ".".join(pieces[:i])
            candidate = by_module_label.get((module, leaf))
            if candidate is not None:
                return candidate
        return None

    candidates: list[Symbol] = []
    for scope in open_scopes:
        target_label = scope.resolve(leaf)
        if target_label is None:
            continue
        candidate = by_module_label.get(
            (scope.module, target_label)
        )
        if candidate is not None:
            candidates.append(candidate)

    unique = {
        candidate.symbol_id: candidate
        for candidate in candidates
    }
    if len(unique) == 1:
        return next(iter(unique.values()))

    # Fail closed: repo-wide name uniqueness is not scope evidence.
    return None


class AgdaLanguageAdapter:
    name = "agda"
    suffixes = (".agda",)

    def extract_file(
        self,
        path: str,
        source: bytes,
    ) -> FileExtraction:
        return extract_file(path, source)

    def build_graph(
        self,
        files: list[FileExtraction],
    ) -> SemanticGraph:
        return build_semantic_graph(files)

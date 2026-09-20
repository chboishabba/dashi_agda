from __future__ import annotations

from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any, Iterable

from tree_sitter import Language, Parser
import tree_sitter_agda

from .model import Relation, SemanticGraph, SourceSpan, Symbol, stable_hash


AGDA_LANGUAGE = Language(tree_sitter_agda.language())

CAPTURE_QUERY = r"""
(module_name) @module_name
(data_name) @data_name
(record_name) @record_name
(field_name) @field_name
(function_name) @function_name
(typed_binding) @typed_binding
(untyped_binding) @untyped_binding
(qid) @reference
(id) @reference
"""


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


def _first_descendant_name(source: bytes, node: Any) -> str | None:
    stack = [node]
    while stack:
        current = stack.pop()
        if current.type in {"qid", "id", "field_name", "data_name", "record_name"}:
            value = _node_text(source, current).strip()
            if value:
                return value
        stack.extend(reversed(current.children))
    return None


def _binding_names(source: bytes, node: Any) -> list[tuple[str, Any]]:
    """Return all syntactic binder names while excluding the bound type.

    For typed bindings, names occur before the first ':' token.  This handles
    multi-binders such as (x y : A) without accidentally turning A into a local
    variable.  Untyped bindings contribute all identifier leaves.
    """

    source_slice = source[node.start_byte : node.end_byte]
    colon = source_slice.find(b":")
    absolute_colon = None if colon < 0 else node.start_byte + colon

    out: list[tuple[str, Any]] = []
    stack = [node]
    seen: set[str] = set()
    while stack:
        current = stack.pop()
        if current.child_count == 0 and current.type in {"qid", "id", "bid"}:
            if absolute_colon is not None and current.start_byte > absolute_colon:
                continue
            value = _node_text(source, current).strip()
            leaf = value.split(".")[-1]
            if leaf and leaf != "_" and leaf not in seen:
                seen.add(leaf)
                out.append((leaf, current))
        stack.extend(reversed(current.children))
    return out


def _declaration_fingerprint(source: bytes, declaration: "RawDeclaration") -> str:
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


def _reference_kind(node: Any) -> str:
    for ancestor in _ancestors(node):
        if ancestor.type == "rhs":
            return "body-depends"
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
class RawDeclaration:
    symbol: Symbol
    owner_ranges: list[tuple[int, int]]
    binders: dict[str, Symbol] = field(default_factory=dict)
    references: list[tuple[str, SourceSpan, str]] = field(default_factory=list)


@dataclass
class FileExtraction:
    path: str
    module: str
    module_symbol: Symbol
    declarations: list[RawDeclaration]
    imports: list[str]
    parse_error: bool


DECLARATION_ANCESTORS = {
    "type_signature",
    "function",
    "data",
    "data_signature",
    "record",
    "record_signature",
}


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

    declarations_by_key: dict[tuple[str, str], RawDeclaration] = {}

    def add_decl(label: str, kind: str, owner: Any, name_node: Any) -> None:
        label = label.strip()
        if not label:
            return
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
            declarations_by_key[key] = RawDeclaration(
                symbol=symbol,
                owner_ranges=[owner_range],
            )
        elif owner_range not in existing.owner_ranges:
            existing.owner_ranges.append(owner_range)

    for node in captures.get("data_name", []):
        owner = _first_ancestor(node, {"data", "data_signature"})
        if owner is not None:
            add_decl(_node_text(source, node), "data", owner, node)

    for node in captures.get("record_name", []):
        owner = _first_ancestor(node, {"record", "record_signature"})
        if owner is not None:
            add_decl(_node_text(source, node), "record", owner, node)

    for node in captures.get("field_name", []):
        owner = _first_ancestor(node, DECLARATION_ANCESTORS | {"fields", "postulate"})
        if owner is None:
            continue
        label = _node_text(source, node)
        if _first_ancestor(node, {"postulate"}) is not None:
            kind = "postulate"
        elif _first_ancestor(node, {"fields"}) is not None:
            kind = "field"
        else:
            kind = "function"
        add_decl(label, kind, owner, node)

    for node in captures.get("function_name", []):
        owner = _first_ancestor(node, {"function"})
        if owner is None:
            continue
        label = _first_descendant_name(source, node)
        if label is not None:
            add_decl(label, "function", owner, node)

    # Same label/kind may have a signature and several equations. Preserve each
    # source range rather than widening one interval across unrelated declarations.
    declarations = list(declarations_by_key.values())

    for declaration in declarations:
        declaration.symbol = replace(
            declaration.symbol,
            fingerprint=_declaration_fingerprint(source, declaration),
        )

    for binding in captures.get("typed_binding", []) + captures.get("untyped_binding", []):
        owner = _smallest_owner(declarations, binding.start_byte, binding.end_byte)
        if owner is None:
            continue
        for leaf, name_node in _binding_names(source, binding):
            owner.binders.setdefault(
                leaf,
                Symbol.create(
                    label=leaf,
                    kind="binder",
                    module=module,
                    scope=owner.symbol.symbol_id,
                    span=_span(path, name_node),
                ),
            )

    for ref in captures.get("reference", []):
        value = _node_text(source, ref).strip()
        if not value:
            continue
        owner = _smallest_owner(declarations, ref.start_byte, ref.end_byte)
        if owner is None:
            continue
        leaf = value.split(".")[-1]
        if leaf == owner.symbol.label:
            continue
        owner.references.append((value, _span(path, ref), _reference_kind(ref)))

    return FileExtraction(
        path=path,
        module=module,
        module_symbol=module_symbol,
        declarations=declarations,
        imports=sorted(set(imports)),
        parse_error=bool(tree.root_node.has_error),
    )


def _smallest_owner(
    declarations: list[RawDeclaration],
    start: int,
    end: int,
) -> RawDeclaration | None:
    matches: list[tuple[int, RawDeclaration]] = []
    for declaration in declarations:
        for owner_start, owner_end in declaration.owner_ranges:
            if owner_start <= start and end <= owner_end:
                matches.append((owner_end - owner_start, declaration))
    if not matches:
        return None
    return min(matches, key=lambda item: item[0])[1]


def build_semantic_graph(files: Iterable[FileExtraction]) -> SemanticGraph:
    files = list(files)
    graph = SemanticGraph()

    declarations: list[RawDeclaration] = []
    modules: dict[str, Symbol] = {}
    imports_by_module: dict[str, list[str]] = {}

    for file in files:
        modules[file.module] = file.module_symbol
        imports_by_module[file.module] = file.imports
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

        module_symbol = modules[symbol.module]
        contains = Relation(
            source=module_symbol.symbol_id,
            target=symbol.symbol_id,
            kind="contains",
            evidence=symbol.span,
        )
        graph.edges[contains.relation_id] = contains

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

    for declaration in declarations:
        owner = declaration.symbol
        for ref, evidence, relation_kind in declaration.references:
            leaf = ref.split(".")[-1]

            local = declaration.binders.get(leaf)
            if local is not None:
                relation = Relation(
                    source=local.symbol_id,
                    target=owner.symbol_id,
                    kind=relation_kind,
                    evidence=evidence,
                )
                graph.edges[relation.relation_id] = relation
                continue

            target = _resolve_reference(
                ref=ref,
                owner_module=owner.module,
                by_module_label=by_module_label,
                by_label=by_label,
            )
            if target is None:
                graph.unresolved_references.append(
                    {
                        "owner": owner.symbol_id,
                        "reference": ref,
                        "relation_kind": relation_kind,
                        "evidence": evidence.__dict__,
                    }
                )
                continue

            relation = Relation(
                source=target.symbol_id,
                target=owner.symbol_id,
                kind=relation_kind,
                evidence=evidence,
            )
            graph.edges[relation.relation_id] = relation

    return graph


def _resolve_reference(
    *,
    ref: str,
    owner_module: str,
    by_module_label: dict[tuple[str, str], Symbol],
    by_label: dict[str, list[Symbol]],
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

    candidates = by_label.get(leaf, [])
    if len(candidates) == 1:
        return candidates[0]

    return None

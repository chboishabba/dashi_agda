from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

from tree_sitter import Language, Parser
import tree_sitter_agda

from .model import Relation, SemanticGraph, SourceSpan, Symbol


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


@dataclass
class RawDeclaration:
    symbol: Symbol
    owner_start: int
    owner_end: int
    local_names: set[str] = field(default_factory=set)
    references: list[tuple[str, SourceSpan]] = field(default_factory=list)


@dataclass
class FileExtraction:
    path: str
    module: str
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
    for node in captures.get("module_name", []):
        ancestor = _first_ancestor(node, {"module"})
        if ancestor is not None:
            value = _node_text(source, node).strip()
            if value:
                module = value
                break

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
            span=_span(path, name_node),
        )
        key = (label, kind)
        existing = declarations_by_key.get(key)
        raw = RawDeclaration(
            symbol=symbol,
            owner_start=owner.start_byte,
            owner_end=owner.end_byte,
        )
        if existing is None:
            declarations_by_key[key] = raw
        else:
            existing.owner_start = min(existing.owner_start, raw.owner_start)
            existing.owner_end = max(existing.owner_end, raw.owner_end)

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
            kind = "declaration"
        add_decl(label, kind, owner, node)

    for node in captures.get("function_name", []):
        owner = _first_ancestor(node, {"function"})
        if owner is None:
            continue
        label = _first_descendant_name(source, node)
        if label is not None:
            add_decl(label, "function", owner, node)

    declarations = list(declarations_by_key.values())

    by_label: dict[str, RawDeclaration] = {}
    for decl in declarations:
        prior = by_label.get(decl.symbol.label)
        if prior is None:
            by_label[decl.symbol.label] = decl
            continue
        if decl.symbol.kind == "function" and prior.symbol.kind == "declaration":
            decl.owner_start = min(decl.owner_start, prior.owner_start)
            decl.owner_end = max(decl.owner_end, prior.owner_end)
            by_label[decl.symbol.label] = decl
        else:
            prior.owner_start = min(prior.owner_start, decl.owner_start)
            prior.owner_end = max(prior.owner_end, decl.owner_end)

    declarations = list(by_label.values())

    binding_nodes = captures.get("typed_binding", []) + captures.get("untyped_binding", [])
    for binding in binding_nodes:
        name = _first_descendant_name(source, binding)
        if name is None:
            continue
        owner = _smallest_owner(declarations, binding.start_byte, binding.end_byte)
        if owner is not None:
            owner.local_names.add(name.split(".")[-1])

    for ref in captures.get("reference", []):
        value = _node_text(source, ref).strip()
        if not value:
            continue
        owner = _smallest_owner(declarations, ref.start_byte, ref.end_byte)
        if owner is None:
            continue
        leaf = value.split(".")[-1]
        if leaf == owner.symbol.label or leaf in owner.local_names:
            continue
        owner.references.append((value, _span(path, ref)))

    return FileExtraction(
        path=path,
        module=module,
        declarations=declarations,
        imports=sorted(set(imports)),
        parse_error=bool(tree.root_node.has_error),
    )


def _smallest_owner(
    declarations: list[RawDeclaration],
    start: int,
    end: int,
) -> RawDeclaration | None:
    candidates = [
        d
        for d in declarations
        if d.owner_start <= start and end <= d.owner_end
    ]
    if not candidates:
        return None
    return min(candidates, key=lambda d: d.owner_end - d.owner_start)


def build_semantic_graph(files: Iterable[FileExtraction]) -> SemanticGraph:
    files = list(files)
    graph = SemanticGraph()

    declarations: list[RawDeclaration] = []
    for file in files:
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

    for declaration in declarations:
        owner = declaration.symbol
        for ref, evidence in declaration.references:
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
                        "evidence": evidence.__dict__,
                    }
                )
                continue
            relation = Relation(
                source=target.symbol_id,
                target=owner.symbol_id,
                kind="depends",
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

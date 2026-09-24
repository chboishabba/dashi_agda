from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple


def node_text(source_bytes: bytes, node) -> str:
    return source_bytes[node.start_byte:node.end_byte].decode("utf-8", "replace")


def descendants(node, *types: str) -> Iterator:
    wanted = set(types)
    stack = [node]
    while stack:
        current = stack.pop()
        if not wanted or current.type in wanted:
            yield current
        stack.extend(reversed(current.named_children))


def first_descendant(node, *types: str):
    return next(descendants(node, *types), None)


def direct_named(node, node_type: str) -> List:
    return [child for child in node.named_children if child.type == node_type]


def line_of(node) -> int:
    return node.start_point[0] + 1


@dataclass(frozen=True)
class ImportDirective:
    kind: str
    names: Tuple[str, ...] = ()
    renamings: Tuple[Tuple[str, str], ...] = ()


@dataclass(frozen=True)
class ImportDecl:
    module: str
    alias: str
    line: int
    opened: bool = False
    public: bool = False
    directives: Tuple[ImportDirective, ...] = ()
    node_type: str = "import"


@dataclass(frozen=True)
class OpenDecl:
    target: str
    line: int
    public: bool = False
    directives: Tuple[ImportDirective, ...] = ()


@dataclass(frozen=True)
class AstField:
    name: str
    type_text: str
    line: int
    type_node: object | None = None


@dataclass
class AstRecord:
    name: str
    line: int
    fields: Dict[str, AstField] = field(default_factory=dict)
    field_occurrences: List[AstField] = field(default_factory=list)
    constructor: Optional[str] = None
    node: object | None = None


@dataclass(frozen=True)
class AstConstructor:
    name: str
    type_text: str
    line: int
    datatype: str
    type_node: object | None = None


@dataclass
class AstData:
    name: str
    line: int
    constructors: Dict[str, AstConstructor] = field(default_factory=dict)
    constructor_occurrences: List[AstConstructor] = field(default_factory=list)
    node: object | None = None


@dataclass(frozen=True)
class AstSignature:
    names: Tuple[str, ...]
    type_text: str
    line: int
    type_node: object | None
    node: object


@dataclass(frozen=True)
class AstClause:
    name: str
    line: int
    lhs_node: object
    rhs_node: object | None
    lhs_text: str
    rhs_text: str
    node: object


@dataclass
class AstIndex:
    path: Path
    source: str
    source_bytes: bytes
    tree: object
    module_name: str
    imports: List[ImportDecl] = field(default_factory=list)
    opens: List[OpenDecl] = field(default_factory=list)
    records: Dict[str, AstRecord] = field(default_factory=dict)
    data: Dict[str, AstData] = field(default_factory=dict)
    signatures: Dict[str, AstSignature] = field(default_factory=dict)
    signature_occurrences: Dict[str, List[AstSignature]] = field(default_factory=dict)
    clauses: Dict[str, List[AstClause]] = field(default_factory=dict)
    pragmas: List[object] = field(default_factory=list)
    infix_nodes: List[object] = field(default_factory=list)
    syntax_nodes: List[object] = field(default_factory=list)
    postulate_nodes: List[object] = field(default_factory=list)
    pattern_nodes: List[object] = field(default_factory=list)

    @property
    def import_map(self) -> Dict[str, str]:
        return {item.alias: item.module for item in self.imports}

    @property
    def opened_namespaces(self) -> Set[str]:
        return {item.target.split(".")[-1] for item in self.opens}


def _leaf_tokens(source_bytes: bytes, node) -> List[str]:
    out: List[str] = []
    stack = [node]
    while stack:
        current = stack.pop()
        if current.child_count == 0:
            text = node_text(source_bytes, current).strip()
            if text:
                out.append(text)
            continue
        stack.extend(reversed(current.children))
    return out


def _name_from_node(source_bytes: bytes, node) -> Optional[str]:
    if node is None:
        return None
    text = node_text(source_bytes, node).strip()
    return text or None


def _module_name_from_tree(source_bytes: bytes, root, path: Path, root_path: Path) -> str:
    # The outermost Agda module is represented by a module node.
    for child in root.named_children:
        if child.type != "module":
            continue
        name_node = next((x for x in child.named_children if x.type == "module_name"), None)
        name = _name_from_node(source_bytes, name_node)
        if name and name != "_":
            return name
    try:
        rel = path.resolve().relative_to(root_path.resolve())
        return ".".join(rel.with_suffix("").parts)
    except ValueError:
        return path.stem


def _import_directive(source_bytes: bytes, node) -> ImportDirective:
    tokens = _leaf_tokens(source_bytes, node)
    kind = tokens[0] if tokens else ""
    if kind == "renaming":
        pairs: List[Tuple[str, str]] = []
        for ren in descendants(node, "renaming"):
            ids = [node_text(source_bytes, x).strip() for x in ren.named_children if x.type == "id"]
            if len(ids) >= 2:
                pairs.append((ids[0], ids[-1]))
        return ImportDirective(kind=kind, renamings=tuple(pairs))
    names = tuple(
        node_text(source_bytes, x).strip()
        for x in descendants(node, "id")
        if node_text(source_bytes, x).strip()
    )
    return ImportDirective(kind=kind, names=names)


def _directives(source_bytes: bytes, node) -> Tuple[ImportDirective, ...]:
    return tuple(_import_directive(source_bytes, child)
                 for child in node.named_children if child.type == "import_directive")


def _parse_import_node(source_bytes: bytes, node, *, opened: bool = False) -> Optional[ImportDecl]:
    module_node = first_descendant(node, "module_name")
    module = _name_from_node(source_bytes, module_node)
    if not module:
        return None
    tokens = _leaf_tokens(source_bytes, node)
    alias = module.split(".")[-1]
    if "as" in tokens:
        i = tokens.index("as")
        if i + 1 < len(tokens):
            alias = tokens[i + 1]
    directives = _directives(source_bytes, node)
    public = any(d.kind == "public" for d in directives)
    return ImportDecl(
        module=module,
        alias=alias,
        line=line_of(node),
        opened=opened,
        public=public,
        directives=directives,
        node_type=node.type,
    )


def _parse_open_node(source_bytes: bytes, node) -> Tuple[Optional[ImportDecl], Optional[OpenDecl]]:
    import_child = next((x for x in node.named_children if x.type == "import"), None)
    directives = _directives(source_bytes, node)
    public = any(d.kind == "public" for d in directives)
    if import_child is not None:
        imp = _parse_import_node(source_bytes, import_child, opened=True)
        if imp is not None:
            # Directives belong to the outer open node in the grammar.
            imp = ImportDecl(
                imp.module, imp.alias, line_of(node), True, public, directives, "open_import"
            )
            return imp, OpenDecl(imp.alias, line_of(node), public, directives)
    module_node = next((x for x in node.named_children if x.type == "module_name"), None)
    target = _name_from_node(source_bytes, module_node)
    if target:
        return None, OpenDecl(target, line_of(node), public, directives)
    return None, None


def _signature_parts(source_bytes: bytes, node) -> Tuple[Tuple[str, ...], Optional[object]]:
    names = tuple(
        node_text(source_bytes, child).strip()
        for child in descendants(node, "field_name")
        if node_text(source_bytes, child).strip()
    )
    if not names:
        # Function declaration signatures expose function_name rather than field_name.
        fname = first_descendant(node, "function_name")
        if fname is not None:
            q = first_descendant(fname, "qid", "id")
            name = _name_from_node(source_bytes, q or fname)
            if name:
                # A declaration LHS should be one name; avoid swallowing its args.
                names = (name.split()[0],)
    exprs = list(descendants(node, "expr"))
    type_node = exprs[-1] if exprs else None
    return names, type_node


def _record_from_node(source_bytes: bytes, node) -> Optional[AstRecord]:
    name_node = first_descendant(node, "record_name")
    name = _name_from_node(source_bytes, name_node)
    if not name:
        return None
    rec = AstRecord(name=name, line=line_of(node), node=node)
    ctor = first_descendant(node, "record_constructor")
    if ctor is not None:
        ident = first_descendant(ctor, "id")
        rec.constructor = _name_from_node(source_bytes, ident)
    # Only signatures nested under a 'fields' declaration are projections.
    for fields_node in descendants(node, "fields"):
        for sig in descendants(fields_node, "signature"):
            names, type_node = _signature_parts(source_bytes, sig)
            if type_node is None:
                continue
            typ = node_text(source_bytes, type_node).strip()
            for field_name in names:
                item = AstField(field_name, typ, line_of(sig), type_node)
                rec.field_occurrences.append(item)
                rec.fields[field_name] = item
    return rec


def _function_signature(source_bytes: bytes, node) -> Optional[AstSignature]:
    lhs = next((x for x in node.named_children if x.type == "lhs"), None)
    rhs = next((x for x in node.named_children if x.type == "rhs"), None)
    if lhs is None or rhs is None:
        return None
    fname = first_descendant(lhs, "function_name")
    if fname is None:
        return None
    name_node = first_descendant(fname, "qid", "id")
    name = _name_from_node(source_bytes, name_node or fname)
    expr = first_descendant(rhs, "expr")
    if not name or expr is None:
        return None
    # A declaration's RHS begins with ':'; definitions have no function_name.
    return AstSignature((name,), node_text(source_bytes, expr).strip(), line_of(node), expr, node)


def _function_clause(source_bytes: bytes, node) -> Optional[AstClause]:
    lhs = next((x for x in node.named_children if x.type == "lhs"), None)
    rhs = next((x for x in node.named_children if x.type == "rhs"), None)
    if lhs is None:
        return None
    if first_descendant(lhs, "function_name") is not None:
        return None
    # The first qualified/id atom on a definition LHS is the defined function.
    name_node = first_descendant(lhs, "qid", "id")
    name = _name_from_node(source_bytes, name_node)
    if not name:
        return None
    rhs_expr = first_descendant(rhs, "expr") if rhs is not None else None
    return AstClause(
        name=name,
        line=line_of(node),
        lhs_node=lhs,
        rhs_node=rhs_expr,
        lhs_text=node_text(source_bytes, lhs).strip(),
        rhs_text=node_text(source_bytes, rhs_expr).strip() if rhs_expr is not None else "",
        node=node,
    )


def _data_from_node(source_bytes: bytes, node) -> Optional[AstData]:
    name_node = first_descendant(node, "data_name")
    name = _name_from_node(source_bytes, name_node)
    if not name:
        return None
    decl = AstData(name=name, line=line_of(node), node=node)
    # Constructor declarations are function signatures nested directly in the
    # data declaration's where block. Nested records/functions are excluded by
    # accepting signatures whose closest data ancestor is this node.
    for fn in descendants(node, "function"):
        parent = fn.parent
        closest_data = None
        while parent is not None and parent is not node.parent:
            if parent.type == "data":
                closest_data = parent
                break
            parent = parent.parent
        if closest_data is not node:
            continue
        sig = _function_signature(source_bytes, fn)
        if sig is None:
            continue
        cname = sig.names[0]
        ctor = AstConstructor(cname, sig.type_text, sig.line, name, sig.type_node)
        decl.constructor_occurrences.append(ctor)
        decl.constructors[cname] = ctor
    return decl


def build_ast_index(parser, path: Path, root_path: Path, source: str) -> AstIndex:
    source_bytes = source.encode("utf-8")
    tree = parser.parse(source_bytes)
    root = tree.root_node
    index = AstIndex(
        path=path,
        source=source,
        source_bytes=source_bytes,
        tree=tree,
        module_name=_module_name_from_tree(source_bytes, root, path, root_path),
    )

    # Walk declarations once. Nested declarations are retained for later scope
    # work, while summaries below deliberately use only outer/module-level
    # function declarations unless they belong to data/record bodies.
    for node in descendants(root):
        if node.type == "open":
            imp, opened = _parse_open_node(source_bytes, node)
            if imp is not None:
                index.imports.append(imp)
            if opened is not None:
                index.opens.append(opened)
        elif node.type == "import" and (node.parent is None or node.parent.type != "open"):
            imp = _parse_import_node(source_bytes, node)
            if imp is not None:
                index.imports.append(imp)
        elif node.type == "record":
            rec = _record_from_node(source_bytes, node)
            if rec is not None:
                index.records[rec.name] = rec
        elif node.type == "data":
            data = _data_from_node(source_bytes, node)
            if data is not None:
                index.data[data.name] = data
        elif node.type == "function":
            # Exclude constructor/record-local function declarations from the
            # module-level signature/definition tables.
            parent = node.parent
            nested_owner = None
            while parent is not None and parent is not root:
                if parent.type in {"data", "record", "fields"}:
                    nested_owner = parent.type
                    break
                parent = parent.parent
            if nested_owner is not None:
                continue
            sig = _function_signature(source_bytes, node)
            if sig is not None:
                for name in sig.names:
                    index.signature_occurrences.setdefault(name, []).append(sig)
                    index.signatures[name] = sig
                continue
            clause = _function_clause(source_bytes, node)
            if clause is not None:
                index.clauses.setdefault(clause.name, []).append(clause)
        elif node.type == "pragma":
            index.pragmas.append(node)
        elif node.type == "infix":
            index.infix_nodes.append(node)
        elif node.type == "syntax":
            index.syntax_nodes.append(node)
        elif node.type == "postulate":
            index.postulate_nodes.append(node)
        elif node.type == "pattern":
            index.pattern_nodes.append(node)
    return index

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
    constructor_node_spans: Set[Tuple[int, int]] = field(default_factory=set)
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


@dataclass(frozen=True)
class AstFieldAssignment:
    name: str
    expr_text: str
    line: int
    expr_node: object | None
    node: object


@dataclass
class AstRecordExpression:
    line: int
    node: object
    owner_function: Optional[str]
    parent_field: Optional[str] = None
    parent_record_start: Optional[int] = None
    assignments: List[AstFieldAssignment] = field(default_factory=list)


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
    module_macro_nodes: List[object] = field(default_factory=list)
    mutual_nodes: List[object] = field(default_factory=list)
    where_nodes: List[object] = field(default_factory=list)
    record_expressions: List[AstRecordExpression] = field(default_factory=list)
    nested_modules: Set[str] = field(default_factory=set)

    @property
    def import_map(self) -> Dict[str, str]:
        return {item.alias: item.module for item in self.imports}

    @property
    def opened_namespaces(self) -> Set[str]:
        return {item.target.split(".")[-1] for item in self.opens}



@dataclass(frozen=True)
class AstToken:
    text: str
    node_type: str
    start_byte: int
    end_byte: int
    line: int
    column: int
    named: bool


def leaf_tokens(source_bytes: bytes, node) -> List[AstToken]:
    """Return ordered concrete leaf tokens under NODE.

    This is deliberately syntax-tree tokenization, not source-text parsing:
    anonymous grammar tokens such as arrows/braces and named qid/id leaves are
    preserved with exact source ranges.
    """
    out: List[AstToken] = []
    stack = [node]
    while stack:
        current = stack.pop()
        if current.child_count == 0:
            text = node_text(source_bytes, current)
            if text:
                out.append(
                    AstToken(
                        text=text,
                        node_type=current.type,
                        start_byte=current.start_byte,
                        end_byte=current.end_byte,
                        line=current.start_point[0] + 1,
                        column=current.start_point[1] + 1,
                        named=current.is_named,
                    )
                )
            continue
        stack.extend(reversed(current.children))
    out.sort(key=lambda token: token.start_byte)
    return out


def significant_tokens(source_bytes: bytes, node) -> List[AstToken]:
    return [token for token in leaf_tokens(source_bytes, node) if token.text.strip()]


def qualified_name_tokens(source_bytes: bytes, node) -> List[AstToken]:
    return [
        token
        for token in significant_tokens(source_bytes, node)
        if token.node_type in {"qid", "id", "field_name", "function_name"}
    ]


@dataclass(frozen=True)
class AstBinder:
    name: str
    type_text: str
    visibility: str
    line: int
    type_start_byte: int
    type_end_byte: int


def typed_binders(source_bytes: bytes, expr_node) -> List[AstBinder]:
    """Extract explicit/implicit/instance typed binders from an expr token tree.

    Agda's grammar intentionally hides several binding helper rules. Walking
    concrete tree tokens keeps delimiter/colon structure without reparsing the
    original source with regex.
    """
    tokens = significant_tokens(source_bytes, expr_node)
    out: List[AstBinder] = []
    open_to_close = {"(": ")", "{": "}", "{{": "}}", "⦃": "⦄"}
    visibility = {"(": "explicit", "{": "implicit", "{{": "instance", "⦃": "instance"}
    i = 0
    while i < len(tokens):
        opener = tokens[i].text
        if opener not in open_to_close:
            i += 1
            continue
        closer = open_to_close[opener]
        depth = 1
        j = i + 1
        colon = None
        while j < len(tokens):
            text = tokens[j].text
            if text == opener:
                depth += 1
            elif text == closer:
                depth -= 1
                if depth == 0:
                    break
            elif text == ":" and depth == 1 and colon is None:
                colon = j
            j += 1
        if j >= len(tokens):
            i += 1
            continue
        if colon is not None and colon > i + 1 and colon + 1 < j:
            names = [
                token for token in tokens[i + 1:colon]
                if token.node_type in {"id", "bid", "field_name", "qid"}
                and token.text not in {".", ".."}
            ]
            type_tokens = tokens[colon + 1:j]
            if names and type_tokens:
                start = type_tokens[0].start_byte
                end = type_tokens[-1].end_byte
                typ = source_bytes[start:end].decode("utf-8", "replace").strip()
                for name in names:
                    if name.text != "_":
                        out.append(
                            AstBinder(
                                name=name.text,
                                type_text=typ,
                                visibility=visibility[opener],
                                line=name.line,
                                type_start_byte=start,
                                type_end_byte=end,
                            )
                        )
        i = j + 1
    return out


@dataclass(frozen=True)
class AstArgument:
    text: str
    visibility: str
    node: object


@dataclass(frozen=True)
class AstApplication:
    head: str
    head_node: object
    args: Tuple[AstArgument, ...]
    node: object

    @property
    def explicit_args(self) -> Tuple[AstArgument, ...]:
        return tuple(arg for arg in self.args if arg.visibility == "explicit")


def _transparent_application_children(node) -> List:
    """Return the outer application atoms exposed through hidden grammar rules.

    Hidden tree-sitter rules are flattened. We recurse only through known
    transparent wrappers and stop at semantic constructs (lambda/let/do/etc.).
    """
    semantic_stops = {
        "lambda", "let", "do", "forall", "record_assignments",
        "field_assignments", "typed_binding", "where",
    }
    atoms = [child for child in node.named_children if child.type == "atom"]
    if atoms:
        return atoms
    result = []
    for child in node.named_children:
        if child.type in semantic_stops:
            continue
        if child.type in {"expr", "lhs", "rhs", "function_name", "stmt"}:
            nested = _transparent_application_children(child)
            if nested:
                result.extend(nested)
    return result


def _argument_visibility(source_bytes: bytes, atom) -> str:
    tokens = significant_tokens(source_bytes, atom)
    if not tokens:
        return "explicit"
    if tokens[0].text in {"{{", "⦃"}:
        return "instance"
    if tokens[0].text == "{":
        return "implicit"
    return "explicit"


def application_view(source_bytes: bytes, node) -> Optional[AstApplication]:
    atoms = _transparent_application_children(node)
    if not atoms:
        # A single qid/id expression is a zero-argument application head.
        names = [
            token for token in significant_tokens(source_bytes, node)
            if token.node_type in {"qid", "id"}
        ]
        if len(names) == 1:
            return AstApplication(names[0].text, names[0], (), node)
        return None

    head_atom = atoms[0]
    head_names = [
        token for token in significant_tokens(source_bytes, head_atom)
        if token.node_type in {"qid", "id"}
    ]
    if not head_names:
        return None
    head_token = head_names[0]
    args = tuple(
        AstArgument(
            text=node_text(source_bytes, atom).strip(),
            visibility=_argument_visibility(source_bytes, atom),
            node=atom,
        )
        for atom in atoms[1:]
    )
    return AstApplication(head_token.text, head_atom, args, node)


def applications(source_bytes: bytes, node) -> Iterator[AstApplication]:
    """Yield maximal application views under NODE without duplicate nesting."""
    stack = [node]
    while stack:
        current = stack.pop()
        view = application_view(source_bytes, current)
        if view is not None and view.args:
            yield view
            # Its atoms may contain nested applications in parenthesized args.
            for arg in reversed(view.args):
                stack.extend(reversed(arg.node.named_children))
            continue
        stack.extend(reversed(current.named_children))


def clause_explicit_argument_count(source_bytes: bytes, lhs_node) -> Optional[int]:
    view = application_view(source_bytes, lhs_node)
    if view is None:
        return None
    return len(view.explicit_args)


def direct_binding_parameters(source_bytes: bytes, declaration_node) -> List[AstBinder]:
    """Return only parameters syntactically attached to a declaration header."""
    out: List[AstBinder] = []
    for child in declaration_node.named_children:
        if child.type not in {"typed_binding", "untyped_binding"}:
            continue
        tokens = significant_tokens(source_bytes, child)
        if not tokens:
            continue
        visibility = "explicit"
        if tokens[0].text in {"{{", "⦃"}:
            visibility = "instance"
        elif tokens[0].text == "{":
            visibility = "implicit"

        colon_index = next((i for i, token in enumerate(tokens) if token.text == ":"), None)
        name_tokens = tokens[:colon_index] if colon_index is not None else tokens
        type_tokens = tokens[colon_index + 1:] if colon_index is not None else []
        names = [
            token for token in name_tokens
            if token.node_type in {"id", "bid", "field_name", "qid"}
            and token.text != "_"
        ]
        type_text = ""
        start = end = child.start_byte
        if type_tokens:
            start = type_tokens[0].start_byte
            end = type_tokens[-1].end_byte
            type_text = source_bytes[start:end].decode("utf-8", "replace").strip()
        for name in names:
            out.append(
                AstBinder(
                    name=name.text,
                    type_text=type_text,
                    visibility=visibility,
                    line=name.line,
                    type_start_byte=start,
                    type_end_byte=end,
                )
            )
    return out


def explicit_declaration_parameter_count(source_bytes: bytes, declaration_node) -> int:
    return sum(
        1 for binder in direct_binding_parameters(source_bytes, declaration_node)
        if binder.visibility == "explicit"
    )


def module_application_target_and_args(source_bytes: bytes, macro_node):
    app = first_descendant(macro_node, "module_application")
    if app is None:
        return None, ()
    module_names = [child for child in descendants(app, "module_name")]
    if not module_names:
        return None, ()
    target = node_text(source_bytes, module_names[0]).strip()
    atoms = [child for child in app.named_children if child.type == "atom"]
    args = tuple(
        AstArgument(
            text=node_text(source_bytes, atom).strip(),
            visibility=_argument_visibility(source_bytes, atom),
            node=atom,
        )
        for atom in atoms
    )
    return target, args

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



_RESERVED_FUNCTION_NAMES = {"where", "as", "constructor", "field", "record", "data", "open", "import", "module"}

def _is_layout_divider_name(name: str) -> bool:
    stripped = name.strip()
    return bool(stripped) and all(ch in "-=_~" for ch in stripped)

def _valid_function_name(name: Optional[str]) -> bool:
    return bool(name) and name not in _RESERVED_FUNCTION_NAMES and not _is_layout_divider_name(name)

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

    # tree-sitter-agda may emit the record header/signature separately from
    # adjacent constructor/fields nodes. Treat only those immediate structural
    # siblings as part of the same record; stop before unrelated declarations.
    related = [node]
    sibling = node.next_named_sibling
    while sibling is not None:
        tokens = [token.text for token in significant_tokens(source_bytes, sibling)]

        is_where_wrapper = (
            sibling.type == "function"
            and tokens
            and tokens[0] == "where"
        )
        if sibling.start_point[1] <= node.start_point[1] and not is_where_wrapper:
            break

        if sibling.type in {"fields", "record_constructor"}:
            related.append(sibling)
            sibling = sibling.next_named_sibling
            continue

        if sibling.type == "ERROR":
            if tokens[:1] in (["constructor"], ["field"], ["where"]):
                related.append(sibling)
                sibling = sibling.next_named_sibling
                continue

        if sibling.type == "function" and tokens:
            if tokens[0] == "where":
                related.append(sibling)
                sibling = sibling.next_named_sibling
                continue
            if tokens[0] == "constructor":
                related.append(sibling)
                if len(tokens) >= 2 and rec.constructor is None:
                    rec.constructor = tokens[1]
                sibling = sibling.next_named_sibling
                continue
        break

    for owner in related:
        ctor = first_descendant(owner, "record_constructor")
        if ctor is not None and rec.constructor is None:
            ident = first_descendant(ctor, "id")
            rec.constructor = _name_from_node(source_bytes, ident)
        elif rec.constructor is None and owner.type in {"function", "ERROR"}:
            tokens = [token.text for token in significant_tokens(source_bytes, owner)]
            if len(tokens) >= 2 and tokens[0] == "constructor":
                rec.constructor = tokens[1]

        for fields_node in descendants(owner, "fields"):
            for sig in descendants(fields_node, "signature"):
                names, type_node = _signature_parts(source_bytes, sig)
                if type_node is None:
                    continue
                typ = node_text(source_bytes, type_node).strip()
                for field_name in names:
                    if field_name in _RESERVED_FUNCTION_NAMES:
                        continue
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
    if not _valid_function_name(name) or expr is None:
        return None
    # A declaration's RHS begins with ':'; definitions have no function_name.
    return AstSignature((name,), node_text(source_bytes, expr).strip(), line_of(node), expr, node)


def _function_clause(
    source_bytes: bytes,
    node,
    *,
    continuation_owner: Optional[str] = None,
) -> Optional[AstClause]:
    lhs = next((x for x in node.named_children if x.type == "lhs"), None)
    rhs = next((x for x in node.named_children if x.type == "rhs"), None)
    if lhs is None:
        return None
    if first_descendant(lhs, "function_name") is not None:
        return None

    lhs_tokens = significant_tokens(source_bytes, lhs)
    is_ellipsis = bool(lhs_tokens and lhs_tokens[0].text in {"...", "…"})
    if is_ellipsis:
        name = continuation_owner
    else:
        # Ordinary definition clauses carry the defined function as the first
        # qualified/id atom. Ellipsis with-clauses deliberately do not.
        name_node = first_descendant(lhs, "qid", "id")
        name = _name_from_node(source_bytes, name_node)

    if not _valid_function_name(name):
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

    def add_constructor(fn) -> bool:
        sig = _function_signature(source_bytes, fn)
        if sig is None:
            return False
        cname = sig.names[0]
        ctor = AstConstructor(cname, sig.type_text, sig.line, name, sig.type_node)
        decl.constructor_occurrences.append(ctor)
        decl.constructors[cname] = ctor
        decl.constructor_node_spans.add((fn.start_byte, fn.end_byte))
        return True

    # Normal data declarations contain constructor functions as descendants.
    for fn in descendants(node, "function"):
        parent = fn.parent
        closest_data = None
        while parent is not None and parent != node.parent:
            if parent.type == "data":
                closest_data = parent
                break
            parent = parent.parent
        if closest_data == node:
            add_constructor(fn)

    # tree-sitter-agda can emit a data signature followed by indented
    # function siblings for constructors. Recover only that indented run.
    if node.type == "data_signature":
        sibling = node.next_named_sibling
        while sibling is not None:
            if sibling.start_point[1] <= node.start_point[1]:
                break
            tokens = [token.text for token in significant_tokens(source_bytes, sibling)]
            if sibling.type == "function":
                if tokens and tokens[0] == "where":
                    sibling = sibling.next_named_sibling
                    continue
                if add_constructor(sibling):
                    sibling = sibling.next_named_sibling
                    continue
            break

    return decl


def _record_expression_from_node(source_bytes: bytes, node) -> AstRecordExpression:
    owner_function = None
    parent_field = None
    parent_record_start = None

    parent = node.parent
    while parent is not None:
        if parent.type in {"field_assignment", "module_assignment"} and parent_field is None:
            name_node = first_descendant(parent, "field_name")
            if name_node is None:
                name_node = first_descendant(parent, "module_name")
            parent_field = _name_from_node(source_bytes, name_node)
            ancestor = parent.parent
            while ancestor is not None:
                if ancestor.type in {"record_assignments", "field_assignments"}:
                    parent_record_start = ancestor.start_byte
                    break
                ancestor = ancestor.parent
        if parent.type == "function":
            clause = _function_clause(source_bytes, parent)
            signature = _function_signature(source_bytes, parent)
            if clause is not None:
                owner_function = clause.name
            elif signature is not None:
                owner_function = signature.names[0]
            break
        parent = parent.parent

    expr = AstRecordExpression(
        line=line_of(node),
        node=node,
        owner_function=owner_function,
        parent_field=parent_field,
        parent_record_start=parent_record_start,
    )
    raw_assignments = [
        *descendants(node, "field_assignment"),
        *descendants(node, "module_assignment"),
    ]
    raw_assignments.sort(key=lambda item: item.start_byte)

    for assignment in raw_assignments:
        ancestor = assignment.parent
        closest = None
        while ancestor is not None and ancestor != node.parent:
            if ancestor.type in {"record_assignments", "field_assignments"}:
                closest = ancestor
                break
            ancestor = ancestor.parent
        if closest != node:
            continue

        name_node = first_descendant(assignment, "field_name")
        if name_node is None:
            name_node = first_descendant(assignment, "module_name")

        rhs_node = first_descendant(assignment, "expr")
        if rhs_node is None and assignment.type == "module_assignment" and assignment.named_children:
            rhs_node = assignment.named_children[-1]

        name = _name_from_node(source_bytes, name_node)
        if not name:
            continue
        expr.assignments.append(
            AstFieldAssignment(
                name=name,
                expr_text=node_text(source_bytes, rhs_node).strip() if rhs_node is not None else "",
                line=line_of(assignment),
                expr_node=rhs_node,
                node=assignment,
            )
        )
    return expr


def _recover_import_from_error(source_bytes: bytes, node) -> Optional[ImportDecl]:
    """Recover the known tree-sitter-agda import-alias grammar gap.

    Recovery consumes the ERROR node's concrete tree leaves rather than
    reparsing source text. If the token sequence is not unambiguous, return
    None and let TSAGDA000 report the grammar/error node.
    """
    tokens = significant_tokens(source_bytes, node)
    texts = [token.text for token in tokens]
    if "import" not in texts:
        return None
    import_index = texts.index("import")
    module_token = next(
        (
            token
            for token in tokens[import_index + 1:]
            if token.node_type in {"module_name", "qid", "id"}
            and token.text not in {"as", "public", "using", "hiding", "renaming"}
        ),
        None,
    )
    if module_token is None:
        return None
    module = module_token.text
    alias = module.split(".")[-1]

    sibling = node.next_named_sibling
    sibling_all = significant_tokens(source_bytes, sibling) if sibling is not None else []
    sibling_texts = [token.text for token in sibling_all]

    if "as" in texts:
        alias_index = texts.index("as")
        if alias_index + 1 < len(tokens):
            alias = tokens[alias_index + 1].text
        else:
            if "as" in sibling_texts:
                as_index = sibling_texts.index("as")
                candidates = [
                    token.text
                    for token in sibling_all[as_index + 1:]
                    if token.node_type in {"qid", "id"}
                    and _valid_function_name(token.text)
                ]
            else:
                candidates = [
                    token.text
                    for token in sibling_all
                    if token.node_type in {"qid", "id"}
                    and _valid_function_name(token.text)
                ]
            if len(candidates) == 1:
                alias = candidates[0]
    elif "as" in sibling_texts:
        as_index = sibling_texts.index("as")
        candidates = [
            token.text
            for token in sibling_all[as_index + 1:]
            if token.node_type in {"qid", "id"}
            and _valid_function_name(token.text)
        ]
        if len(candidates) == 1:
            alias = candidates[0]

    opened = "open" in texts[:import_index]
    return ImportDecl(
        module=module,
        alias=alias,
        line=line_of(node),
        opened=opened,
        public="public" in texts,
        directives=(),
        node_type="ERROR_import_alias",
    )


def _append_import(index: AstIndex, item: ImportDecl) -> None:
    key = (item.module, item.alias, item.line, item.opened)
    if any((x.module, x.alias, x.line, x.opened) == key for x in index.imports):
        return
    index.imports.append(item)
    if item.opened:
        index.opens.append(
            OpenDecl(item.alias, item.line, item.public, item.directives)
        )

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
    last_clause_owner: Optional[str] = None
    recovered_constructor_spans: Set[Tuple[int, int]] = set()
    for node in descendants(root):
        if node.type == "open":
            imp, opened = _parse_open_node(source_bytes, node)
            if imp is not None:
                _append_import(index, imp)
            if opened is not None and imp is None:
                index.opens.append(opened)
        elif node.type == "import" and (node.parent is None or node.parent.type != "open"):
            imp = _parse_import_node(source_bytes, node)
            if imp is not None:
                _append_import(index, imp)
        elif node.type == "ERROR":
            recovered = _recover_import_from_error(source_bytes, node)
            if recovered is not None:
                _append_import(index, recovered)
        elif node.type in {"record", "record_signature"}:
            rec = _record_from_node(source_bytes, node)
            if rec is not None:
                existing = index.records.get(rec.name)
                if existing is None:
                    index.records[rec.name] = rec
                else:
                    if existing.constructor is None and rec.constructor is not None:
                        existing.constructor = rec.constructor
                    existing.field_occurrences.extend(rec.field_occurrences)
                    existing.fields.update(rec.fields)
        elif node.type in {"data", "data_signature"}:
            data = _data_from_node(source_bytes, node)
            if data is not None:
                existing = index.data.get(data.name)
                if existing is None:
                    index.data[data.name] = data
                else:
                    existing.constructor_occurrences.extend(data.constructor_occurrences)
                    existing.constructors.update(data.constructors)
                    existing.constructor_node_spans.update(data.constructor_node_spans)
                recovered_constructor_spans.update(data.constructor_node_spans)
        elif node.type == "function":
            if (node.start_byte, node.end_byte) in recovered_constructor_spans:
                continue
            # Exclude constructor/record-local function declarations from the
            # module-level signature/definition tables.
            parent = node.parent
            nested_owner = None
            while parent is not None and parent != root:
                if parent.type in {"data", "record", "fields", "where"}:
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
            lhs = next(
                (child for child in node.named_children if child.type == "lhs"),
                None,
            )
            lhs_tokens = significant_tokens(source_bytes, lhs) if lhs is not None else []
            is_ellipsis = bool(
                lhs_tokens and lhs_tokens[0].text in {"...", "…"}
            )
            clause = _function_clause(
                source_bytes,
                node,
                continuation_owner=last_clause_owner,
            )
            if clause is not None:
                index.clauses.setdefault(clause.name, []).append(clause)
                if not is_ellipsis:
                    last_clause_owner = clause.name
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
        elif node.type == "module_macro":
            index.module_macro_nodes.append(node)
        elif node.type == "mutual":
            index.mutual_nodes.append(node)
        elif node.type == "where":
            index.where_nodes.append(node)
        elif node.type == "module" and node != root:
            name_node = next(
                (child for child in node.named_children if child.type == "module_name"),
                None,
            )
            nested_name = _name_from_node(source_bytes, name_node)
            if nested_name and nested_name != "_":
                index.nested_modules.add(nested_name.split(".")[-1])
        elif node.type == "record_assignments":
            # Do not double-count the record_assignments alias nested inside a
            # field_assignments node; both expose the same field assignments.
            if node.parent is None or node.parent.type != "field_assignments":
                index.record_expressions.append(_record_expression_from_node(source_bytes, node))
    return index

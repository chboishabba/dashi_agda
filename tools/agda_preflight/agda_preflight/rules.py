from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Tuple

from .ast_index import significant_tokens, typed_binders, descendants, first_descendant, applications, application_view, clause_explicit_argument_count, direct_binding_parameters, explicit_declaration_parameter_count, module_application_target_and_args
from .shapes import shape_from_node, shape_from_tokens, terminal_head, explicit_arity, equality_shape, split_top_level, PiShape, HeadShape

_IDENT = r"[A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*"

@dataclass
class Constructor:
    name: str
    datatype: str
    type_text: str
    line: int
    arity: int

@dataclass
class DataDecl:
    name: str
    line: int
    constructors: Dict[str, Constructor]
    indexed: bool = False

def _line_col(source: str, offset: int) -> Tuple[int, int]:
    line = source.count("\n", 0, offset) + 1
    prev = source.rfind("\n", 0, offset)
    return line, offset - prev

def _split_arrows(text: str) -> List[str]:
    out, buf, depth = [], [], 0
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth = max(0, depth - 1)
        if depth == 0 and ch == "→":
            out.append("".join(buf).strip()); buf = []
        elif depth == 0 and text.startswith("->", i):
            out.append("".join(buf).strip()); buf = []; i += 1
        else:
            buf.append(ch)
        i += 1
    out.append("".join(buf).strip())
    return out

def _diag(D, code, msg, s, line, col=1, hint=None, severity="error", confidence="high"):
    return D(code, msg, s.path, line, col, hint, severity, confidence)


def _resolve_record_head(checker, summary, head):
    if not head:
        return None
    imported = checker.imported_summaries(summary)
    if "." in head:
        alias, name = head.rsplit(".", 1)
        owner = imported.get(alias)
        if owner is not None and name in owner.ast.records:
            return owner, owner.ast.records[name]
    if head in summary.ast.records:
        return summary, summary.ast.records[head]
    return None


def _resolve_record_ast(checker, summary, signature):
    if signature is None or signature.type_node is None:
        return None
    head = terminal_head(shape_from_node(summary.ast.source_bytes, signature.type_node))
    return _resolve_record_head(checker, summary, head)


def _resolve_field_record_ast(checker, owner_summary, field):
    if field is None or field.type_node is None:
        return None
    head = terminal_head(
        shape_from_node(owner_summary.ast.source_bytes, field.type_node)
    )
    return _resolve_record_head(checker, owner_summary, head)


def _assignment_map(record_expr):
    return [(assignment.name, assignment) for assignment in record_expr.assignments]


def _single_identifier(source_bytes, expr_node):
    if expr_node is None:
        return None
    tokens = significant_tokens(source_bytes, expr_node)
    names = [
        token.text
        for token in tokens
        if token.node_type in {"qid", "id", "field_name"}
    ]
    punctuation = {
        token.text
        for token in tokens
        if token.text.strip() and token.node_type not in {"qid", "id", "field_name"}
    }
    return names[0] if len(names) == 1 and not punctuation else None

def extended_diagnostics(checker, s, D):
    source = s.source; out = []
    data = {
        name: DataDecl(
            name=name,
            line=decl.line,
            constructors={
                cname: Constructor(
                    name=cname,
                    datatype=name,
                    type_text=ctor.type_text,
                    line=ctor.line,
                    arity=(
                        explicit_arity(shape_from_node(s.ast.source_bytes, ctor.type_node))
                        if ctor.type_node is not None else 0
                    ),
                )
                for cname, ctor in decl.constructors.items()
            },
            indexed=False,
        )
        for name, decl in s.ast.data.items()
    }
    ctors = {
        cname: ctor
        for decl in data.values()
        for cname, ctor in decl.constructors.items()
    }
    clauses = {
        name: [
            (clause.line, clause.lhs_text, clause.rhs_text)
            for clause in items
        ]
        for name, items in s.ast.clauses.items()
    }
    imported = checker.imported_summaries(s)

    try:
        expected = ".".join(s.path.relative_to(checker.root).with_suffix("").parts)
        if s.module_name != expected:
            out.append(_diag(D, "TSAGDA004", f"module declares {s.module_name}, but path denotes {expected}", s, 1))
    except ValueError: pass

    for name, occurrences in s.ast.signature_occurrences.items():
        if len(occurrences) > 1:
            out.append(_diag(D, "TSAGDA005", f"duplicate top-level signature {name}", s, occurrences[1].line))

    for rname, rec in s.ast.records.items():
        seen_fields = set()
        for field in rec.field_occurrences:
            if field.name in seen_fields:
                out.append(_diag(D, "TSAGDA006", f"duplicate field {field.name} in record {rname}", s, field.line))
            seen_fields.add(field.name)

    constructor_owner = {}
    for dname, decl in s.ast.data.items():
        for ctor in decl.constructor_occurrences:
            previous = constructor_owner.get(ctor.name)
            if previous is not None:
                out.append(_diag(D, "TSAGDA007", f"duplicate constructor {ctor.name}", s, ctor.line))
            constructor_owner[ctor.name] = dname

    for name, sig in s.ast.signatures.items():
        if name not in s.ast.clauses:
            out.append(_diag(D, "TSAGDA008", f"{name} has a signature but no evident defining clause", s, sig.line, severity="warning", confidence="medium"))
    for name, cs in clauses.items():
        if name not in s.signatures:
            out.append(_diag(D, "TSAGDA009", f"{name} has defining clause(s) but no evident top-level signature", s, cs[0][0], severity="warning", confidence="medium"))
        seen = set()
        for clause in s.ast.clauses.get(name, []):
            lhs_tokens = tuple(token.text for token in significant_tokens(s.ast.source_bytes, clause.lhs_node))
            rhs_tokens = tuple(token.text for token in significant_tokens(s.ast.source_bytes, clause.rhs_node)) if clause.rhs_node is not None else ()
            key = (lhs_tokens, rhs_tokens)
            if key in seen:
                out.append(_diag(D, "TSAGDA010", f"duplicate identical clause for {name}", s, clause.line))
            seen.add(key)

    root_tokens = significant_tokens(s.ast.source_bytes, s.ast.tree.root_node)
    root_apps = list(applications(s.ast.source_bytes, s.ast.tree.root_node))
    for token in root_tokens:
        if token.text == "?" or "{!" in token.text or "!}" in token.text:
            out.append(_diag(D, "TSAGDA012", "unresolved interaction hole", s, token.line, token.column))
    for name, sig in s.ast.signatures.items():
        if sig.type_node is None:
            continue
        tokens = significant_tokens(s.ast.source_bytes, sig.type_node)
        if any(token.text == "_" for token in tokens):
            out.append(_diag(D, "TSAGDA013", f"exported signature {name} contains explicit underscore metavariable", s, sig.line))

    import_lines = [
        (item.line, item.opened, item.module, item.alias, item.directives)
        for item in s.ast.imports
    ]
    alias_owner = {}
    for line, is_open, module, alias, directives in import_lines:
        p = checker.module_path(module); top = module.split(".")[0]
        if not p.exists() and ((checker.root / top).exists() or (checker.root / (top + ".agda")).exists() or top == "DASHI"):
            out.append(_diag(D, "TSAGDA020", f"imported repository module {module} does not exist", s, line))
        if alias in alias_owner and alias_owner[alias] != module:
            out.append(_diag(D, "TSAGDA028", f"alias {alias} refers to both {alias_owner[alias]} and {module}", s, line))
        alias_owner[alias] = module
        target = imported.get(alias)
        if target:
            exports = set(checker.exported_names(target))
            for directive in directives:
                if directive.kind == "using":
                    for n in directive.names:
                        if n not in exports:
                            out.append(_diag(D, "TSAGDA023", f"{n} in using(...) is not exported by {module}", s, line))
                elif directive.kind == "hiding":
                    for n in directive.names:
                        if n not in exports:
                            out.append(_diag(D, "TSAGDA024", f"{n} in hiding(...) is not exported by {module}", s, line, severity="warning", confidence="medium"))
                elif directive.kind == "renaming":
                    for old, new in directive.renamings:
                        if old not in exports:
                            out.append(_diag(D, "TSAGDA025", f"renaming source {old} is not exported by {module}", s, line))

    for token in root_tokens:
        if token.node_type != "qid" or "." not in token.text:
            continue
        alias, name = token.text.rsplit(".", 1)
        target = imported.get(alias)
        if target and name not in checker.exported_names(target):
            out.append(_diag(D, "TSAGDA021", f"{alias}.{name} is not exported by {target.module_name}", s, token.line, token.column))

    for name, sig in s.ast.signatures.items():
        if sig.type_node is None:
            continue
        want = explicit_arity(shape_from_node(s.ast.source_bytes, sig.type_node))
        binder_names = {binder.name for binder in typed_binders(s.ast.source_bytes, sig.type_node)}
        for clause in s.ast.clauses.get(name, []):
            got = clause_explicit_argument_count(s.ast.source_bytes, clause.lhs_node)
            if got is not None and got != want:
                out.append(_diag(D, "TSAGDA045", f"{name} clause has {got} explicit LHS arguments; signature has {want}", s, clause.line))
            lhs_tokens = significant_tokens(s.ast.source_bytes, clause.lhs_node)
            for i, token in enumerate(lhs_tokens):
                if token.text not in {"{", "{{", "⦃"}:
                    continue
                if i + 1 >= len(lhs_tokens):
                    continue
                candidate = lhs_tokens[i + 1]
                if candidate.node_type in {"id", "bid"} and candidate.text != "_" and candidate.text not in binder_names:
                    out.append(_diag(D, "TSAGDA042", f"named implicit argument {candidate.text} is absent from {name}'s telescope", s, clause.line))

    opened = {}
    for rname, rec in s.records.items():
        if rname in s.opens:
            for f in rec.fields: opened.setdefault(f, []).append(rname)
    for f, owners in opened.items():
        if len(owners) > 1: out.append(_diag(D, "TSAGDA055", f"opened projection {f} is ambiguous across {', '.join(owners)}", s, 1, severity="warning", confidence="medium"))

    record_expr_by_start = {
        expr.node.start_byte: expr
        for expr in s.ast.record_expressions
    }
    record_target_cache = {}

    def resolve_record_expression_target(record_expr, visiting=None):
        key = record_expr.node.start_byte
        if key in record_target_cache:
            return record_target_cache[key]

        active = set() if visiting is None else set(visiting)
        if key in active:
            return None
        active.add(key)

        if record_expr.parent_field and record_expr.parent_record_start is not None:
            parent_expr = record_expr_by_start.get(record_expr.parent_record_start)
            if parent_expr is None:
                return None
            parent_target = resolve_record_expression_target(parent_expr, active)
            if parent_target is None:
                return None
            parent_owner, parent_record = parent_target
            field = parent_record.fields.get(record_expr.parent_field)
            target = _resolve_field_record_ast(checker, parent_owner, field)
            record_target_cache[key] = target
            return target

        owner = record_expr.owner_function
        if not owner:
            return None
        sig = s.ast.signatures.get(owner)
        target = _resolve_record_ast(checker, s, sig)
        record_target_cache[key] = target
        return target

    for record_expr in s.ast.record_expressions:
        target_ref = resolve_record_expression_target(record_expr)
        if target_ref is None:
            continue
        target_owner, target = target_ref
        assignments = _assignment_map(record_expr)
        names = [name for name, _ in assignments]
        for name, assignment in assignments:
            if name not in target.fields:
                out.append(_diag(D, "TSAGDA060", f"{name} is not a field of record {target.name}", s, assignment.line))
        for name in set(names):
            if names.count(name) > 1:
                duplicate = next(a for n, a in assignments if n == name)
                out.append(_diag(D, "TSAGDA061", f"field {name} is assigned more than once", s, duplicate.line))
        missing = [name for name in target.fields if name not in names]
        if missing:
            out.append(_diag(D, "TSAGDA062", f"record {target.name} is missing fields: {', '.join(missing)}", s, record_expr.line))
        for name, assignment in assignments:
            field = target.fields.get(name)
            if field is None or field.type_node is None or assignment.expr_node is None:
                continue
            lambda_node = next((n for n in assignment.expr_node.named_children if n.type == "lambda"), None)
            if lambda_node is None:
                lambda_node = next((n for n in assignment.expr_node.named_children if n.type == "lambda_clause"), None)
            if lambda_node is not None:
                tokens = significant_tokens(s.ast.source_bytes, lambda_node)
                arrows = [i for i, token in enumerate(tokens) if token.text in {"→", "->"}]
                got = 0
                if arrows:
                    before = tokens[:arrows[0]]
                    got = sum(1 for token in before if token.node_type in {"id", "bid"} and token.text not in {"λ"})
                want = explicit_arity(shape_from_node(target_owner.ast.source_bytes, field.type_node))
                if want and got != want:
                    out.append(_diag(D, "TSAGDA064", f"field {name} lambda has {got} binders; target field has {want} explicit arguments", s, assignment.line))

    for dname, decl in s.ast.data.items():
        for ctor in decl.constructors.values():
            if ctor.type_node is None:
                continue
            ctor_shape = shape_from_node(s.ast.source_bytes, ctor.type_node)
            result_head = terminal_head(ctor_shape)
            if result_head and result_head.rsplit(".", 1)[-1] != dname:
                out.append(_diag(D, "TSAGDA122", f"constructor {ctor.name} of {dname} visibly returns {result_head}", s, ctor.line))

            tokens = significant_tokens(s.ast.source_bytes, ctor.type_node)
            arrow_parts = split_top_level(tokens, {"→", "->"})
            for domain_tokens in arrow_parts[:-1]:
                domain_shape = shape_from_tokens(domain_tokens)
                if isinstance(domain_shape, PiShape) and domain_shape.domains:
                    first = domain_shape.domains[0].head
                    if isinstance(first, HeadShape) and first.head.rsplit(".", 1)[-1] == dname:
                        out.append(_diag(D, "TSAGDA130", f"{dname} occurs negatively in constructor {ctor.name}", s, ctor.line))
                        out.append(_diag(D, "TSAGDA131", f"{dname} occurs in an obvious contravariant constructor position", s, ctor.line))
                        break

    # AST-backed constructor patterns, simple finite coverage and recursion.
    for name, clause_items in s.ast.clauses.items():
        signature = s.ast.signatures.get(name)
        if signature is None or signature.type_node is None:
            continue
        signature_shape = shape_from_node(s.ast.source_bytes, signature.type_node)
        expected_dtype = None
        if isinstance(signature_shape, PiShape) and signature_shape.domains:
            first_domain = signature_shape.domains[0].head
            if isinstance(first_domain, HeadShape):
                expected_dtype = first_domain.head.rsplit(".", 1)[-1]

        catch_line = None
        used_constructors = []
        for clause in clause_items:
            lhs_tokens = significant_tokens(s.ast.source_bytes, clause.lhs_node)
            lhs_view = application_view(s.ast.source_bytes, clause.lhs_node)

            # Constructor applications nested in patterns.
            for app in applications(s.ast.source_bytes, clause.lhs_node):
                ctor_name = app.head.rsplit(".", 1)[-1]
                ctor = ctors.get(ctor_name)
                if ctor is None:
                    continue
                used_constructors.append(ctor_name)
                got = len(app.explicit_args)
                if got != ctor.arity:
                    out.append(_diag(D, "TSAGDA082", f"constructor pattern {ctor_name} has {got} arguments; arity is {ctor.arity}", s, clause.line))
                if expected_dtype and ctor.datatype != expected_dtype:
                    out.append(_diag(D, "TSAGDA081", f"pattern constructor {ctor_name} belongs to {ctor.datatype}, expected {expected_dtype}", s, clause.line))

            # Catch-all after the function head: every visible explicit arg is _.
            if catch_line is not None:
                out.append(_diag(D, "TSAGDA088", f"clause follows visible catch-all at line {catch_line}", s, clause.line))
                break
            if lhs_view is not None and lhs_view.explicit_args and all(arg.text.strip() == "_" for arg in lhs_view.explicit_args):
                catch_line = clause.line

            # Obvious absurd pattern "()".
            token_texts = [token.text for token in lhs_tokens]
            if expected_dtype in data and data[expected_dtype].constructors:
                for i in range(len(token_texts) - 1):
                    if token_texts[i] == "(" and token_texts[i + 1] == ")":
                        out.append(_diag(D, "TSAGDA085", f"absurd pattern used for visibly inhabited datatype {expected_dtype}", s, clause.line))
                        break

            # Direct identical recursive call.
            if clause.rhs_node is not None and lhs_view is not None:
                lhs_args = tuple(arg.text for arg in lhs_view.explicit_args)
                for app in applications(s.ast.source_bytes, clause.rhs_node):
                    if app.head.rsplit(".", 1)[-1] != name:
                        continue
                    rhs_args = tuple(arg.text for arg in app.explicit_args[:len(lhs_args)])
                    if lhs_args and rhs_args == lhs_args:
                        out.append(_diag(D, "TSAGDA140", f"{name} recursively calls itself with identical visible arguments", s, clause.line, severity="warning", confidence="medium"))

        if expected_dtype in data:
            dtype = data[expected_dtype]
            if dtype.constructors and used_constructors and set(used_constructors) != set(dtype.constructors):
                missing = sorted(set(dtype.constructors) - set(used_constructors))
                if missing and catch_line is None:
                    out.append(_diag(D, "TSAGDA087", f"simple finite coverage for {name} misses constructors: {', '.join(missing)}", s, clause_items[0].line))
            if len(used_constructors) != len(set(used_constructors)):
                out.append(_diag(D, "TSAGDA089", f"{name} has duplicate constructor branches in simple finite coverage", s, clause_items[0].line))

    eq_shapes = {}

    def endpoint_shapes_visibly_incompatible(left_shape, right_shape):
        left_head = terminal_head(left_shape)
        right_head = terminal_head(right_shape)
        if left_head is None or right_head is None:
            return False

        left_ctor = ctors.get(left_head.rsplit(".", 1)[-1])
        right_ctor = ctors.get(right_head.rsplit(".", 1)[-1])
        if left_ctor is not None and right_ctor is not None:
            return left_ctor.datatype != right_ctor.datatype

        sortish = {"Set", "Set₀", "Set₁", "Set₂", "Setω", "Prop", "Prop₁"}
        if left_head in sortish or right_head in sortish:
            return (left_head in sortish) != (right_head in sortish)

        return False

    def equality_endpoints_visibly_incompatible(eq_shape):
        # Arbitrary term/function heads are not type heads. Different names
        # such as f x and g x are not evidence of a type mismatch.
        return endpoint_shapes_visibly_incompatible(eq_shape.lhs, eq_shape.rhs)

    for name, signature in s.ast.signatures.items():
        if signature.type_node is None:
            continue
        eq_shape = equality_shape(
            shape_from_node(s.ast.source_bytes, signature.type_node)
        )
        if eq_shape is not None:
            eq_shapes[name] = eq_shape
            if equality_endpoints_visibly_incompatible(eq_shape):
                out.append(
                    _diag(
                        D,
                        "TSAGDA105",
                        f"equality {name} has visibly incompatible rigid endpoint heads",
                        s,
                        signature.line,
                    )
                )

    for name, clause_items in s.ast.clauses.items():
        target_eq = eq_shapes.get(name)
        for clause in clause_items:
            if clause.rhs_node is None:
                continue
            tokens = significant_tokens(s.ast.source_bytes, clause.rhs_node)
            if len(tokens) == 1 and tokens[0].text == "refl" and target_eq is not None:
                if equality_endpoints_visibly_incompatible(target_eq):
                    out.append(
                        _diag(
                            D,
                            "TSAGDA100",
                            "refl is used for equality endpoints with incompatible rigid heads",
                            s,
                            clause.line,
                        )
                    )

            for i, token in enumerate(tokens):
                if token.text != "trans" or i + 2 >= len(tokens):
                    continue
                left_name = tokens[i + 1].text
                right_name = tokens[i + 2].text
                left_eq = eq_shapes.get(left_name)
                right_eq = eq_shapes.get(right_name)
                if left_eq is None or right_eq is None:
                    continue
                if endpoint_shapes_visibly_incompatible(left_eq.rhs, right_eq.lhs):
                    out.append(
                        _diag(
                            D,
                            "TSAGDA102",
                            f"trans intermediate endpoints {left_name}/{right_name} have incompatible rigid heads",
                            s,
                            clause.line,
                        )
                    )
    known = set(s.signatures) | set(data) | set(ctors)
    fix = {}
    postulates = []
    critical = any(x in str(s.path) for x in ("/Closure/", "/Millennium/", "Exact.agda", "Receipt", "Theorem"))

    for node in s.ast.infix_nodes:
        tokens = significant_tokens(s.ast.source_bytes, node)
        if len(tokens) < 3:
            continue
        kind = tokens[0].text
        precedence = tokens[1].text
        for token in tokens[2:]:
            sym = token.text
            shape = (kind, precedence)
            if sym not in known:
                out.append(_diag(D, "TSAGDA150", f"fixity declaration references unknown symbol {sym}", s, token.line, severity="warning", confidence="medium"))
            if sym in fix and fix[sym] != shape:
                out.append(_diag(D, "TSAGDA151", f"conflicting fixity declarations for {sym}", s, token.line))
            fix[sym] = shape

    for node in s.ast.syntax_nodes:
        tokens = significant_tokens(s.ast.source_bytes, node)
        identifiers = [token for token in tokens if token.node_type == "id"]
        if identifiers:
            target = identifiers[0]
            if target.text not in known:
                out.append(_diag(D, "TSAGDA153", f"syntax declaration references unknown symbol {target.text}", s, target.line, severity="warning", confidence="medium"))

    for node in s.ast.postulate_nodes:
        for fn in descendants(node, "function"):
            sig_node = first_descendant(fn, "function_name")
            if sig_node is None:
                continue
            names = [token for token in significant_tokens(s.ast.source_bytes, sig_node) if token.node_type in {"qid", "id"}]
            if names:
                postulates.append((names[0].text, names[0].line))

    for node in s.ast.pragmas:
        text_value = s.ast.source_bytes[node.start_byte:node.end_byte].decode("utf-8", "replace")
        upper = text_value.upper()
        line = node.start_point[0] + 1
        if "NON_TERMINATING" in upper:
            out.append(_diag(D, "TSAGDA162", "NON_TERMINATING pragma weakens termination guarantees", s, line, severity="warning", confidence="medium"))
        elif "TERMINATING" in upper:
            out.append(_diag(D, "TSAGDA161", "TERMINATING pragma bypasses termination checking", s, line, severity="warning", confidence="medium"))
        if "NO_POSITIVITY_CHECK" in upper:
            out.append(_diag(D, "TSAGDA163", "NO_POSITIVITY_CHECK disables positivity checking", s, line, severity="warning", confidence="medium"))
        if "ALLOW-UNSOLVED-METAS" in upper:
            out.append(_diag(D, "TSAGDA164", "allow-unsolved-metas weakens the trust boundary", s, line, severity="warning", confidence="medium"))
        if any(flag in upper for flag in ("--TYPE-IN-TYPE", "--NO-POSITIVITY-CHECK", "--NO-TERMINATION-CHECK")):
            out.append(_diag(D, "TSAGDA165", "unsafe OPTIONS pragma in proof source", s, line, severity="warning", confidence="medium"))
        words = text_value.replace("{-#", " ").replace("#-}", " ").split()
        if words and words[0].upper() in {"COMPILE", "FOREIGN"} and len(words) > 1:
            target = words[1]
            if target not in known:
                out.append(_diag(D, "TSAGDA166", f"foreign/compile pragma names unknown declaration {target}", s, line))

    if critical:
        for n, line in postulates: out.append(_diag(D, "TSAGDA160", f"postulate {n} occurs in proof-critical source", s, line))
        if s.module_name.endswith("Exact"):
            for token in root_tokens:
                if token.text in {"_", "?"} or "{!" in token.text or "!}" in token.text:
                    out.append(_diag(D, "TSAGDA204", "Exact module contains unresolved proof placeholder", s, token.line, token.column))
            for n, line in postulates:
                out.append(_diag(D, "TSAGDA204", f"Exact module postulates {n}", s, line))
        for n, line in postulates:
            lowered = n.lower()
            if any(word in lowered for word in ("theorem", "receipt", "exact", "closure", "gate")):
                out.append(_diag(D, "TSAGDA202", f"proof endpoint {n} is only postulated", s, line))
        if "/Closure/" in str(s.path):
            for line, _, module, _, _ in import_lines:
                lowered = module.lower()
                if any(word in lowered for word in ("obstruction", "assumption", "postulate", "placeholder")):
                    out.append(_diag(D, "TSAGDA205", f"closure imports assumption/obstruction module {module}", s, line, severity="warning", confidence="medium"))

    for name, sig in s.ast.signatures.items():
        if sig.type_node is None:
            continue
        tokens = significant_tokens(s.ast.source_bytes, sig.type_node)
        if any(token.text == "_" for token in tokens):
            shape = equality_shape(shape_from_node(s.ast.source_bytes, sig.type_node))
            code = "TSAGDA173" if shape is not None else "TSAGDA170"
            out.append(_diag(D, code, f"signature {name} contains explicit underscore", s, sig.line))
    for record_expr in s.ast.record_expressions:
        for assignment in record_expr.assignments:
            if assignment.expr_node is None:
                continue
            tokens = significant_tokens(s.ast.source_bytes, assignment.expr_node)
            if len(tokens) == 1 and tokens[0].text == "_":
                out.append(_diag(D, "TSAGDA172", f"record field {assignment.name} is filled with raw underscore", s, assignment.line, severity="warning", confidence="medium"))

    # Repository graph checks: stay inside the module's reachable import cone.
    # Running a repository-wide rglob/dependency_graph here made this O(modules × repo).
    cycle_found = False
    permanent = set()
    temporary = []

    def visit_import_cone(summary):
        nonlocal cycle_found
        module = summary.module_name
        if module in permanent or cycle_found:
            return
        if module in temporary:
            cycle_found = True
            return

        temporary.append(module)
        for dependency in sorted(set(summary.imports.values())):
            dependency_path = checker.module_path(dependency)
            if not dependency_path.exists():
                continue
            try:
                dependency_summary = checker.parse_summary(dependency_path)
            except (OSError, UnicodeDecodeError):
                continue
            visit_import_cone(dependency_summary)
            if cycle_found:
                break
        temporary.pop()
        permanent.add(module)

    visit_import_cone(s)
    if cycle_found:
        out.append(_diag(D, "TSAGDA029", f"module {s.module_name} participates in an import cycle reachable from this module", s, 1))

    # Canonical module identity is path-derived. A second canonical file for the
    # same declared module is enough evidence for TSAGDA030; do not scan the repo.
    canonical_path = checker.module_path(s.module_name).resolve()
    if canonical_path.exists() and canonical_path != s.path.resolve():
        out.append(
            _diag(
                D,
                "TSAGDA030",
                f"module identity {s.module_name} also resolves to canonical path {canonical_path}",
                s,
                1,
            )
        )

    # TSAGDA026/027: collisions created by open imports and renamings.
    visible = {}
    for line, is_open, module, alias, directives in import_lines:
        if not is_open: continue
        target = imported.get(alias)
        if not target: continue
        names = set(checker.exported_names(target))
        ren = {}
        for directive in directives:
            if directive.kind == "using":
                names &= set(directive.names)
            elif directive.kind == "hiding":
                names -= set(directive.names)
            elif directive.kind == "renaming":
                ren.update(dict(directive.renamings))
        for n in names:
            vn = ren.get(n, n); visible.setdefault(vn, []).append(module)
    for n, mods in visible.items():
        if len(set(mods)) > 1 and n not in s.signatures and n not in s.records:
            out.append(_diag(D, "TSAGDA027", f"open imports make {n} ambiguous between {', '.join(sorted(set(mods)))}", s, 1, severity="warning", confidence="medium"))

    # TSAGDA040/041/046/047/049: bounded arity checks for simple applications.
    known_arity = {
        name: explicit_arity(shape_from_node(s.ast.source_bytes, sig.type_node))
        for name, sig in s.ast.signatures.items()
        if sig.type_node is not None
    }
    known_arity.update({name: ctor.arity for name, ctor in ctors.items()})
    for clause_items in s.ast.clauses.values():
        for clause in clause_items:
            if clause.rhs_node is None:
                continue
            for app in applications(s.ast.source_bytes, clause.rhs_node):
                short_head = app.head.rsplit(".", 1)[-1]
                want = known_arity.get(short_head)
                if want is None:
                    continue
                got = len(app.explicit_args)
                if got > want:
                    line = app.head_node.start_point[0] + 1
                    col = app.head_node.start_point[1] + 1
                    code = "TSAGDA046" if short_head in ctors else "TSAGDA040"
                    out.append(_diag(D, code, f"{app.head} is visibly over-applied: {got} explicit arguments for arity {want}", s, line, col))

    # AST-backed local record constructors and imported projections.
    local_record_constructor_arity = {
        record.constructor: len(record.fields)
        for record in s.ast.records.values()
        if record.constructor
    }
    for app in root_apps:
        short = app.head.rsplit(".", 1)[-1]
        want = local_record_constructor_arity.get(short)
        if want is not None and len(app.explicit_args) > want:
            out.append(
                _diag(
                    D,
                    "TSAGDA047",
                    f"record constructor {app.head} is visibly over-applied ({len(app.explicit_args)}>{want})",
                    s,
                    app.head_node.start_point[0] + 1,
                    app.head_node.start_point[1] + 1,
                )
            )

    imported_projection_specs = {}
    for alias, mod in imported.items():
        for rname, record in mod.ast.records.items():
            for fname, field in record.fields.items():
                arity = (
                    explicit_arity(shape_from_node(mod.ast.source_bytes, field.type_node))
                    if field.type_node is not None else 0
                )
                imported_projection_specs[f"{alias}.{fname}"] = (mod, rname, field, 1 + arity)

    app_head_spans = []
    for app in root_apps:
        app_head_spans.append((app.head, app.head_node.start_byte, app.head_node.end_byte))
        spec = imported_projection_specs.get(app.head)
        if spec is None:
            continue
        mod, owner, field, want = spec
        got = len(app.explicit_args)
        line = app.head_node.start_point[0] + 1
        col = app.head_node.start_point[1] + 1
        if got == 0:
            out.append(_diag(D, "TSAGDA052", f"{app.head} is used without a visible {owner} receiver", s, line, col))
            out.append(_diag(D, "TSAGDA049", f"projection {app.head} is under-applied", s, line, col))
            continue
        if got > want:
            out.append(_diag(D, "TSAGDA053", f"{app.head} is visibly over-applied ({got}>{want})", s, line, col))

        receiver = app.explicit_args[0].text.strip()
        if receiver in mod.ast.records or receiver in mod.ast.signatures:
            out.append(_diag(D, "TSAGDA051", f"{app.head} receives known declaration/type name {receiver} where a {owner} value is expected", s, line, col, severity="warning", confidence="medium"))

        containing = None
        for function_name, clause_items in s.ast.clauses.items():
            for clause in clause_items:
                if clause.node.start_byte <= app.head_node.start_byte < clause.node.end_byte:
                    containing = function_name
                    break
            if containing is not None:
                break
        if containing is not None:
            signature = s.ast.signatures.get(containing)
            if signature is not None and signature.type_node is not None:
                binder = next(
                    (
                        item for item in typed_binders(s.ast.source_bytes, signature.type_node)
                        if item.name == receiver
                    ),
                    None,
                )
                if binder is not None:
                    words = (
                        binder.type_text
                        .replace("(", " ").replace(")", " ")
                        .replace("{", " ").replace("}", " ")
                        .replace(",", " ").split()
                    )
                    record_heads = {word.rsplit(".", 1)[-1] for word in words}
                    imported_records = set(mod.ast.records)
                    mismatched = sorted((record_heads & imported_records) - {owner})
                    if mismatched:
                        out.append(_diag(D, "TSAGDA054", f"projection {app.head} belongs to {owner}, but receiver {receiver} is declared as {mismatched[0]}", s, line, col))
                        out.append(_diag(D, "TSAGDA050", f"{app.head} expects {owner}; receiver {receiver} has visibly different declared head", s, line, col))

    # Zero-argument qualified projections are not yielded by applications().
    for token in root_tokens:
        if token.node_type != "qid" or token.text not in imported_projection_specs:
            continue
        covered = any(
            head == token.text and start <= token.start_byte < end
            for head, start, end in app_head_spans
        )
        if not covered:
            _, owner, _, _ = imported_projection_specs[token.text]
            out.append(_diag(D, "TSAGDA052", f"{token.text} is used without a visible {owner} receiver", s, token.line, token.column))
            out.append(_diag(D, "TSAGDA049", f"projection {token.text} is under-applied", s, token.line, token.column))

    # Constructor equalities with visibly different datatype owners.
    for i in range(len(root_tokens) - 2):
        left, op, right = root_tokens[i:i + 3]
        lctor = ctors.get(left.text.rsplit(".", 1)[-1])
        rctor = ctors.get(right.text.rsplit(".", 1)[-1])
        if op.text == "≡" and lctor is not None and rctor is not None and lctor.datatype != rctor.datatype:
            out.append(_diag(D, "TSAGDA075", f"equality compares constructors from different datatypes: {left.text} vs {right.text}", s, right.line, right.column))

    # TSAGDA101/103/104: AST-backed equality combinator outer-shape checks.
    for name, clause_items in s.ast.clauses.items():
        target_shape = eq_shapes.get(name)
        for clause in clause_items:
            if clause.rhs_node is None:
                continue
            tokens = significant_tokens(s.ast.source_bytes, clause.rhs_node)
            for app in applications(s.ast.source_bytes, clause.rhs_node):
                short = app.head.rsplit(".", 1)[-1]
                if short == "sym" and app.explicit_args and target_shape is not None:
                    proof_name = app.explicit_args[0].text.strip()
                    proof_shape = eq_shapes.get(proof_name)
                    if proof_shape is not None:
                        left_bad = endpoint_shapes_visibly_incompatible(proof_shape.lhs, target_shape.rhs)
                        right_bad = endpoint_shapes_visibly_incompatible(proof_shape.rhs, target_shape.lhs)
                        if left_bad or right_bad:
                            out.append(_diag(D, "TSAGDA101", f"sym proof endpoint head does not match target equality for {name}", s, clause.line))
                elif short == "cong" and app.explicit_args:
                    function_name = app.explicit_args[0].text.strip()
                    function_sig = s.ast.signatures.get(function_name)
                    if function_sig is not None and function_sig.type_node is not None:
                        arity = explicit_arity(shape_from_node(s.ast.source_bytes, function_sig.type_node))
                        if arity == 0:
                            out.append(_diag(D, "TSAGDA103", f"cong function {function_name} has no visible function argument", s, clause.line))
            if target_shape is None:
                for token in tokens:
                    if token.text in eq_shapes:
                        out.append(_diag(D, "TSAGDA104", f"equality proof {token.text} is used as the value of non-equality result {name}", s, clause.line))
                        break

    # TSAGDA120/121/123: AST-backed rigid declaration sanity.
    known_terms = set(s.ast.clauses) | set(ctors)
    for rname, rec in s.ast.records.items():
        for fname, field in rec.fields.items():
            if field.type_node is None:
                continue
            head = terminal_head(shape_from_node(s.ast.source_bytes, field.type_node))
            if head in known_terms and head not in data and head not in s.ast.records:
                out.append(_diag(D, "TSAGDA120", f"field {rname}.{fname} has known term {head} in type-head position", s, field.line))
                out.append(_diag(D, "TSAGDA123", f"projection {rname}.{fname} has known term {head} in type position", s, field.line))
    for dname, decl in s.ast.data.items():
        for ctor in decl.constructors.values():
            if ctor.type_node is None:
                continue
            head = terminal_head(shape_from_node(s.ast.source_bytes, ctor.type_node))
            if head in known_terms and head not in data:
                out.append(_diag(D, "TSAGDA121", f"constructor {ctor.name} result resolves to known term {head}", s, ctor.line))

    # TSAGDA141/142 are advisory AST structural recursion warnings.
    for name, clause_items in s.ast.clauses.items():
        for clause in clause_items:
            if clause.rhs_node is None:
                continue
            lhs_view = application_view(s.ast.source_bytes, clause.lhs_node)
            lhs_args = tuple(arg.text for arg in lhs_view.explicit_args) if lhs_view is not None else ()
            for app in applications(s.ast.source_bytes, clause.rhs_node):
                if app.head.rsplit(".", 1)[-1] != name:
                    continue
                rhs_args = tuple(arg.text for arg in app.explicit_args[:len(lhs_args)])
                if lhs_args and rhs_args:
                    numeric_increase = False
                    for left, right in zip(lhs_args, rhs_args):
                        if left.isdigit() and right.isdigit() and int(right) > int(left):
                            numeric_increase = True
                    if numeric_increase:
                        out.append(_diag(D, "TSAGDA141", f"{name} has an obviously increasing numeric recursive argument", s, clause.line, severity="warning", confidence="medium"))
                    obvious_smaller = any(
                        right in {"pred", "tail"} or (left.startswith("(") and right in left)
                        for left, right in zip(lhs_args, rhs_args)
                    )
                    if not obvious_smaller:
                        out.append(_diag(D, "TSAGDA142", f"{name} recursive call has no syntactically obvious smaller argument", s, clause.line, severity="warning", confidence="medium"))

    # TSAGDA143: termination bypass in proof-critical code.
    if critical:
        for node in s.ast.pragmas:
            text_value = s.ast.source_bytes[node.start_byte:node.end_byte].decode("utf-8", "replace").upper()
            if "TERMINATING" in text_value:
                out.append(_diag(D, "TSAGDA143", "proof-critical code uses a termination-bypass pragma", s, node.start_point[0] + 1))

    # TSAGDA152: mixfix holes versus visible arity.
    for sym, shape in fix.items():
        if "_" in sym and sym in s.signatures:
            holes = sym.count("_")
            ast_sig = s.ast.signatures.get(sym)
            want = (
                explicit_arity(shape_from_node(s.ast.source_bytes, ast_sig.type_node))
                if ast_sig is not None and ast_sig.type_node is not None else 0
            )
            if holes != want:
                out.append(_diag(D, "TSAGDA152", f"mixfix {sym} has {holes} holes but signature has {want} explicit arguments", s, s.signatures[sym].line, severity="warning", confidence="medium"))

    # TSAGDA174: raw metas in module applications.
    for node in s.ast.module_macro_nodes:
        tokens = significant_tokens(s.ast.source_bytes, node)
        if any(token.text == "_" for token in tokens):
            first = tokens[0] if tokens else None
            out.append(_diag(D, "TSAGDA174", "module application contains raw underscore metavariable", s, first.line if first else node.start_point[0] + 1, first.column if first else 1, severity="warning", confidence="medium"))

    # TSAGDA200/201/203/206/208: DASHI-specific structural policy.
    if critical:
        for record_expr in s.ast.record_expressions:
            for assignment in record_expr.assignments:
                if assignment.expr_node is None:
                    continue
                tokens = significant_tokens(s.ast.source_bytes, assignment.expr_node)
                if len(tokens) == 1 and tokens[0].text == "_":
                    out.append(_diag(D, "TSAGDA201", f"proof-critical record field {assignment.name} contains raw metavariable", s, assignment.line))
        for rname, rec in s.ast.records.items():
            for fname, field in rec.fields.items():
                lowered = fname.lower()
                if not any(word in lowered for word in ("agreement", "proof", "witness", "receipt")):
                    continue
                if field.type_node is None:
                    continue
                head = terminal_head(shape_from_node(s.ast.source_bytes, field.type_node))
                if head == "Set":
                    out.append(_diag(D, "TSAGDA203", f"proof-like field {rname}.{fname} is unconstrained Set rather than an evident proposition/witness", s, field.line, severity="warning", confidence="medium"))
        module_lower = s.module_name.lower()
        if any(word in module_lower for word in ("factorthrough", "admissib", "bidi")):
            heads = [
                terminal_head(shape_from_node(s.ast.source_bytes, sig.type_node))
                for sig in s.ast.signatures.values()
                if sig.type_node is not None
            ]
            rigid = sorted(set(h for h in heads if h and "." in h))
            if len(rigid) > 1:
                code = "TSAGDA208" if any(word in module_lower for word in ("factorthrough", "admissib")) else "TSAGDA206"
                out.append(_diag(D, code, f"bridge module exposes multiple qualified carrier/result families: {', '.join(rigid[:6])}", s, 1))


    # Remaining bounded structural diagnostics and specific aliases.

    # TSAGDA011: empty where/mutual blocks from AST.
    for node in list(s.ast.where_nodes) + list(s.ast.mutual_nodes):
        semantic_children = [
            child for child in node.named_children
            if child.type not in {"module_name", "bid"}
        ]
        if not semantic_children:
            out.append(_diag(D, "TSAGDA011", f"{node.type} block has no evident declaration", s, node.start_point[0] + 1))

    # TSAGDA022/026: qualified alias mistakes and rename collisions.
    known_aliases = set(imported)
    local_prefixes = set(s.records) | set(data)
    for token in root_tokens:
        if token.node_type != "qid" or "." not in token.text:
            continue
        alias = token.text.split(".", 1)[0]
        if alias not in known_aliases and alias not in local_prefixes and alias[:1].isupper():
            out.append(_diag(D, "TSAGDA022", f"qualified prefix {alias} is not a known import alias or local namespace", s, token.line, token.column, severity="warning", confidence="medium"))
    for line, is_open, module, alias, directives in import_lines:
        for directive in directives:
            if directive.kind != "renaming":
                continue
            for old, new in directive.renamings:
                if new in s.signatures or new in s.records:
                    out.append(_diag(D, "TSAGDA026", f"renaming {old} to {new} collides with a local declaration", s, line))

    # TSAGDA041/043/044/110/111: AST telescope and lambda visibility.
    for name, clause_items in s.ast.clauses.items():
        sig = s.ast.signatures.get(name)
        if sig is None or sig.type_node is None:
            continue
        signature_shape = shape_from_node(s.ast.source_bytes, sig.type_node)
        want = explicit_arity(signature_shape)
        binders = typed_binders(s.ast.source_bytes, sig.type_node)
        binder_visibility = {binder.name: binder.visibility for binder in binders}

        for clause in clause_items:
            got = clause_explicit_argument_count(s.ast.source_bytes, clause.lhs_node)
            if got is not None and got != want:
                out.append(_diag(D, "TSAGDA110", f"{name} clause binder count {got} does not match explicit telescope arity {want}", s, clause.line))

            lhs_tokens = significant_tokens(s.ast.source_bytes, clause.lhs_node)
            for i, token in enumerate(lhs_tokens[:-1]):
                if token.text not in {"{", "{{", "⦃"}:
                    continue
                candidate = lhs_tokens[i + 1]
                expected_visibility = binder_visibility.get(candidate.text)
                actual_visibility = "instance" if token.text in {"{{", "⦃"} else "implicit"
                if expected_visibility == "explicit":
                    out.append(_diag(D, "TSAGDA043", f"explicit binder {candidate.text} is matched with {actual_visibility} visibility", s, clause.line))
                    out.append(_diag(D, "TSAGDA111", f"clause visibility for {candidate.text} disagrees with signature", s, clause.line))

            if clause.rhs_node is None:
                continue
            lambda_node = first_descendant(clause.rhs_node, "lambda")
            if lambda_node is not None:
                tokens = significant_tokens(s.ast.source_bytes, lambda_node)
                arrow = next((i for i, token in enumerate(tokens) if token.text in {"→", "->"}), None)
                if arrow is not None:
                    lambda_binders = [
                        token for token in tokens[:arrow]
                        if token.node_type in {"id", "bid"} and token.text not in {"λ", "_"}
                    ]
                    remaining = max(0, want - (got or 0))
                    if remaining and len(lambda_binders) != remaining:
                        out.append(_diag(D, "TSAGDA044", f"RHS lambda exposes {len(lambda_binders)} binders but {remaining} explicit binders remain", s, clause.line, severity="warning", confidence="medium"))

            rhs_view = application_view(s.ast.source_bytes, clause.rhs_node)
            if rhs_view is not None and not rhs_view.args:
                target_sig = s.ast.signatures.get(rhs_view.head.rsplit(".", 1)[-1])
                if target_sig is not None and target_sig.type_node is not None:
                    target_arity = explicit_arity(shape_from_node(s.ast.source_bytes, target_sig.type_node))
                    result_head = terminal_head(signature_shape)
                    if target_arity > 0 and result_head not in {None, "Set", "Set₀", "Set₁", "Set₂", "Setω", "Prop", "Prop₁"}:
                        out.append(_diag(D, "TSAGDA041", f"RHS {rhs_view.head} is a known function left unapplied in a saturated result position", s, clause.line, severity="warning", confidence="medium"))

    # TSAGDA048: AST parameterized module application arity.
    module_params = {}
    for alias, mod in imported.items():
        outer_module = next((node for node in mod.ast.tree.root_node.named_children if node.type == "module"), None)
        if outer_module is not None:
            module_params[alias] = explicit_declaration_parameter_count(mod.ast.source_bytes, outer_module)

    for macro in s.ast.module_macro_nodes:
        target, args = module_application_target_and_args(s.ast.source_bytes, macro)
        if not target:
            continue
        alias = target.split(".", 1)[0]
        want = module_params.get(alias)
        if want is None:
            continue
        got = sum(1 for arg in args if arg.visibility == "explicit" and arg.text != "_")
        if got != want:
            out.append(_diag(D, "TSAGDA048", f"module application supplies {got} visible arguments; imported module expects {want}", s, macro.start_point[0] + 1))

    # TSAGDA056: dependent field projection used bare despite a record binder.
    for rname, record in s.ast.records.items():
        field_names = set(record.fields)
        dependent = set()
        for fname, field in record.fields.items():
            if field.type_node is None:
                continue
            tokens = significant_tokens(s.ast.source_bytes, field.type_node)
            referenced = {token.text for token in tokens if token.text in field_names and token.text != fname}
            if referenced:
                dependent.add(fname)
        if not dependent:
            continue

        for name, sig in s.ast.signatures.items():
            if sig.type_node is None:
                continue
            binders = typed_binders(s.ast.source_bytes, sig.type_node)
            if not any(rname in binder.type_text.replace("(", " ").replace(")", " ").split() for binder in binders):
                continue
            tokens = significant_tokens(s.ast.source_bytes, sig.type_node)
            for i, token in enumerate(tokens):
                if token.text not in dependent:
                    continue
                following = tokens[i + 1] if i + 1 < len(tokens) else None
                if following is None or following.text in {"→", "->", ")", "}", "}}", "⦄", "]"}:
                    out.append(_diag(D, "TSAGDA056", f"dependent projection {token.text} is used without an evident {rname} receiver", s, token.line, token.column, severity="warning", confidence="medium"))

    # TSAGDA063/065/066/067/068 and TSAGDA200: AST-backed record refinements.
    record_ctor_owner = {
        record.constructor: name
        for name, record in s.ast.records.items()
        if record.constructor
    }
    for record_expr in s.ast.record_expressions:
        owner = record_expr.owner_function
        if not owner:
            continue
        sig = s.ast.signatures.get(owner)
        target_ref = _resolve_record_ast(checker, s, sig)
        sig_head = terminal_head(shape_from_node(s.ast.source_bytes, sig.type_node)) if sig and sig.type_node is not None else None
        if target_ref is None:
            if sig_head in data:
                out.append(_diag(D, "TSAGDA063", f"record expression is used where datatype {sig_head} is the declared result", s, record_expr.line))
            continue
        target_owner, target = target_ref
        for fname, assignment in _assignment_map(record_expr):
            field = target.fields.get(fname)
            if field is None or field.type_node is None or assignment.expr_node is None:
                continue
            field_head = terminal_head(shape_from_node(target_owner.ast.source_bytes, field.type_node))
            tokens = significant_tokens(s.ast.source_bytes, assignment.expr_node)
            if len(tokens) == 1 and tokens[0].text == "Set" and field_head not in {"Set","Set₀","Set₁","Set₂","Setω","Prop","Prop₁"}:
                out.append(_diag(D, "TSAGDA200", f"adapter field {fname} supplies Set where target expects witness/result {field_head}", s, assignment.line))
            ident = _single_identifier(s.ast.source_bytes, assignment.expr_node)
            if ident in record_ctor_owner and record_ctor_owner[ident] != target.name:
                out.append(_diag(D, "TSAGDA068", f"constructor {ident} constructs {record_ctor_owner[ident]}, not target record {target.name}", s, assignment.line))

    # TSAGDA070-079 AST-backed shallow head checks.
    for name, clause_items in s.ast.clauses.items():
        sig = s.ast.signatures.get(name)
        if sig is None or sig.type_node is None:
            continue
        signature_shape = shape_from_node(s.ast.source_bytes, sig.type_node)
        expected = terminal_head(signature_shape)
        for clause in clause_items:
            if clause.rhs_node is None:
                continue
            rhs_tokens = significant_tokens(s.ast.source_bytes, clause.rhs_node)
            rhs_shape = shape_from_node(s.ast.source_bytes, clause.rhs_node)

            if len(rhs_tokens) == 1 and rhs_tokens[0].text in {"Set","Set₀","Set₁","Set₂","Setω","Prop","Prop₁"} and expected not in {"Set","Set₀","Set₁","Set₂","Setω","Prop","Prop₁"}:
                out.append(_diag(D, "TSAGDA078", f"sort {rhs_tokens[0].text} is used as the value of {name}, whose rigid result head is {expected}", s, clause.line))
                out.append(_diag(D, "TSAGDA070", f"type/sort supplied where a term of head {expected} is expected", s, clause.line))

            rhs_view = application_view(s.ast.source_bytes, clause.rhs_node)
            if rhs_view is not None:
                short = rhs_view.head.rsplit(".", 1)[-1]
                ctor = ctors.get(short)
                if ctor is not None and expected and ctor.datatype != expected.rsplit(".", 1)[-1]:
                    out.append(_diag(D, "TSAGDA072", f"{name} returns constructor {short} of {ctor.datatype}, not declared head {expected}", s, clause.line))
                    out.append(_diag(D, "TSAGDA075", f"constructor {short} belongs to wrong datatype for {name}", s, clause.line))

                function_sig = s.ast.signatures.get(short)
                if function_sig is not None and function_sig.type_node is not None:
                    function_shape = shape_from_node(s.ast.source_bytes, function_sig.type_node)
                    if isinstance(function_shape, PiShape) and rhs_view.explicit_args:
                        first_expected = function_shape.domains[0].head if function_shape.domains else None
                        arg_ident = rhs_view.explicit_args[0].text.strip()
                        arg_ctor = ctors.get(arg_ident.rsplit(".", 1)[-1])
                        if isinstance(first_expected, HeadShape) and arg_ctor is not None:
                            expected_dt = first_expected.head.rsplit(".", 1)[-1]
                            if expected_dt != arg_ctor.datatype:
                                out.append(_diag(D, "TSAGDA073", f"argument {arg_ident} has datatype {arg_ctor.datatype}, but {rhs_view.head} expects {expected_dt}", s, clause.line))
                    if explicit_arity(function_shape) == 0 and rhs_view.args:
                        out.append(_diag(D, "TSAGDA079", f"known non-function {rhs_view.head} is applied as a function", s, clause.line))

            if len(rhs_tokens) == 1 and rhs_tokens[0].node_type == "literal":
                text_value = rhs_tokens[0].text
                numeric = text_value and text_value[0].isdigit()
                if numeric and expected in {"Bool", "String", "Char"}:
                    out.append(_diag(D, "TSAGDA074", f"numeric literal is incompatible with rigid result head {expected}", s, clause.line))

    # Known functions occurring bare in type positions.
    function_arities = {
        fn: explicit_arity(shape_from_node(s.ast.source_bytes, fsig.type_node))
        for fn, fsig in s.ast.signatures.items()
        if fsig.type_node is not None
    }
    for name, sig in s.ast.signatures.items():
        if sig.type_node is None:
            continue
        tokens = significant_tokens(s.ast.source_bytes, sig.type_node)
        for i, token in enumerate(tokens):
            arity = function_arities.get(token.text)
            if not arity or token.text == name:
                continue
            following = tokens[i + 1] if i + 1 < len(tokens) else None
            if following is None or following.text in {"→", "->", ")", "}", "}}", "⦄", "]"}:
                out.append(_diag(D, "TSAGDA076", f"known function {token.text} is used as a type without enough application", s, token.line, token.column, severity="warning", confidence="medium"))

    # TSAGDA080/083/084/086: bounded AST pattern hygiene.
    global_pattern_names = set(ctors) | set(data) | set(s.records)
    for name, clause_items in s.ast.clauses.items():
        signature = s.ast.signatures.get(name)
        for clause in clause_items:
            tokens = significant_tokens(s.ast.source_bytes, clause.lhs_node)
            token_texts = [token.text for token in tokens]

            # Unknown constructor-like qualified/unqualified heads in nested apps.
            for app in applications(s.ast.source_bytes, clause.lhs_node):
                short = app.head.rsplit(".", 1)[-1]
                if short and short[:1].isupper() and short not in global_pattern_names:
                    line = app.head_node.start_point[0] + 1
                    col = app.head_node.start_point[1] + 1
                    out.append(_diag(D, "TSAGDA080", f"pattern references unknown constructor-like name {app.head}", s, line, col, severity="warning", confidence="medium"))

            # Inaccessible pattern token '.' followed by an identifier with no
            # other occurrence in the same LHS is suspicious.
            for i, token in enumerate(tokens[:-1]):
                if token.text != ".":
                    continue
                target = tokens[i + 1]
                occurrences = sum(1 for candidate in tokens if candidate.text == target.text)
                if target.node_type in {"id", "qid"} and occurrences == 1:
                    out.append(_diag(D, "TSAGDA084", f"inaccessible pattern .{target.text} has no evident local binder", s, target.line, target.column, severity="warning", confidence="medium"))

            # Absurd lambda in RHS when any explicit signature domain has a
            # locally known inhabited datatype head.
            if clause.rhs_node is not None and signature is not None and signature.type_node is not None:
                rhs_tokens = significant_tokens(s.ast.source_bytes, clause.rhs_node)
                has_absurd_lambda = any(
                    rhs_tokens[i].text in {"λ", "\\"}
                    and i + 2 < len(rhs_tokens)
                    and rhs_tokens[i + 1].text == "("
                    and rhs_tokens[i + 2].text == ")"
                    for i in range(len(rhs_tokens))
                )
                if has_absurd_lambda:
                    shape = shape_from_node(s.ast.source_bytes, signature.type_node)
                    if isinstance(shape, PiShape):
                        inhabited = next(
                            (
                                domain.head.head.rsplit(".", 1)[-1]
                                for domain in shape.domains
                                if isinstance(domain.head, HeadShape)
                                and domain.head.head.rsplit(".", 1)[-1] in data
                                and data[domain.head.head.rsplit(".", 1)[-1]].constructors
                            ),
                            None,
                        )
                        if inhabited:
                            out.append(_diag(D, "TSAGDA086", f"absurd lambda used while visible domain {inhabited} is inhabited", s, clause.line, severity="warning", confidence="medium"))

    # TSAGDA071: known term supplied in a type/sort-valued record field.
    known_term_heads = set(clauses) | set(ctors)
    for record_expr in s.ast.record_expressions:
        owner = record_expr.owner_function
        if not owner:
            continue
        target_ref = _resolve_record_ast(checker, s, s.ast.signatures.get(owner))
        if target_ref is None:
            continue
        target_owner, target = target_ref
        for fname, assignment in _assignment_map(record_expr):
            field = target.fields.get(fname)
            if field is None or field.type_node is None or assignment.expr_node is None:
                continue
            field_head = terminal_head(shape_from_node(target_owner.ast.source_bytes, field.type_node))
            if field_head not in {"Set","Set₀","Set₁","Set₂","Setω","Prop","Prop₁"}:
                continue
            ident = _single_identifier(s.ast.source_bytes, assignment.expr_node)
            if ident and ident in known_term_heads and ident not in data and ident not in s.records:
                out.append(_diag(D, "TSAGDA071", f"known term {ident} is supplied where field {fname} expects a type/sort", s, assignment.line))

    # TSAGDA077: AST-visible type-constructor parameter arity.
    type_params = {
        name: explicit_declaration_parameter_count(s.ast.source_bytes, record.node)
        for name, record in s.ast.records.items()
        if record.node is not None
    }
    type_params.update(
        {
            name: explicit_declaration_parameter_count(s.ast.source_bytes, decl.node)
            for name, decl in s.ast.data.items()
            if decl.node is not None
        }
    )
    for name, sig in s.ast.signatures.items():
        if sig.type_node is None:
            continue
        covered_spans = []
        for app in applications(s.ast.source_bytes, sig.type_node):
            short = app.head.rsplit(".", 1)[-1]
            want = type_params.get(short)
            if want is None:
                continue
            covered_spans.append((app.head_node.start_byte, app.head_node.end_byte, short))
            got = len(app.explicit_args)
            if got != want:
                out.append(_diag(D, "TSAGDA077", f"type constructor {short} has {want} visible parameters but use supplies {got}", s, app.head_node.start_point[0] + 1, app.head_node.start_point[1] + 1, severity="warning", confidence="medium"))
        tokens = significant_tokens(s.ast.source_bytes, sig.type_node)
        for token in tokens:
            short = token.text.rsplit(".", 1)[-1]
            want = type_params.get(short)
            if not want:
                continue
            if any(start <= token.start_byte < end and item == short for start, end, item in covered_spans):
                continue
            out.append(_diag(D, "TSAGDA077", f"type constructor {short} has {want} visible parameters but is used bare", s, token.line, token.column, severity="warning", confidence="medium"))

    # TSAGDA113: high-confidence single-identifier RHS scope check.
    global_names = set(checker.exported_names(s)) | set(data) | set(ctors) | set(imported)
    for name, clause_items in s.ast.clauses.items():
        for clause in clause_items:
            if clause.rhs_node is None:
                continue
            rhs_tokens = [
                token for token in significant_tokens(s.ast.source_bytes, clause.rhs_node)
                if token.node_type in {"qid", "id"}
            ]
            all_rhs_tokens = significant_tokens(s.ast.source_bytes, clause.rhs_node)
            if len(rhs_tokens) != 1 or len(all_rhs_tokens) != 1:
                continue
            ident = rhs_tokens[0].text
            lhs_names = {
                token.text
                for token in significant_tokens(s.ast.source_bytes, clause.lhs_node)
                if token.node_type in {"qid", "id", "bid"}
            }
            if ident not in lhs_names and ident not in global_names and ident not in {"Set","Nat","Bool","String","refl","tt"}:
                out.append(_diag(D, "TSAGDA113", f"RHS identifier {ident} has no evident local or top-level binding", s, clause.line, rhs_tokens[0].column, severity="warning", confidence="medium"))

    # TSAGDA104: equality proof used as whole RHS for a non-equality target.
    for name, cs in clauses.items():
        sig = s.signatures.get(name)
        if not sig or "≡" in sig.type_text: continue
        for line, lhs, rhs in cs:
            if rhs in eq_shapes:
                out.append(_diag(D, "TSAGDA104", f"equality proof {rhs} is used as the value of non-equality result {name}", s, line))

    # TSAGDA114/115: AST clause result and duplicate signature checks.
    for name, occurrences in s.ast.signature_occurrences.items():
        if len(occurrences) <= 1:
            continue
        shapes = []
        for occurrence in occurrences:
            tokens = tuple(
                token.text
                for token in significant_tokens(s.ast.source_bytes, occurrence.type_node)
            ) if occurrence.type_node is not None else ()
            shapes.append(tokens)
        if len(set(shapes)) > 1:
            out.append(_diag(D, "TSAGDA115", f"{name} has multiple incompatible top-level signatures", s, occurrences[-1].line))

    for name, clause_items in s.ast.clauses.items():
        sig = s.ast.signatures.get(name)
        if sig is None or sig.type_node is None:
            continue
        expected = terminal_head(shape_from_node(s.ast.source_bytes, sig.type_node))
        for clause in clause_items:
            if clause.rhs_node is None:
                continue
            view = application_view(s.ast.source_bytes, clause.rhs_node)
            if view is None:
                continue
            ctor = ctors.get(view.head.rsplit(".", 1)[-1])
            if ctor is not None and expected and ctor.datatype != expected.rsplit(".", 1)[-1]:
                out.append(_diag(D, "TSAGDA114", f"clause result constructor head disagrees with declared result head {expected}", s, clause.line))

    # TSAGDA154: ambiguous opened mixfix/operator.
    for n, mods in visible.items():
        if "_" in n and len(set(mods)) > 1:
            out.append(_diag(D, "TSAGDA154", f"operator {n} is provided by multiple open imports", s, 1, severity="warning", confidence="medium"))

    # TSAGDA171/175 aliases for high-value metavariable classes.
    for d in list(out):
        if d.code == "TSAGDA002":
            out.append(_diag(D, "TSAGDA171", d.message, s, d.line, d.column, d.hint))
        if d.code == "TSAGDA012":
            out.append(_diag(D, "TSAGDA175", d.message, s, d.line, d.column, d.hint))

    # TSAGDA185: public re-export collision; TSAGDA186: stale import modifiers.
    public_exports = {}
    for line, is_open, module, alias, directives in import_lines:
        if not is_open or not any(d.kind == "public" for d in directives): continue
        target = imported.get(alias)
        if not target: continue
        names = set(checker.exported_names(target))
        for n in names:
            public_exports.setdefault(n, []).append(module)
    for n, mods in public_exports.items():
        if len(set(mods)) > 1:
            out.append(_diag(D, "TSAGDA185", f"public re-export {n} collides across {', '.join(sorted(set(mods)))}", s, 1, severity="warning", confidence="medium"))

    for d in list(out):
        if d.code in {"TSAGDA023", "TSAGDA024", "TSAGDA025"}:
            out.append(_diag(D, "TSAGDA186", f"stale import modifier: {d.message}", s, d.line, d.column, d.hint, severity="warning", confidence="high"))

    # TSAGDA207: explicit forward/backward bidi endpoints should reverse.
    if "bidi" in s.module_name.lower():
        forward = next(
            (
                sig for name, sig in s.ast.signatures.items()
                if any(word in name.lower() for word in ("forward", "totarget", "encode"))
            ),
            None,
        )
        backward = next(
            (
                sig for name, sig in s.ast.signatures.items()
                if any(word in name.lower() for word in ("backward", "tosource", "decode", "inverse"))
            ),
            None,
        )
        if (
            forward is not None and backward is not None
            and forward.type_node is not None and backward.type_node is not None
        ):
            fshape = shape_from_node(s.ast.source_bytes, forward.type_node)
            bshape = shape_from_node(s.ast.source_bytes, backward.type_node)
            if isinstance(fshape, PiShape) and isinstance(bshape, PiShape) and fshape.domains and bshape.domains:
                fa = terminal_head(fshape.domains[0].head)
                fb = terminal_head(fshape.codomain)
                ba = terminal_head(bshape.domains[0].head)
                bb = terminal_head(bshape.codomain)
                if all((fa, fb, ba, bb)) and (fa != bb or fb != ba):
                    out.append(_diag(D, "TSAGDA207", f"bidi forward/backward outer heads are not reversed: {fa}->{fb} versus {ba}->{bb}", s, min(forward.line, backward.line), severity="warning", confidence="medium"))


    return out

def api_snapshot(checker):
    modules = {}
    for path in checker.repository_agda_files():
        try:
            rel = path.relative_to(checker.root)
        except ValueError:
            continue
        try:
            s = checker.parse_summary(path)
        except Exception:
            continue
        constructors = {
            cname: {
                "datatype": dname,
                "arity": (
                    explicit_arity(shape_from_node(s.ast.source_bytes, ctor.type_node))
                    if ctor.type_node is not None else 0
                ),
            }
            for dname, decl in s.ast.data.items()
            for cname, ctor in decl.constructors.items()
        }
        signatures = {
            name: {
                "text": sig.type_text,
                "explicit_arity": (
                    explicit_arity(shape_from_node(s.ast.source_bytes, sig.type_node))
                    if sig.type_node is not None else 0
                ),
                "result_head": (
                    terminal_head(shape_from_node(s.ast.source_bytes, sig.type_node))
                    if sig.type_node is not None else None
                ),
            }
            for name, sig in s.ast.signatures.items()
        }
        modules[s.module_name] = {
            "path": str(rel),
            "exports": sorted(set(checker.exported_names(s)) | set(constructors)),
            "signatures": signatures,
            "records": {k: {"fields": sorted(r.fields)} for k, r in s.records.items()},
            "projections": {f: rname for rname, r in s.records.items() for f in r.fields},
            "constructors": constructors,
        }
    return {"version": 2, "modules": modules}

def api_drift(checker, baseline, D):
    out = []; now = api_snapshot(checker).get("modules", {})
    for mod, old in baseline.get("modules", {}).items():
        cur = now.get(mod); path = checker.module_path(mod)
        if not cur or not path.exists(): continue
        s = checker.parse_summary(path)
        for name in sorted(set(old.get("exports", ())) - set(cur.get("exports", ()))):
            out.append(_diag(D, "TSAGDA180", f"exported name {name} disappeared from {mod}", s, 1))
        for rn, rold in old.get("records", {}).items():
            rnew = cur.get("records", {}).get(rn)
            if rnew:
                for fn in sorted(set(rold.get("fields", ())) - set(rnew.get("fields", ()))):
                    out.append(_diag(D, "TSAGDA181", f"record field {rn}.{fn} disappeared", s, 1))
        for cn, cold in old.get("constructors", {}).items():
            cnew = cur.get("constructors", {}).get(cn)
            if cnew and cnew.get("arity") != cold.get("arity"):
                out.append(_diag(D, "TSAGDA182", f"constructor {cn} arity changed {cold.get('arity')} -> {cnew.get('arity')}", s, 1))
        for fn, fold in old.get("signatures", {}).items():
            fnew = cur.get("signatures", {}).get(fn)
            if not fnew:
                continue
            old_arity = fold.get("explicit_arity") if isinstance(fold, dict) else None
            new_arity = fnew.get("explicit_arity") if isinstance(fnew, dict) else None
            if old_arity is not None and new_arity is not None and old_arity != new_arity:
                out.append(_diag(D, "TSAGDA183", f"function {fn} arity changed {old_arity} -> {new_arity}", s, 1))
        for proj, old_owner in old.get("projections", {}).items():
            new_owner = cur.get("projections", {}).get(proj)
            if new_owner and new_owner != old_owner:
                out.append(_diag(D, "TSAGDA184", f"projection {proj} moved receiver record {old_owner} -> {new_owner}", s, 1))
    return out

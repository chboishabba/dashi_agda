from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, Sequence, Tuple

from .ast_index import AstToken, significant_tokens


class Shape:
    pass


@dataclass(frozen=True)
class UnknownShape(Shape):
    pass


@dataclass(frozen=True)
class MetaShape(Shape):
    pass


@dataclass(frozen=True)
class SortShape(Shape):
    name: str


@dataclass(frozen=True)
class HeadShape(Shape):
    head: str
    args: Tuple[str, ...] = ()


@dataclass(frozen=True)
class PiShape(Shape):
    domains: Tuple["DomainShape", ...]
    codomain: Shape


@dataclass(frozen=True)
class EqualityShape(Shape):
    lhs: Shape
    rhs: Shape


@dataclass(frozen=True)
class LiteralShape(Shape):
    kind: str
    text: str


@dataclass(frozen=True)
class DomainShape:
    visibility: str
    head: Shape


_OPEN = {"(": ")", "{": "}", "{{": "}}", "⦃": "⦄", "[": "]"}
_CLOSE = {value: key for key, value in _OPEN.items()}
_SORT_TEXT = {"Set", "Set₀", "Set₁", "Set₂", "Setω", "Prop", "Prop₁"}


def _visibility(tokens: Sequence[AstToken]) -> str:
    if not tokens:
        return "explicit"
    first = tokens[0].text
    if first in {"{{", "⦃"}:
        return "instance"
    if first == "{":
        return "implicit"
    return "explicit"


def split_top_level(tokens: Sequence[AstToken], separators: set[str]) -> List[List[AstToken]]:
    parts: List[List[AstToken]] = [[]]
    stack: List[str] = []
    for token in tokens:
        text = token.text
        if text in _OPEN:
            stack.append(text)
            parts[-1].append(token)
            continue
        if text in _CLOSE:
            if stack and stack[-1] == _CLOSE[text]:
                stack.pop()
            parts[-1].append(token)
            continue
        if not stack and text in separators:
            parts.append([])
            continue
        parts[-1].append(token)
    return parts


def _trim_delimiters(tokens: Sequence[AstToken]) -> List[AstToken]:
    result = list(tokens)
    changed = True
    while changed and len(result) >= 2:
        changed = False
        first, last = result[0].text, result[-1].text
        if first in _OPEN and _OPEN[first] == last:
            depth = 0
            balanced = True
            for i, tok in enumerate(result):
                if tok.text == first:
                    depth += 1
                elif tok.text == last:
                    depth -= 1
                    if depth == 0 and i != len(result) - 1:
                        balanced = False
                        break
            if balanced and depth == 0:
                result = result[1:-1]
                changed = True
    return result


def rigid_head_from_tokens(tokens: Sequence[AstToken]) -> Shape:
    items = _trim_delimiters(tokens)
    if not items:
        return UnknownShape()
    if len(items) == 1 and items[0].text == "_":
        return MetaShape()
    first = items[0]
    if first.text in _SORT_TEXT or first.node_type in {"SetN", "PropN"}:
        return SortShape(first.text)
    if first.node_type == "literal":
        text = first.text
        kind = "string" if text.startswith('"') else "number"
        return LiteralShape(kind, text)

    # In a typed binder segment such as '(x : A)', the type begins after the
    # top-level colon. Do not infer from the binder name.
    colon_parts = split_top_level(items, {":"})
    if len(colon_parts) == 2:
        return rigid_head_from_tokens(colon_parts[1])

    # Prefer syntax-tree identifiers rather than interpreting arbitrary text.
    names = [
        tok.text
        for tok in items
        if tok.node_type in {"qid", "id", "data_name", "record_name", "field_name"}
        and tok.text not in {"λ", "∀"}
    ]
    if not names:
        # Anonymous grammar leaves such as builtin Nat may still appear as raw
        # tokens, but only accept identifier-looking leaves conservatively.
        for tok in items:
            text = tok.text
            if text and not any(ch.isspace() for ch in text) and text not in _OPEN and text not in _CLOSE:
                if text not in {"→", "->", ":", "=", ",", ";"}:
                    return HeadShape(text)
        return UnknownShape()
    return HeadShape(names[0], tuple(names[1:]))


def _group_end(tokens: Sequence[AstToken], start: int) -> Optional[int]:
    opener = tokens[start].text
    closer = _OPEN.get(opener)
    if closer is None:
        return None
    stack = [opener]
    for index in range(start + 1, len(tokens)):
        text = tokens[index].text
        if text in _OPEN:
            stack.append(text)
            continue
        if text in _CLOSE and stack and _CLOSE[text] == stack[-1]:
            stack.pop()
            if not stack:
                return index
    return None


def _binder_multiplicity(
    tokens: Sequence[AstToken],
    *,
    forall_context: bool = False,
) -> int:
    """Count binders represented by one syntactic group.

    Typed groups such as (A B : Set) bind two names. Inside an explicit
    forall telescope, untyped groups such as p q and {m Δ q} also bind
    each identifier separately. Outside forall an untyped parenthesized
    group remains an ordinary type expression and contributes one domain.
    """
    items = _trim_delimiters(tokens)
    colon_parts = split_top_level(items, {":"})
    if len(colon_parts) == 2:
        names = [
            token
            for token in colon_parts[0]
            if token.node_type in {"id", "bid", "qid", "field_name"}
            and token.text not in {"∀", "_"}
        ]
        return max(1, len(names))

    if forall_context:
        names = [
            token
            for token in items
            if token.node_type in {"id", "bid", "qid", "field_name"}
            and token.text not in {"∀", "_"}
        ]
        if names:
            return len(names)

    return 1


def _domain_shapes_from_segment(tokens: Sequence[AstToken]) -> List[DomainShape]:
    """Expand one arrow-domain segment into its telescope binders."""
    items = list(tokens)
    forall_context = bool(items and items[0].text == "∀")
    while items and items[0].text in {"∀", ","}:
        items.pop(0)
    if not items:
        return []

    groups: List[List[AstToken]] = []
    residual: List[AstToken] = []
    index = 0
    while index < len(items):
        token = items[index]
        if token.text in _OPEN:
            end = _group_end(items, index)
            if end is not None:
                if residual:
                    groups.append(residual)
                    residual = []
                groups.append(items[index:end + 1])
                index = end + 1
                continue
        residual.append(token)
        index += 1
    if residual:
        groups.append(residual)

    domains: List[DomainShape] = []
    for group in groups:
        trimmed = [token for token in group if token.text not in {",", "∀"}]
        if not trimmed:
            continue
        multiplicity = _binder_multiplicity(
            trimmed,
            forall_context=forall_context,
        )
        colon_parts = split_top_level(_trim_delimiters(trimmed), {":"})
        if forall_context and len(colon_parts) != 2:
            head = UnknownShape()
        else:
            head = rigid_head_from_tokens(trimmed)
        domain = DomainShape(_visibility(trimmed), head)
        domains.extend(domain for _ in range(multiplicity))
    return domains

def shape_from_tokens(tokens: Sequence[AstToken]) -> Shape:
    items = _trim_delimiters(tokens)
    if not items:
        return UnknownShape()

    # Parse top-level function arrows before interpreting equality in the
    # codomain. This preserves the Agda telescope/result structure.
    arrows = split_top_level(items, {"→", "->"})
    if len(arrows) > 1:
        domains: List[DomainShape] = []
        for segment in arrows[:-1]:
            domains.extend(_domain_shapes_from_segment(segment))
        return PiShape(tuple(domains), shape_from_tokens(arrows[-1]))

    eq_parts = split_top_level(items, {"≡"})
    if len(eq_parts) == 2:
        return EqualityShape(
            rigid_head_from_tokens(eq_parts[0]),
            rigid_head_from_tokens(eq_parts[1]),
        )

    return rigid_head_from_tokens(items)


def shape_from_node(source_bytes: bytes, node) -> Shape:
    if node is None:
        return UnknownShape()
    return shape_from_tokens(significant_tokens(source_bytes, node))


def terminal_shape(shape: Shape) -> Shape:
    while isinstance(shape, PiShape):
        shape = shape.codomain
    return shape


def terminal_head(shape: Shape) -> Optional[str]:
    shape = terminal_shape(shape)
    if isinstance(shape, HeadShape):
        return shape.head
    if isinstance(shape, SortShape):
        return shape.name
    if isinstance(shape, LiteralShape):
        return shape.kind
    return None


def explicit_arity(shape: Shape) -> int:
    if not isinstance(shape, PiShape):
        return 0
    return sum(1 for domain in shape.domains if domain.visibility == "explicit")


def all_arity(shape: Shape) -> int:
    if not isinstance(shape, PiShape):
        return 0
    return len(shape.domains)


def equality_shape(shape: Shape) -> Optional[EqualityShape]:
    shape = terminal_shape(shape)
    return shape if isinstance(shape, EqualityShape) else None


def compatible_rigid_heads(left: Shape, right: Shape) -> Optional[bool]:
    """Return False only for a statically rigid mismatch; None means unknown."""
    left = terminal_shape(left)
    right = terminal_shape(right)
    if isinstance(left, SortShape) and isinstance(right, SortShape):
        return left.name == right.name
    if isinstance(left, HeadShape) and isinstance(right, HeadShape):
        return left.head == right.head
    if isinstance(left, LiteralShape) and isinstance(right, LiteralShape):
        return left.kind == right.kind
    if isinstance(left, MetaShape) or isinstance(right, MetaShape):
        return None
    return None

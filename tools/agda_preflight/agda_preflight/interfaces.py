from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Optional, Sequence, Set, Tuple

from .ast_index import explicit_declaration_parameter_count
from .shapes import explicit_arity, shape_from_node, terminal_head


@dataclass(frozen=True)
class InterfaceDirective:
    kind: str
    names: Tuple[str, ...]
    renamings: Tuple[Tuple[str, str], ...]


@dataclass(frozen=True)
class PublicReexport:
    module: str
    directives: Tuple[InterfaceDirective, ...]


@dataclass(frozen=True)
class InterfaceField:
    name: str
    type_text: str
    terminal_head: Optional[str]
    explicit_arity: int


@dataclass(frozen=True)
class InterfaceRecord:
    name: str
    constructor: Optional[str]
    fields: Tuple[InterfaceField, ...]
    field_surface_complete: bool

    @property
    def field_map(self) -> Dict[str, InterfaceField]:
        return {field.name: field for field in self.fields}


@dataclass(frozen=True)
class InterfaceSignature:
    name: str
    type_text: str
    terminal_head: Optional[str]
    explicit_arity: int


@dataclass(frozen=True)
class ModuleInterface:
    module_name: str
    signatures: Tuple[InterfaceSignature, ...]
    records: Tuple[InterfaceRecord, ...]
    data_constructors: Tuple[Tuple[str, Tuple[str, ...]], ...]
    nested_modules: Tuple[str, ...]
    module_parameter_count: int
    public_reexports: Tuple[PublicReexport, ...]
    resolved_exports: Tuple[str, ...] = ()

    @property
    def signature_map(self) -> Dict[str, InterfaceSignature]:
        return {item.name: item for item in self.signatures}

    @property
    def record_map(self) -> Dict[str, InterfaceRecord]:
        return {item.name: item for item in self.records}

    @property
    def local_exports(self) -> Set[str]:
        names = set(self.signature_map) | set(self.record_map) | set(self.nested_modules)
        for record in self.records:
            names.update(field.name for field in record.fields)
            if record.constructor:
                names.add(record.constructor)
        for datatype, constructors in self.data_constructors:
            names.add(datatype)
            names.update(constructors)
        return names

    @property
    def exports(self) -> Set[str]:
        return set(self.resolved_exports) if self.resolved_exports else self.local_exports


def _directive(item) -> InterfaceDirective:
    return InterfaceDirective(
        kind=item.kind,
        names=tuple(item.names),
        renamings=tuple(tuple(pair) for pair in item.renamings),
    )


def _module_parameter_count(summary) -> int:
    outer = next(
        (
            node
            for node in summary.ast.tree.root_node.named_children
            if node.type == "module"
        ),
        None,
    )
    if outer is None:
        return 0
    return explicit_declaration_parameter_count(
        summary.ast.source_bytes,
        outer,
    )


def interface_from_summary(root: Path, summary) -> ModuleInterface:
    signatures = []
    for name, signature in sorted(summary.ast.signatures.items()):
        shape = (
            shape_from_node(summary.ast.source_bytes, signature.type_node)
            if signature.type_node is not None
            else None
        )
        signatures.append(
            InterfaceSignature(
                name=name,
                type_text=signature.type_text,
                terminal_head=terminal_head(shape) if shape is not None else None,
                explicit_arity=explicit_arity(shape) if shape is not None else 0,
            )
        )

    records = []
    for name, record in sorted(summary.ast.records.items()):
        fields = []
        for field_name, field in sorted(record.fields.items()):
            shape = (
                shape_from_node(summary.ast.source_bytes, field.type_node)
                if field.type_node is not None
                else None
            )
            fields.append(
                InterfaceField(
                    name=field_name,
                    type_text=field.type_text,
                    terminal_head=terminal_head(shape) if shape is not None else None,
                    explicit_arity=explicit_arity(shape) if shape is not None else 0,
                )
            )
        records.append(
            InterfaceRecord(
                name=name,
                constructor=record.constructor,
                fields=tuple(fields),
                field_surface_complete=record.field_surface_complete,
            )
        )

    data_constructors = tuple(
        (
            name,
            tuple(sorted(declaration.constructors)),
        )
        for name, declaration in sorted(summary.ast.data.items())
    )

    public_reexports = []
    seen = set()
    for item in summary.ast.imports:
        if not (item.opened and item.public):
            continue
        key = (
            item.module,
            tuple(
                (
                    directive.kind,
                    tuple(directive.names),
                    tuple(tuple(pair) for pair in directive.renamings),
                )
                for directive in item.directives
            ),
        )
        if key in seen:
            continue
        seen.add(key)
        public_reexports.append(
            PublicReexport(
                module=item.module,
                directives=tuple(_directive(d) for d in item.directives),
            )
        )

    for opened in summary.ast.opens:
        if not opened.public:
            continue
        module = summary.imports.get(opened.target)
        if module is None:
            candidate = root.joinpath(
                *opened.target.split(".")
            ).with_suffix(".agda")
            if candidate.exists():
                module = opened.target
        if module is None:
            continue
        key = (
            module,
            tuple(
                (
                    directive.kind,
                    tuple(directive.names),
                    tuple(tuple(pair) for pair in directive.renamings),
                )
                for directive in opened.directives
            ),
        )
        if key in seen:
            continue
        seen.add(key)
        public_reexports.append(
            PublicReexport(
                module=module,
                directives=tuple(_directive(d) for d in opened.directives),
            )
        )

    return ModuleInterface(
        module_name=summary.module_name,
        signatures=tuple(signatures),
        records=tuple(records),
        data_constructors=data_constructors,
        nested_modules=tuple(sorted(summary.ast.nested_modules)),
        module_parameter_count=_module_parameter_count(summary),
        public_reexports=tuple(
            sorted(
                public_reexports,
                key=lambda item: (
                    item.module,
                    tuple(d.kind for d in item.directives),
                ),
            )
        ),
    )


def _apply_directives(names: Set[str], directives: Sequence[InterfaceDirective]) -> Set[str]:
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


def resolve_interface_exports(
    interfaces: Dict[str, ModuleInterface],
) -> Dict[str, ModuleInterface]:
    memo: Dict[str, Set[str]] = {}

    def resolve(module: str, active: Set[str]) -> Set[str]:
        cached = memo.get(module)
        if cached is not None:
            return set(cached)
        interface = interfaces[module]
        if module in active:
            return interface.local_exports
        nested = set(active)
        nested.add(module)
        exports = interface.local_exports
        for reexport in interface.public_reexports:
            target = interfaces.get(reexport.module)
            if target is None:
                continue
            exports.update(
                _apply_directives(
                    resolve(reexport.module, nested),
                    reexport.directives,
                )
            )
        memo[module] = set(exports)
        return exports

    return {
        module: ModuleInterface(
            module_name=interface.module_name,
            signatures=interface.signatures,
            records=interface.records,
            data_constructors=interface.data_constructors,
            nested_modules=interface.nested_modules,
            module_parameter_count=interface.module_parameter_count,
            public_reexports=interface.public_reexports,
            resolved_exports=tuple(sorted(resolve(module, set()))),
        )
        for module, interface in interfaces.items()
    }

# DASHI Theory Atlas

The theory atlas is a downstream presentation and integration surface. It does not introduce proof-status records, verification booleans, or theorem authority.

## Generate the Yang–Mills critical-path atlas

```bash
python scripts/materialize_dashi_theory_atlas.py
```

This reads `config/dashi-yang-mills-critical-path-atlas.json`, scans Agda declarations under `DASHI/`, derives dependencies and authority states, and writes:

- `artifacts/dashi-yang-mills-critical-path.json`
- `artifacts/dashi-yang-mills-critical-path.svg`

Use validation-only mode in CI:

```bash
python scripts/materialize_dashi_theory_atlas.py --check
```

## Derived states

The generator emits only these mechanically derived states:

- `proved`: a declaration has a definition and no selected open dependency;
- `proved_conditional`: the declaration consumes a named analytic input type or depends on a selected open declaration;
- `source_imported`: the declaration's module matches a configured source-import authority rule;
- `open_analytic`: the declaration is postulated, lacks a definition, or matches a configured open-obligation naming rule;
- `legacy`: the selected card is explicitly outside the critical path.

The atlas configuration may choose declarations, titles, formulas, lanes, source anchors, and explicit graph edges. It cannot directly assert a proof state.

## Claim boundary

Compilation certifies type-correct assembly only. It does not discharge displayed open analytic inputs.

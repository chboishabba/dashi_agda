# DASHI Agda preflight

A deliberately shallow, fast semantic checker for the error classes that are
expensive to discover only after a deep `DASHI/Everything.agda` traversal.

It **does not replace Agda**. Tree-sitter provides the incremental syntax tree;
the preflight layer adds a small symbol/record/type-shape model and an import
DAG. Agda remains the kernel/typechecker and the final source of truth.

The package uses the Tree-sitter 0.25–0.26 runtime line required by
`tree-sitter-agda` 1.3.3's PyCapsule language binding.

## Initial diagnostics

- `TSAGDA000`: tree-sitter syntax error / missing node
- `TSAGDA001`: opened record projection used unapplied where a type is expected
- `TSAGDA002`: projection receiver written as `_` despite a matching named
  record binder in scope
- `TSAGDA003`: simple record-field codomain/kind mismatch (for example
  `Nat -> Top` supplied to a `Nat -> Set` field)

The first two semantic rules are regression-targeted at failures found in
`TriadicEisensteinTransformationTheorem.agda` on 2026-09-23.

## Install

```bash
cd tools/agda_preflight
python -m pip install -e .
```

## Usage

Check one module:

```bash
dashi-agda-preflight --root ../.. \
  ../../DASHI/Physics/Closure/TriadicEisensteinTransformationTheorem.agda
```

Check the reverse-import closure of a changed module:

```bash
dashi-agda-preflight --root ../.. --closure \
  ../../DASHI/Physics/Closure/TriadicEisensteinTransformationTheorem.agda
```

Print the affected-module compile plan without running the semantic checks:

```bash
dashi-agda-preflight --root ../.. --plan \
  ../../DASHI/Physics/Closure/TriadicEisensteinTransformationTheorem.agda
```

Machine-readable diagnostics:

```bash
dashi-agda-preflight --root ../.. --json FILE.agda
```

A recommended edit loop is:

```text
edit
  -> dashi-agda-preflight FILE
  -> agda FILE
  -> dashi-agda-preflight --plan FILE
  -> compile affected frontier in order
  -> DASHI/Everything.agda only at the end
```

## Scope

The checker intentionally only reports mismatches it can establish from cheap
outer type shapes. It should prefer a false negative over a speculative error.
Novel Agda failures should be added as small regression fixtures before a new
rule is generalized.

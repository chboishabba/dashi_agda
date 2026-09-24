# DASHI Agda preflight

A fast, deliberately non-elaborating front-end for Agda. Tree-sitter supplies the
incremental syntax tree; the preflight layer adds module/name resolution,
record/data/function summaries, telescopes, shallow type shapes, structural
proof checks, trust-boundary policy checks, and an import DAG.

It **does not replace Agda**. Agda remains the kernel/typechecker and final source
of truth. The preflight checker should prefer a false negative over pretending
to solve dependent unification.

## Design boundary

The checker may do:

```text
parse
  -> lexical/module scopes
  -> import/open/using/hiding/renaming resolution
  -> exported symbol index
  -> record/data/constructor/projection index
  -> telescope reconstruction
  -> shallow type-shape propagation
  -> bounded substitution/head comparison
  -> structural diagnostics
  -> DASHI trust-boundary diagnostics
  -> reverse-import compile plan
```

The checker must not attempt:

- general dependent unification or metavariable solving;
- arbitrary definitional equality or normalization of recursive functions;
- instance search;
- full universe constraint solving;
- indexed coverage;
- full positivity or termination;
- cubical/path elaboration;
- reflection/macro execution;
- proof validity.

## Current implementation status

The frontend is now **tree-sitter-first and regex-free for Agda syntax parsing**.

The core modules:

```text
checker.py
ast_index.py
shapes.py
rules.py
```

must not use regular expressions to interpret Agda syntax. A regression test
enforces that invariant.

The shallow type-shape layer follows two important soundness rules:

- **Function-arrow structure is parsed before equality in the codomain.** A type
  such as `(x : A) → f x ≡ g x` is represented as a `Pi` whose codomain is an
  `Equality`, not as an equality whose left endpoint accidentally contains
  the telescope.
- **Equality incompatibility requires rigid evidence.** Different arbitrary
  term/function heads are not treated as different types. Hard equality
  diagnostics are reserved for cases such as constructors known to belong to
  different datatypes, or an evident sort-vs-term mismatch.

A single pre-arrow telescope segment may also contain multiple binders, e.g.
`∀ {X} (s : State X) (x : X) → ...`; these are counted individually for
arity diagnostics.

The current implementation has structural AST support for:

- modules, imports, opens, aliases and import directives;
- records, fields, record constructors and record expressions;
- data declarations and constructors;
- signatures, function clauses, telescopes and binder visibility;
- applications with explicit/implicit/instance arguments;
- patterns and simple finite coverage;
- pragmas, fixity declarations and syntax declarations;
- shallow type shapes (`Sort`, `Head`, `Pi`, `Equality`, `Meta`,
  `Literal`, `Unknown`);
- reverse import graphs and semantic API snapshots.

The original motivating failures are now detected structurally:

- unapplied dependent projections such as `Parameter` instead of
  `Parameter M`;
- explicit projection receiver holes such as `Pareto.cost _` when a matching
  record binder is in scope;
- record-adapter kind mismatches such as `Nat → ⊤` being supplied to a
  `Nat → Set` field.

Any future syntax-sensitive diagnostic should extend `ast_index.py` or
`shapes.py`; it should not add source-text parsing to `rules.py`.

### Still intentionally delegated to Agda

The following remain outside the preflight implementation boundary because they
require real elaboration/kernel reasoning rather than shallow structural
analysis:

- dependent unification and metavariable solving;
- arbitrary definitional equality and normalization;
- instance search;
- universe-constraint solving;
- indexed datatype coverage;
- full positivity and termination checking;
- cubical/path elaboration;
- reflection/macro execution;
- proof validity.

## Evidence provenance

Every diagnostic has an explicit minimum evidence layer:

```text
TREE_SITTER
    concrete syntax / source ranges / unambiguous tree structure

DASHI_INDEX
    tree-sitter + DASHI module/record/data/telescope/shape indexes

AGDA_SCOPE
    Agda-resolved scope/elaboration facts such as opens, renamings,
    overloading, mixfix resolution and implicit insertion

AGDA_TYPECHECKER
    full Agda typechecking / kernel evidence
```

The evidence policy is executable, not documentation-only. A structural rule
that requires `AGDA_SCOPE` cannot fail the fast preflight run merely because
`rules.py` emitted an error-shaped suspicion. Without scope evidence it is
downgraded to a warning with:

```text
confidence = insufficient-evidence
evidence = dashi-index
minimum_evidence = agda-scope
evidence_sufficient = false
```

All documented `TSAGDA...` codes must be explicitly classified in
`evidence.py`; an unclassified diagnostic is a programming error.

The current scope-dependent family includes checks whose truth can change after
Agda resolves opens/renamings, overloaded or mixfix names, or dependent local
scope. Examples include:

```text
TSAGDA022  unknown/malformed alias use
TSAGDA024  hiding entry validity across re-export chains
TSAGDA026  rename/open collision
TSAGDA027  ambiguous unqualified open
TSAGDA055  ambiguous opened projection
TSAGDA084  inaccessible-pattern scope
TSAGDA113  apparently unbound RHS identifier
TSAGDA154  ambiguous opened operator
```

### Native Agda scope oracle

Agda itself exposes `--only-scope-checking`. The preflight checker can use it
directly:

```bash
dashi-agda-preflight --agda-scope-check FILE.agda
```

or through pytest:

```bash
pytest --agda-preflight --agda-deps --agda-scope-check --agda-root . \
  DASHI/Everything.agda -vv
```

Use `--agda-bin /path/to/agda` when Agda is not on `PATH`.

This mode is intentionally a **negative oracle**. If Agda successfully
scope-checks a module, diagnostics whose minimum evidence is `AGDA_SCOPE` are
suppressed. If scope checking fails, the backend does not guess which structural
suspicion caused the failure, so those diagnostics remain advisory.

Some superficially similar checks actually require typechecking, not scope
checking. In particular:

```text
TSAGDA041  under-application in a saturated context
TSAGDA076  function used as a type / partial application
```

have minimum evidence `AGDA_TYPECHECKER`; successful scope checking cannot
promote or suppress them.

### Optional Agda scope refinement

Both the CLI and pytest harness accept:

```bash
--agda-scope-command '<command>'
```

The external command receives the absolute Agda file path as its final argument,
unless its argv contains the literal placeholder `{file}`. It returns one JSON
object describing only refinements of already-emitted structural suspicions:

```json
{
  "confirmed": [
    {"code": "TSAGDA113", "line": 42, "column": 7}
  ],
  "suppressed": [
    {"code": "TSAGDA027", "line": 18, "column": 1}
  ]
}
```

A confirmed location is upgraded to `agda-scope` evidence. If its only reason
for being a warning was insufficient evidence, it can regain hard-error status.
A suppressed location is removed. Backend failure, malformed JSON, or missing
confirmation never manufactures evidence and never creates a new hard error.

This interface is intentionally narrower than an Agda reimplementation: an
Agda-aware frontend may resolve ambiguous structural suspicions, while the
actual typechecker remains authoritative for dependent unification,
definitional equality, universes, instances, coverage, termination, positivity,
and proof validity.

Pytest reports evidence-deferred findings separately:

```text
Agda preflight
modules passed: ...
modules failed: ...
errors: ...
warnings: ...
deferred for stronger evidence: ...
```

## Diagnostic catalogue

Diagnostics are grouped by capability. Some families are exact/high-confidence;
heuristic families are emitted as warnings.

### Syntax / declaration structure

- `TSAGDA000` tree-sitter syntax error / missing node
- `TSAGDA004` module declaration disagrees with filesystem path
- `TSAGDA005` duplicate top-level declaration
- `TSAGDA006` duplicate record field
- `TSAGDA007` duplicate constructor
- `TSAGDA008` declaration signature without an evident defining clause
- `TSAGDA009` defining clause without an evident signature
- `TSAGDA010` duplicate identical function clause
- `TSAGDA011` structurally suspicious/dangling block
- `TSAGDA012` interaction hole `{!! !!}` / `?`
- `TSAGDA013` explicit underscore in an exported declaration/signature

### Modules / imports / names

- `TSAGDA020` imported repository module does not exist
- `TSAGDA021` unknown qualified symbol on a known module alias
- `TSAGDA022` malformed/unknown import alias use
- `TSAGDA023` unknown symbol in `using (...)`
- `TSAGDA024` unknown symbol in `hiding (...)`
- `TSAGDA025` unknown renaming source
- `TSAGDA026` open/renaming collision
- `TSAGDA027` ambiguous unqualified exported name from multiple opens
- `TSAGDA028` conflicting aliases for imports
- `TSAGDA029` repository import cycle
- `TSAGDA030` module identity/path collision

### Telescopes / calls / arity

- `TSAGDA040` too many explicit arguments for a statically-known head
- `TSAGDA041` too few explicit arguments in a syntactically saturated context
- `TSAGDA042` named implicit argument not present in telescope
- `TSAGDA043` obvious explicit/implicit visibility mismatch
- `TSAGDA044` lambda binder count incompatible with expected Pi shape
- `TSAGDA045` definition-clause argument count disagrees with declaration
- `TSAGDA046` constructor application arity mismatch
- `TSAGDA047` record constructor arity mismatch
- `TSAGDA048` parameterized-module application arity mismatch
- `TSAGDA049` projection over/under-application

### Projections

- `TSAGDA001` opened type-valued projection used unapplied as a type
- `TSAGDA002` projection receiver written as `_` despite a matching binder
- `TSAGDA050` projection receiver has a visibly incompatible record head
- `TSAGDA051` projection receives a known type where a record value is expected
- `TSAGDA052` projection receiver is visibly missing
- `TSAGDA053` projection is visibly over-applied
- `TSAGDA054` projection does not belong to the inferred receiver record
- `TSAGDA055` ambiguous opened projection
- `TSAGDA056` dependent projection is used before required record parameters

### Record construction / adapters

- `TSAGDA060` unknown field in record expression
- `TSAGDA061` duplicate field assignment
- `TSAGDA062` statically-known mandatory field missing
- `TSAGDA063` record expression targets visibly wrong known record
- `TSAGDA064` record-field lambda/telescope shape mismatch
- `TSAGDA003` / `TSAGDA065` terminal codomain/kind mismatch
- `TSAGDA066` record-field result head mismatch
- `TSAGDA067` source projection incompatible with target field
- `TSAGDA068` constructor does not construct expected record

### Shallow type shapes

The checker uses a deliberately small outer-shape language:
`Unknown`, `Meta`, `Sort`, `Head`, `Pi`, `Equality`, and `Literal`.
Only bounded head comparison/substitution is performed.

- `TSAGDA070` type/sort supplied where a term is structurally required
- `TSAGDA071` term supplied where a type/sort is structurally required
- `TSAGDA072` obvious result type-head mismatch
- `TSAGDA073` obvious argument type-head mismatch
- `TSAGDA074` literal incompatible with expected outer head
- `TSAGDA075` datatype constructor belongs to the wrong datatype
- `TSAGDA076` known function used as a type without enough application
- `TSAGDA077` known type constructor over/under-applied
- `TSAGDA078` sort used as an ordinary value
- `TSAGDA079` known non-function applied as a function

### Patterns / finite coverage

These checks are intentionally restricted to simple non-indexed datatypes.

- `TSAGDA080` unknown constructor in pattern
- `TSAGDA081` pattern constructor belongs to visibly wrong datatype
- `TSAGDA082` constructor-pattern arity mismatch
- `TSAGDA083` repeated binder in a linear pattern
- `TSAGDA084` suspicious inaccessible/dot-pattern name
- `TSAGDA085` absurd pattern on a visibly inhabited simple datatype
- `TSAGDA086` absurd lambda on a visibly inhabited simple datatype
- `TSAGDA087` trivial missing finite constructor case
- `TSAGDA088` clause visibly unreachable after catch-all
- `TSAGDA089` duplicate constructor branch

### Equality combinator structure

These do not prove equality; they only reject statically incompatible endpoint
shapes.

- `TSAGDA100` `refl` against visibly different rigid heads
- `TSAGDA101` `sym` endpoint shape mismatch
- `TSAGDA102` `trans` intermediate endpoint mismatch
- `TSAGDA103` `cong` structurally incompatible function/result
- `TSAGDA104` known equality proof supplied to a visibly non-equality consumer
- `TSAGDA105` equality endpoints have visibly incompatible rigid type heads

### Clause / scope checks

- `TSAGDA110` clause has incompatible LHS binder count
- `TSAGDA111` obvious visibility mismatch between clause and signature
- `TSAGDA112` named implicit pattern does not exist in signature
- `TSAGDA113` RHS uses a visibly unbound local identifier
- `TSAGDA114` clause name/result head incompatible with declaration
- `TSAGDA115` multiple incompatible signatures for one declaration

### Universe / declaration sanity

These are bounded structural checks, not universe solving.

- `TSAGDA120` field type resolves to a known term rather than a type head
- `TSAGDA121` constructor result resolves to a known term rather than datatype
- `TSAGDA122` constructor visibly returns another datatype
- `TSAGDA123` Set-valued projection declaration resolves to a term head

### Positivity / termination heuristics

- `TSAGDA130` obvious negative recursive occurrence
- `TSAGDA131` obvious recursive occurrence under a contravariant arrow
- `TSAGDA140` recursive call repeats identical arguments
- `TSAGDA141` obviously increasing recursive argument
- `TSAGDA142` no visibly smaller recursive argument found
- `TSAGDA143` proof-critical code uses a termination-bypass pragma

The termination family is warning-only.

### Fixity / syntax declarations

- `TSAGDA150` fixity declaration references an unknown symbol
- `TSAGDA151` duplicate/conflicting fixity
- `TSAGDA152` mixfix hole count mismatch
- `TSAGDA153` syntax declaration references unknown symbol
- `TSAGDA154` ambiguous opened operator

### Trust-boundary / unsafe escape hatches

These are policy diagnostics rather than Agda errors.

- `TSAGDA160` postulate in a configured proof-critical subtree
- `TSAGDA161` `TERMINATING`
- `TSAGDA162` `NON_TERMINATING`
- `TSAGDA163` `NO_POSITIVITY_CHECK`
- `TSAGDA164` unsolved-meta allowance or policy violation
- `TSAGDA165` unsafe/suspicious OPTIONS pragma
- `TSAGDA166` foreign/compile pragma names an unknown declaration

### Metavariable / hole risk

- `TSAGDA170` `_` in exported result type
- `TSAGDA171` projection receiver meta despite an available receiver
- `TSAGDA172` `_` as a record-field value
- `TSAGDA173` `_` in theorem equality endpoint
- `TSAGDA174` `_` in a module parameter/application
- `TSAGDA175` unresolved interaction hole

### Cross-module API drift

The persistent index records exported names, telescopes, fields, constructors and
fixities by source hash. Comparing an older summary with the live summary can
report:

- `TSAGDA180` imported/exported name disappeared
- `TSAGDA181` imported record field disappeared/changed
- `TSAGDA182` constructor arity changed
- `TSAGDA183` function telescope changed incompatibly
- `TSAGDA184` projection receiver record changed
- `TSAGDA185` public re-export collision
- `TSAGDA186` stale `using/hiding/renaming` entry

### DASHI-specific trust/architecture rules

- `TSAGDA200` gate/receipt adapter leaves a type where a witness is structurally expected
- `TSAGDA201` proof-critical record contains a raw metavariable
- `TSAGDA202` theorem/receipt endpoint is only postulated
- `TSAGDA203` agreement proposition is visibly weakened to unconstrained `Set`
- `TSAGDA204` an `Exact` module exports holes/metas/postulates
- `TSAGDA205` proof-critical closure imports a configured obstruction/assumption module
- `TSAGDA206` same-carrier adapter visibly switches carrier family
- `TSAGDA207` bidi source/target outer shapes disagree
- `TSAGDA208` factor-through/admissibility bridge visibly uses another carrier family

## Pytest integration

The package registers a native pytest plugin through the standard `pytest11`
entry point. Pytest is only the execution/progress harness; the semantic engine
remains `Checker`.

Install the test extra:

```bash
python -m pip install -e 'tools/agda_preflight[test]'
```

Check one module as one pytest item:

```bash
pytest --agda-preflight --agda-root . \
  DASHI/Physics/Closure/TriadicEisensteinTransformationTheorem.agda -vv
```

Use normal pytest verbosity for detailed progress. Each Agda module is a native
pytest item, so `-vv` shows the module currently being checked and pytest's
ordinary completed-item percentage.

For an aggregate such as `DASHI/Everything.agda`, collect its recursive import
DAG in **dependency-first order**:

```bash
pytest --agda-preflight --agda-deps --agda-root . \
  DASHI/Everything.agda -vv
```

From the repository root, the equivalent convenience runner is:

```bash
scripts/check_agda_preflight_pytest.sh
```

Override the aggregate root with `AGDA_PREFLIGHT_TARGET`, and pass any extra pytest arguments through directly, for example:

```bash
AGDA_PREFLIGHT_TARGET=DASHI/Physics/Closure/TriadicEisensteinTransformationTheorem.agda \
  scripts/check_agda_preflight_pytest.sh -k Eisenstein -n auto
```

This is the preferred replacement for an opaque one-shot preflight of
`Everything.agda`: imported leaves are checked first and
`DASHI.Everything` is checked last.

For the opposite workflow—"this leaf changed; which consumers are affected?"—
use the reverse-import closure:

```bash
pytest --agda-preflight --agda-closure --agda-root . \
  DASHI/Physics/Closure/TriadicEisensteinTransformationTheorem.agda -vv
```

Both modes can be combined. Duplicate modules are collected only once.

Normal pytest selection works on module item names:

```bash
pytest --agda-preflight --agda-deps --agda-root . \
  DASHI/Everything.agda -k Eisenstein -vv
```

Parallel execution is available through `pytest-xdist`:

```bash
pytest --agda-preflight --agda-deps --agda-root . \
  DASHI/Everything.agda -n auto -vv
```

Warnings remain non-fatal and are surfaced through pytest's warning reporting.
Use:

```bash
--agda-errors-only
```

to suppress advisory warning text while retaining hard structural failures.

Every module report also carries the complete structured diagnostic list in
pytest `user_properties`, so JUnit/CI integrations can preserve
`TSAGDA...` diagnostics without scraping terminal text.

The terminal summary adds:

```text
Agda preflight
modules passed: ...
modules failed: ...
errors: ...
warnings: ...
```

No timing/ETA model is maintained; progress is intentionally delegated to
pytest's normal item collection and reporting.

Scope refinement can be enabled in the same run, for example:

```bash
pytest --agda-preflight --agda-deps --agda-root . \
  --agda-scope-command 'my-agda-scope-wrapper {file}' \
  DASHI/Everything.agda -vv
```

## CLI

Install:

```bash
cd tools/agda_preflight
python -m pip install -e .
```

Check one module:

```bash
dashi-agda-preflight --root ../.. FILE.agda
```

Check the reverse-import closure:

```bash
dashi-agda-preflight --root ../.. --closure FILE.agda
```

Print the affected compile frontier:

```bash
dashi-agda-preflight --root ../.. --plan FILE.agda
```

Machine-readable diagnostics:

```bash
dashi-agda-preflight --root ../.. --json FILE.agda
```

The intended edit loop is:

```text
edit
  -> preflight changed files
  -> fix high-confidence structural failures
  -> compile the nearest affected Agda frontier
  -> feed novel Agda failures back as regression fixtures
  -> run DASHI/Everything.agda only after the frontier is clean
```

## Engineering policy

Every new diagnostic should have:

1. a minimal failing fixture;
2. a nearby valid fixture;
3. a confidence classification;
4. a documented boundary describing what it does not infer.

The preflight checker is an error firewall, not a second theorem prover.

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

## Interactive incremental workflow

The production-facing hot path is now `dashi-agda`, not pytest:

```bash
dashi-agda diagnose DASHI/Biology/Everything.agda --profile
dashi-agda next-error DASHI/Biology/Everything.agda --require-fix --json
dashi-agda benchmark DASHI/Biology/Everything.agda --runs 7
```

`diagnose` never invokes Agda. It uses a persistent SQLite/WAL source index
under `.cache/agda_preflight/source-index.sqlite3` by default. The index stores
module identity, source freshness/hash, direct import edges, dependency
fingerprints and cached structural diagnostics.

A warm unchanged rollup request performs:

```text
SQLite open
  -> indexed dependency-closure query
  -> stat closure files
  -> return cached diagnostics
```

and the required performance invariant is:

```text
files_parsed = 0
checker_instances = 0
```

If a source file changes, its structural public-API fingerprint is recomputed
from exported signatures, record/data schemas, nested modules and explicit
public re-export directives. Importers depend on that API fingerprint rather
than the dependency's raw source hash. An implementation-only edit therefore
reparses the leaf while reusing importer diagnostics; exported API changes
still invalidate the affected importer chain.

Every interactive request has request-local telemetry. JSON output includes
per-stage milliseconds and counts such as:

```text
request.total
db.open
db.schema
closure.lookup
source.stat
source.read
source.hash
parse.tree_sitter
diagnostics.local
fixes.generate
semantic.catalog_lookup

modules_in_closure
files_stat
files_parsed
dirty_modules
modules_cached
diagnostics_cached
diagnostics_recomputed
semantic_snapshot_hits
semantic_snapshot_misses
```

`dashi-agda benchmark` measures a cold temporary-index bootstrap separately
from repeated warm requests and reports min/p50/p95/max warm latency plus the
warm parse-count invariant.

Diagnostics can also carry structured repair metadata:

```text
root_cause
explanation
expected
found
fixes[]
  title
  applicability = machine_safe | likely | speculative
  rationale
  validation = structural | scope | typecheck
  edits[]
```

The current fix-enrichment layer covers high-value projection and record-field
failures without weakening the diagnostic rules themselves.

Every diagnostic also has a stable worktree-local ID. Agent workflows can ask
for the highest-priority actionable error and, where an exact edit span exists,
apply it explicitly:

```bash
dashi-agda next-error DASHI/Biology/Everything.agda --require-fix --json

dashi-agda apply-fix DASHI/Biology/Everything.agda <diagnostic-id> \
  --fix 0 \
  --allow-likely
```

`machine_safe` edits may be applied directly. `likely` edits require the
explicit `--allow-likely` gate. `speculative` fixes are never machine-applied.
After an edit, `apply-fix` immediately re-runs structural diagnosis through
the persistent index and reports whether the original diagnostic ID vanished.
It does not invoke Agda.

The benchmark command is also an executable performance gate. Defaults are:

```text
cold bootstrap <= 60,000 ms
warm p95      <= 10,000 ms
every warm run parses zero files
```

A benchmark exits nonzero if any of those conditions fail.

### Last-known-good semantic catalog

The source index can optionally join against the existing `agda2lean`
SQLite catalog:

```bash
dashi-agda diagnose DASHI/Biology/Everything.agda \
  --semantic-catalog /path/to/agda2lean/catalog.sqlite \
  --json
```

This exposes existing semantic module object hashes, declaration counts and
term counts without invoking Agda. The current `agda2lean` schema does not yet
store the source SHA that produced each semantic object, so these hits are
reported with:

```text
freshness = unknown
```

A catalog hit must therefore be treated as a last-known semantic snapshot, not
proof that the current source is type-valid. The cross-repo follow-up is to
persist the checked source hash in `agda2lean` so freshness can be decided
exactly.

Pytest remains the regression/full-audit surface for the checker itself; it is
not the normal agent runtime.

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


Inspect the live policy matrix without reading source:

```bash
dashi-agda-evidence
dashi-agda-evidence --level agda-scope
dashi-agda-evidence --level agda-typechecker --json
```

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

### Aggregate scope refinement

When pytest is collecting a dependency closure with `--agda-deps` and
`--agda-auto-refine`, scope refinement is closure-aware rather than strictly
per-module.

The collector first probes the selected aggregate root. If that scope-check
succeeds, every module in its collected dependency closure is marked as having
`AGDA_SCOPE` evidence. If it fails, the collector recursively probes only the
direct imported subtrees that remain unresolved:

```text
aggregate root
  success -> certify whole closure
  failure
    -> probe imported subtree roots
         success -> certify that subtree
         failure -> descend again
```

Successful subtrees are cached, shared DAG dependencies are not re-probed, and
failed frontier modules are cached so individual pytest items do not repeat the
same failed scope process.

For a shadow-tree or wrapper-based Agda environment, use an exit-code scope
runner:

```bash
pytest --agda-preflight --agda-deps \
  --agda-auto-refine=scope \
  --agda-scope-runner 'scripts/run-shadow-scope.sh {file}' \
  --agda-root . DASHI/Everything.agda -vv
```

The runner command may contain the literal `{file}`; otherwise the absolute
module path is appended. Exit status 0 certifies scope success. Nonzero status
leaves the structural scope findings deferred. This protocol is intentionally
different from `--agda-scope-command`, whose command must emit precise JSON
confirmation/suppression locations.

This is especially useful when the real Agda environment lives in a reusable
shadow tree or Nix toolchain. The preflight package remains generic while the
runner owns synchronization, library/include paths, resource guards and the
concrete Agda version.

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

### Aggregate full-typecheck refinement

When pytest runs with `--agda-deps --agda-auto-refine=typecheck`, full
typechecking uses the same dependency-closure strategy as scope refinement.
The structural pass first identifies only modules with
`AGDA_TYPECHECKER`-deferred findings. Aggregate roots are typechecked once;
successful roots certify their candidate-bearing dependency closure, while
failed roots descend only through relevant imported subtrees. Modules already
known to fail scope are never pointlessly full-typechecked.

A reusable shadow-tree checker can be supplied independently for each evidence
layer:

```bash
AGDA_PREFLIGHT_REFINE=typecheck \
AGDA_PREFLIGHT_SCOPE_RUNNER='DASHI_NO_TMUX=1 DASHI_SKIP_RSYNC=1 ./scripts/run_agda29_parallel_check.sh --only-scope-checking {file}' \
AGDA_PREFLIGHT_TYPECHECK_RUNNER='DASHI_NO_TMUX=1 DASHI_SKIP_RSYNC=1 ./scripts/run_agda29_parallel_check.sh {file}' \
  ./scripts/check_agda_preflight_pytest.sh
```

Leading `KEY=VALUE` assignments in command-backed runners are merged into the
subprocess environment. The literal `{file}` is replaced with the absolute
module path; if omitted, the path is appended.

The command-backed full checker also harvests Agda `Checking Module (...)`
progress conservatively on failed/timeout runs: all completed modules before
the final failing module may be cached as typecheck-valid, while the final
observed module is never certified merely from progress output.

### Optional full Agda typecheck oracle

For focused or CI runs where the expense is acceptable, the preflight harness
can use ordinary Agda checking as the strongest negative oracle:

```bash
dashi-agda-preflight --agda-typecheck-oracle FILE.agda
```

or:

```bash
pytest --agda-preflight --agda-typecheck-oracle --agda-root . \
  DASHI/Physics/Closure/Foo.agda -vv
```

A successful full Agda check suppresses structural suspicions whose minimum
evidence is either `AGDA_SCOPE` or `AGDA_TYPECHECKER`. It does **not** suppress
DASHI trust/policy diagnostics such as forbidden postulates, raw proof
placeholders, or architectural gate violations: Agda acceptance does not make
those policy constraints false.

A failed typecheck is not reverse-engineered into TSAGDA conclusions; the
structural findings remain advisory unless independently confirmed.

The three refinement modes are mutually exclusive:

```text
--agda-scope-command      external precise confirmation/suppression
--agda-scope-check        Agda --only-scope-checking negative oracle
--agda-typecheck-oracle   full Agda negative oracle
```

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

Evidence policy is intentionally stricter than syntactic detectability. A rule
may cheaply *notice* a suspicious shape while still requiring Agda scope or the
full typechecker before it can become a hard conclusion. In particular,
definitional equality, dependent term/type roles, projection saturation,
constructor/pattern compatibility, coverage, positivity, and shallow arity
through aliases are not treated as DASHI-index facts.

### Syntax / declaration structure

- `TSAGDA000` tree-sitter syntax error / missing node; hard only with Agda-scope evidence because the grammar is intentionally incomplete
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
- `TSAGDA021` qualified symbol not exported by the apparent module; requires `AGDA_SCOPE` for a hard conclusion
- `TSAGDA022` malformed/unknown import alias use (`AGDA_SCOPE`)
- `TSAGDA023` apparent unknown symbol in `using (...)`; requires `AGDA_SCOPE`
- `TSAGDA024` apparent unknown symbol in `hiding (...)` (`AGDA_SCOPE`)
- `TSAGDA025` apparent unknown renaming source; requires `AGDA_SCOPE`
- `TSAGDA026` open/renaming collision (`AGDA_SCOPE`)
- `TSAGDA027` ambiguous unqualified exported name from multiple opens (`AGDA_SCOPE`)
- `TSAGDA028` conflicting aliases for imports; requires `AGDA_SCOPE`
- `TSAGDA029` repository import cycle
- `TSAGDA030` module identity/path collision

### Telescopes / calls / arity

Pointfree definitions such as `fst = proj₁` are never rejected merely because
their LHS has zero visible arguments while the declared type is functional.
Likewise, apparent over-application or clause/signature arity disagreement can
depend on definitional unfolding of result type synonyms. Those diagnostics are
therefore retained as useful suspicions but require `AGDA_TYPECHECKER` evidence
for a hard conclusion.

- `TSAGDA040` apparent over-application; typechecker evidence required because result aliases may unfold to functions
- `TSAGDA041` apparent under-application in a saturated context (`AGDA_TYPECHECKER`)
- `TSAGDA042` named implicit apparently absent from the shallow telescope (`AGDA_TYPECHECKER`)
- `TSAGDA043` apparent explicit/implicit visibility mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA044` lambda binder count versus shallow expected Pi shape (`AGDA_TYPECHECKER`)
- `TSAGDA045` non-pointfree clause/declaration arity disagreement; typechecker evidence required because eta/type aliases can change visible arity
- `TSAGDA046` apparent constructor application arity mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA047` apparent record-constructor arity mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA048` apparent parameterized-module application arity mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA049` apparent projection over/under-application (`AGDA_TYPECHECKER`)

### Projections

- `TSAGDA001` opened type-valued projection used unapplied as a type
- `TSAGDA002` projection receiver `_` despite an apparent matching binder (`AGDA_TYPECHECKER`)
- `TSAGDA050` apparent projection receiver/record-head mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA051` apparent declaration/type supplied as projection receiver (`AGDA_TYPECHECKER`)
- `TSAGDA052` projection receiver is syntactically absent (`AGDA_TYPECHECKER`; canonical triage root `TSAGDA049`)
- `TSAGDA053` apparent projection over-application (`AGDA_TYPECHECKER`)
- `TSAGDA054` projection/receiver record mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA055` ambiguous opened projection (`AGDA_SCOPE`)
- `TSAGDA056` apparent dependent projection parameter mismatch (`AGDA_TYPECHECKER`)

### Record construction / adapters

- `TSAGDA060` unknown field in record expression
- `TSAGDA061` duplicate field assignment
- `TSAGDA062` statically-known mandatory field missing
- `TSAGDA063` apparent record-expression target mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA064` record-field lambda/telescope shape mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA003` / `TSAGDA065` apparent terminal codomain/kind mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA066` apparent record-field result-head mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA067` source projection/target-field compatibility suspicion (`AGDA_TYPECHECKER`)
- `TSAGDA068` apparent constructor/expected-record mismatch (`AGDA_TYPECHECKER`)

### Shallow type shapes

The checker uses a deliberately small outer-shape language:
`Unknown`, `Meta`, `Sort`, `Head`, `Pi`, `Equality`, and `Literal`.
Only bounded head comparison/substitution is performed.

- `TSAGDA070` apparent type/sort used in a term position (`AGDA_TYPECHECKER`)
- `TSAGDA071` apparent term used in a type position (`AGDA_TYPECHECKER`)
- `TSAGDA072` apparent constructor/result type-head mismatch; typechecker evidence required when declared heads may unfold through synonyms
- `TSAGDA073` apparent argument type-head mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA074` literal/expected-type mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA075` constructor/datatype disagreement; conservatively typechecker-gated because the code is shared by rigid and synonym-sensitive checks
- `TSAGDA076` apparent function used as a type without enough application (`AGDA_TYPECHECKER`)
- `TSAGDA077` apparent type-constructor arity mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA078` sort apparently used as an ordinary value (`AGDA_TYPECHECKER`)
- `TSAGDA079` shallow zero-arity declaration applied as a function (`AGDA_TYPECHECKER`)

### Patterns / finite coverage

These checks are intentionally restricted to simple non-indexed datatypes.

- `TSAGDA080` apparent unknown constructor in pattern (`AGDA_SCOPE`)
- `TSAGDA081` apparent pattern-constructor/datatype mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA082` apparent constructor-pattern arity mismatch (`AGDA_TYPECHECKER`)
- `TSAGDA083` repeated binder in a linear pattern
- `TSAGDA084` suspicious inaccessible/dot-pattern name
- `TSAGDA085` absurd-pattern suspicion (`AGDA_TYPECHECKER`)
- `TSAGDA086` absurd-lambda suspicion (`AGDA_TYPECHECKER`)
- `TSAGDA087` finite-coverage suspicion (`AGDA_TYPECHECKER`)
- `TSAGDA088` clause visibly unreachable after catch-all
- `TSAGDA089` duplicate constructor branch

### Equality combinator structure

These do not prove equality; they only reject statically incompatible endpoint
shapes.

- `TSAGDA100` `refl` against visibly different rigid heads
- `TSAGDA101` `sym` endpoint shape mismatch
- `TSAGDA102` `trans` intermediate endpoint mismatch
- `TSAGDA103` apparent `cong` function/result incompatibility (`AGDA_TYPECHECKER`)
- `TSAGDA104` equality proof apparently supplied to a non-equality consumer (`AGDA_TYPECHECKER`)
- `TSAGDA105` equality endpoints have visibly incompatible rigid type heads

### Clause / scope checks

- `TSAGDA110` compatibility alias of typechecker-gated `TSAGDA045`
- `TSAGDA111` clause/signature visibility suspicion (`AGDA_TYPECHECKER`)
- `TSAGDA112` named implicit apparently absent from signature (`AGDA_TYPECHECKER`)
- `TSAGDA113` RHS identifier has no shallow binding (`AGDA_SCOPE`)
- `TSAGDA114` apparent clause constructor/result-head disagreement; typechecker evidence required for synonym unfolding
- `TSAGDA115` multiple incompatible signatures for one declaration

### Universe / declaration sanity

These are bounded structural checks, not universe solving.

- `TSAGDA120` term-like declaration head appears in a field type (`AGDA_TYPECHECKER`)
- `TSAGDA121` constructor result resolves to a term-like shallow head (`AGDA_TYPECHECKER`)
- `TSAGDA122` constructor target appears to differ from its datatype (`AGDA_TYPECHECKER`)
- `TSAGDA123` compatibility view of term-like field type (`AGDA_TYPECHECKER`; canonical triage root `TSAGDA120`)

### Positivity / termination heuristics

- `TSAGDA130` syntactic negative-recursion suspicion (`AGDA_TYPECHECKER`)
- `TSAGDA131` syntactic contravariant-recursion suspicion (`AGDA_TYPECHECKER`)
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

## One-command triage workflow

For the common repository-wide case, use:

```bash
scripts/check_agda_preflight_pytest.sh
```

The wrapper now defaults to:

```text
target              DASHI/Everything.agda
collection          dependency-first
output              compact pytest diagnostics
scope refinement    demand-driven only
structured report   .cache/agda_preflight/report.json
```

Demand-driven refinement means Agda scope checking runs **only** for modules that
actually contain `AGDA_SCOPE`-deferred findings. Modules with no such findings
stay on the cheap tree/index path.

Control escalation with:

```bash
AGDA_PREFLIGHT_REFINE=none      scripts/check_agda_preflight_pytest.sh
AGDA_PREFLIGHT_REFINE=scope     scripts/check_agda_preflight_pytest.sh
AGDA_PREFLIGHT_REFINE=typecheck scripts/check_agda_preflight_pytest.sh
```

`scope` is the default. `typecheck` additionally runs full Agda checking only
for modules that still contain `AGDA_TYPECHECKER`-level findings after the
scope stage. A failed scope check prevents pointless full-typecheck escalation.

Override the report location or aggregate root with:

```bash
AGDA_PREFLIGHT_REPORT=/tmp/agda-report.json \
AGDA_PREFLIGHT_TARGET=DASHI/Physics/Closure/Foo.agda \
  scripts/check_agda_preflight_pytest.sh
```

The terminal summary ranks the most frequent diagnostic codes and separates
hard from deferred counts. Complete per-location diagnostics remain in the JSON
report.

After the run, triage without grepping pytest logs:

```bash
# Highest-volume hard structural failures
dashi-agda-triage

# Findings waiting for stronger semantic evidence
dashi-agda-triage --deferred

# Concentrate on one diagnostic family
dashi-agda-triage --code TSAGDA060
dashi-agda-triage --deferred --code TSAGDA113

# Machine-readable triage summary
dashi-agda-triage --json
```

This deliberately separates three jobs:

```text
run       -> pytest + optional demand-driven Agda refinement
store     -> complete JSON evidence/diagnostic corpus
triage    -> ranked hard/deferred frontier
```

so large sweeps do not require manually reading tens of thousands of warning
lines.

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

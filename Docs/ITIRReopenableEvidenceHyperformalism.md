# ITIR reopenable evidence hyperformalism

## Purpose

This note consolidates the current ITIR / numeric-PNF evidence architecture onto
existing DASHI mathematics.  It deliberately avoids parallel implementations of
fibres, hyperfabrics, balanced/ternary phase, P/Q/J, 3/6/9, resolution towers,
identity fibres, or indexed gluing.

The target distinction is:

```text
fine semantic / representational carrier
        |
        | projection + retained receipt
        v
coarse execution surface
        |
        +-- signed/phase evidence reweights candidates
        +-- bounded execution may prune active work
        +-- hard proof may refute a candidate
        |
        v
proof-carrying local identity / factor derivation
        |
        v
optional external/world alignment
```

The three operations in the middle are different propositions.  In particular:

```text
currently suppressed
!= pruned from the current execution frontier
!= semantically refuted.
```

A negative/interfering phase is not a proof of impossibility, and an execution
overflow receipt is not a semantic rejection.

## Reused repository spine

The tranche imports or specialises the following existing objects.

### Fibre restriction and reopening

`DASHI.Core.FibreRestrictionCore` already proves the architectural boundary:
evidence may restrict a projected fibre without recovering the hidden carrier
or promoting truth.

`DASHI.Cognition.PNF.ReopenableEvidenceFibre` adds only the missing optional
receipt/reopening datum:

```text
receipt : Carrier -> Receipt
reopen  : Surface -> Receipt -> Carrier
reopen(project x, receipt x) = x.
```

This is the ITIR form of provenance-bearing coarse-graining.  It does not assert
that every quotient in mathematics or every runtime compression has a section.

### P/Q/J reference

`DASHI.Analysis.NormalizedFibreAveragingExact` supplies an exact finite
probability-fibre model with

```text
P^2 = P
Q   = I - P
P + Q reconstructs the fine observable.
```

`DASHI.Analysis.GlassesProjectionInvolutionExact` supplies the exact finite
involution

```text
J^2 = I
J P J = Q
J Q J = P.
```

The new PNF aggregate imports those exact claim boundaries as reference.  It
does **not** promote the two-point rational model to a universal semantic P/Q/J
theorem.  An application must construct the corresponding projector/residual
laws on its real carrier before using them authoritatively.

### Hyperformal incidence and interference

`DASHI.Reasoning.TypedHyperfabricCore` remains the higher-arity incidence,
stalk, restriction, provenance and obstruction carrier.

`DASHI.Reasoning.RelationalBranchInterference` remains the exact finite
integer-pair n-branch interference algebra, and
`DASHI.Reasoning.RelationalTernaryPhaseGeometry` remains the exact Eisenstein
`Z[omega]` symmetric ternary phase reference.  No literal quantum cognition or
Born-probability claim is introduced.

### 3 / 6 / 9

`DASHI.Biology.SSP369JResolutionBifiltrationExact` already establishes the
structural reading used here:

```text
3/6/9 = cumulative coordinate / relational horizon
r     = independent representation resolution.
```

The PNF specialisation is:

```text
H3 = local structural evidence
H6 = H3 + discourse / temporal evidence
H9 = H6 + external / authority evidence.
```

The candidate fibre itself may have arbitrary cardinality or richer geometry.
3/6/9 counts evidence-coordinate slots, not candidate branches.

`DASHI.Foundations.Base369BinaryTernaryRefinement` remains the separate exact
2^a 3^b refinement lattice.  Neither that lattice nor the H3/H6/H9 horizon is
silently identified with every semantic resolution problem.

## Parser/name support is not identity

The real-corpus identity benchmark exposed a large mismatch between admitted
identity projections and factor-bearing identity projections.  The missing seam
is formalised in `ParserArgumentSupportGluing` as

```text
parser/name representation --support/gluing--> argument-bearing PNF ObjectId.
```

It reuses:

- `DASHI.Core.TypedDependencyCore.DependencyWitness` for proposition-local
  source/target/provenance/scope;
- `NSTriadKNIndexedGluingRound32Exact.IndexedGluing` for the exact external to
  internal representation seam.

There is no constructor from structural support to identity.  Transporting an
identity comparison across the seam requires admitted identity witnesses at
both ends and a proof that they land on the same canonical entity.

## Identity proof existence is not factor utility

`IdentityProofUtility` separates

```text
admitted identity projection
factor-bearing identity projection
Level-3 identity substitution.
```

A valid identity is not rejected merely because no current factor uses it.
Factor applicability requires an independent factor-participation witness.  Only
then is the existing `IdentitySubstitutionProof` constructible.

This is the formal target for interpreting corpus funnels such as

```text
identity projections -> factor-bearing projections -> Level-3 substitutions
```

without weakening identity admission to increase the final number.

## Inductive preference is not deductive resolution

`InductiveDemandPreference` reuses the existing `DemandState` machine.  A
preferred candidate may carry a margin and evidence-coverage receipt, but it
still inhabits `openDemand`.

Scalar identity continues to require the existing exact path:

```text
singular reference + exactly one witness -> scalar identity permission.
```

This gives ITIR a place to represent discourse-level inductive reasoning without
turning ranking into proof.

## Local chronology before world alignment

`TemporalRoleWorldAlignment` makes role occupancy temporal:

```text
(entity, role, temporal cell, evidence).
```

Two different local entities may therefore occupy the same role in ordered
cells.  A GWB corpus can establish Reagan-as-President and Bush-as-President
through local chronology without first consulting Wikidata.

External/world alignment is a later proof-relevant fibre.  A candidate external
entity does not become world identity by lexical or vector similarity; promotion
still requires the existing `externalAlignmentEvidence` and
`externalAuthority` witness path from `ProofRelevantIdentityFibres`.

## Numeric occurrence fibres

The hot PNF carrier already has numeric token, sentence, symbol, factor, object
and demand IDs.  `NumericOccurrenceFibre` therefore wraps rather than replaces
`SpacyNumericProjection`.

Repeated tokens remain distinct occurrences:

```text
he_1 != he_2
```

while both may project to the same surface/lemma fibre key.  Multiplicity is the
number of occurrence members in a fibre, not a larger semantic incidence
coefficient.

No claim is made that balanced-ternary packing, CRT packing, or another
number-theoretic layout is automatically the physically optimal PostgreSQL row
representation.  Physical layout is a benchmarked execution decision; exact
numeric carrier structure and storage encoding remain separate obligations.

## PostgreSQL lexical retrieval

PostgreSQL full-text search dictionaries normalize tokens to lexemes; Snowball
provides stemming and Ispell provides dictionary normalization.  ITIR should use
that product capability aggressively when it reduces retrieval work, while
keeping its authority boundary explicit.

The PNF lexical coordinates are therefore distinct:

```text
exact surface SymbolId
parser lemma observation
retrieval lexeme SymbolId(s).
```

A PostgreSQL retrieval lexeme is not definitionally equal to a parser lemma.
Full-text normalization is a retrieval projection and may be more aggressive.

Reference:

- PostgreSQL 18, *12.6 Dictionaries*:
  https://www.postgresql.org/docs/18/textsearch-dictionaries.html

`tsvector`/full-text state is treated as a derived retrieval surface, not the
canonical token-occurrence geometry.  Authoritative occurrence position remains
in the numeric token carrier.

### Regex boundary

Semantic cue phrases are represented after tokenisation as exact finite words
of `SymbolId`:

```text
NumericCueWord = List SymbolId.
```

A runtime may compile governed cue words into a trie, DFA, Aho-Corasick machine,
or another efficient integer-token matcher.  The Agda contract intentionally
does not privilege one implementation.  Regex has no direct semantic promotion
constructor.

## Sampling, aliasing and coarse/fine lookup

`SemanticSamplingLookupGeometry` reuses
`StratifiedResolutionTowerExact.ResolutionTower` and formalises only the exact
condition needed from the Nyquist analogy:

```text
fineQuery x = coarseQuery(project x)
```

for every fine state at a declared sufficient resolution.

An `AliasingWitness` is two distinct fine states with the same coarse shadow.
This makes the semantic question precise without claiming a classical Fourier
bandlimit or Shannon sampling theorem for language.

Sampling sufficiency and description-length optimality are separate.  A
representation may be sufficient but inefficient; an MDL optimum may be too
coarse if it aliases query-relevant distinctions.

## Lookup geometry

`DirectDemandLookup` now separates three supplied storage-engine contracts:

```text
exact equality / hash-style      -> expected constant-budget contract
ordered tree / B-tree-style      -> logarithmic contract
prefix / partition geometry      -> explicit prefix bound.
```

These are contracts, not unconditional PostgreSQL complexity theorems.  A real
runtime should instantiate them from an observed query plan / benchmark receipt.

PostgreSQL exposes B-tree, hash, GiST, SP-GiST and GIN index families with
different operator/query geometries.  Reference:

- PostgreSQL, *11.2 Index Types*:
  https://www.postgresql.org/docs/current/indexes-types.html

The dual semantic address is therefore:

```text
exact numeric lookup key + structured geometric address.
```

Exact equality, prefix/ultrametric neighbourhood, temporal interval and fuzzy
proposal need not use the same physical index.

A prefix/resolution tower is not called p-adic by theorem unless the application
also constructs the compatible modular arithmetic required for p-adic algebra.

## Continuous / vector proposal geometry

A continuous or floating-point coordinate is an evaluation/search view, not the
canonical semantic object.  Approximate neighbourhood retrieval can therefore
propose an active fibre, followed by exact numeric constraints and proof-bearing
resolution.

The pgvector project supports exact nearest-neighbour search as well as
approximate HNSW/IVFFlat indexing.  In ITIR this capability belongs strictly to
candidate generation; approximate retrieval has no identity-promotion
constructor.

Reference:

- pgvector project:
  https://github.com/pgvector/pgvector

## Bounded execution and omitted mass

`BoundedExecutionCarrier` consolidates the pattern independently present in
proper-name enumeration and factor composition:

```text
semantic possibility count
retained execution count
execution limit
overflow/coverage receipt.
```

It bridges the existing runtime-specific enumeration records rather than
replacing them.

An optional generic `SplitMeasureReceipt` records

```text
retained mass + omitted mass = total mass
```

on an application-supplied mass algebra.  It does not manufacture a probability
measure or Born rule.  This is the natural place for future causal-cone / beam
reweighting receipts where a branch can leave the active frontier without being
refuted.

## Authority summary

The reference spine enforces:

```text
support/gluing       != identity
retrieval rank        != semantic admission
inductive preference != deductive resolution
negative phase        != refutation
execution pruning     != refutation
overflow              != semantic rejection
role identity         != person identity
local entity          != world entity
H9 authority evidence != automatic world promotion
prefix geometry       != automatically p-adic
query sufficiency     != classical Nyquist theorem
finite P/Q/J model    != universal semantic P/Q/J theorem.
```

The intended runtime direction is increasingly pure numeric execution after
tokenisation, with text retained for source/provenance/presentation and with
PostgreSQL-native retrieval/index products used wherever measurement shows they
reduce work without crossing these authority boundaries.

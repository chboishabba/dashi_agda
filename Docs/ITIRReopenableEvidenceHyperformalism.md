# ITIR reopenable evidence hyperformalism

## Purpose

This note consolidates the ITIR / numeric-PNF evidence architecture onto the
existing DASHI mathematical spine.  The governing rule is **reuse before new
abstraction**: fibres, hyperfabrics, P/Q/J, 3/6/9, multiscale residual codecs,
signed interference, symmetry/orbits, identity fibres, dependency witnesses,
resolution towers and indexed gluing are imported rather than reimplemented.

The post-tokenisation target is increasingly numeric:

```text
source text / provenance boundary
        |
        v
numeric token occurrences and lexical fibres
        |
        v
representation/support gluing
        |
        v
reopenable evidence hyperfibre
        |
        +-- signed fine evidence -> coarse phase observation
        +-- H3 -> H6 -> H9 relational horizon
        +-- soft reweighting / path-dependent accessibility
        +-- bounded execution + overflow / omitted-mass receipt
        +-- inductive preference, still unresolved
        |
        v
proof-relevant local identity
        |
        v
factor applicability / Level-3 substitution
        |
        v
local temporal-role model
        |
        v
optional external/world alignment
```

The architecture is fail-closed about promotion.  In particular:

```text
currently suppressed
!= pruned from the current execution frontier
!= semantically refuted.
```

Semantic refutation itself is proof-bearing and indexed by evidence.

## Existing repository spine reused

### Fibre restriction, receipt and reopening

`DASHI.Core.FibreRestrictionCore` already gives the central authority boundary:
evidence can restrict a projected fibre without recovering the fine carrier and
without promoting truth.

`DASHI.Cognition.PNF.ReopenableEvidenceFibre` adds only the optional exact
provenance receipt required when an application can reconstruct the same fine
state:

```text
receipt : Carrier -> Receipt
reopen  : Surface -> Receipt -> Carrier
reopen(project x, receipt x) = x.
```

This is not a theorem that every quotient splits.  It is a proof obligation for
runtime compressions that claim exact reopening.

Soft evidence uses `EvidenceReweighting`.  It changes application-supplied
weights but has no refutation constructor.  `SemanticAdmissibility` instead
requires a `RefutationSystem` and an explicit `Refutes evidence candidate`
witness before `semanticallyRefuted` can be constructed.

Corrective reachability reuses
`DASHI.Core.TypedDependencyCore.DependentActionSystem` and its proof-bearing
`AdmissibleAction` with precondition, postcondition and dependency receipt.
`CorrectivePath` is only the reflexive/transitive PNF closure over those existing
admissible actions.

## Exact P/Q/J reference, not universal promotion

`DASHI.Analysis.NormalizedFibreAveragingExact` supplies the exact finite
normalised fibre reference with `P^2=P`, `Q=I-P`, orthogonality and exact
coarse/residual reconstruction.

`DASHI.Analysis.GlassesProjectionInvolutionExact` supplies the exact generic-base
two-point fibre model with

```text
J^2 = I
J P J = Q
J Q J = P.
```

`PNFEvidenceHyperformalism` reuses it directly as
`ComplementaryReadingReference {Candidate}`.  It is a concrete adversarial /
complementary-view reference, not a theorem that every semantic hyperfibre has a
P/Q/J decomposition.  `UniversalSemanticPQJPermission` is constructorless.

## Hyperformal incidence and phase/interference

`DASHI.Reasoning.TypedHyperfabricCore` remains the higher-arity incidence,
stalk, restriction, provenance and obstruction carrier.

`DASHI.Reasoning.RelationalBranchInterference` remains the exact finite signed
interference reference.  `EvidenceHorizon369.EvidenceCoordinate` therefore
stores

```text
fineSignedEvidence : Z
phaseClassification : ClassifiedInteraction fineSignedEvidence
```

and derives `reinforcing / independent / interfering` and magnitude from that
existing classification witness.  The coarse ternary direction cannot be
assigned independently of its fine signed receipt.

`DASHI.Reasoning.RelationalTernaryPhaseGeometry` remains the exact Eisenstein
phase reference.  No literal quantum-cognition or Born-probability claim is
introduced.  A later application may supply a continuous or constructive-real
fine field, but must separately prove how its coarse signed observation maps to
this reference structure.

## 3 / 6 / 9 is relational accumulation, not branching factor

The structural source is
`DASHI.Biology.SSP369JResolutionBifiltrationExact`:

```text
H3 = one three-coordinate block
H6 = H3 + a second three-coordinate block
H9 = H6 + a third three-coordinate block.
```

The PNF evidence specialisation is:

```text
H3 = local structural evidence
H6 = H3 + discourse / temporal evidence
H9 = H6 + external / authority evidence.
```

The candidate fibre can have arbitrary cardinality or richer geometry.  3/6/9
counts accumulated evidence-coordinate slots, not possible referents.

Relational horizon and representational resolution remain independent axes.
`EvidenceHorizon369` now works over **any existing**
`StratifiedResolutionTowerExact.ResolutionTower` and proves the finite commuting
squares

```text
project6to3 (coarsenH6 x) = coarsenH3 (project6to3 x)
project9to6 (coarsenH9 x) = coarsenH6 (project9to6 x).
```

Thus increasing relational horizon and coarsening representation commute at the
formal interface.  This does not prove interchange of any infinite limits.

`Base369BinaryTernaryRefinement` remains the separate exact `2^a 3^b`
refinement lattice and is not identified with every semantic resolution tower.

## Parser/name support is not identity

The real-corpus benchmark exposed many admitted identity projections but very
few factor-bearing identity projections.  The missing structural seam is
formalised in `ParserArgumentSupportGluing`:

```text
parser/name representation --support/gluing--> argument-bearing PNF object.
```

It reuses:

- `TypedDependencyCore.DependencyWitness` for proposition-local source, target,
  provenance and scope;
- the generic `IndexedGluing` proof from the merged indexed-gluing spine.

There is no constructor from support to identity.

For multiscale carriers the stronger requirement is now explicit:

```text
S_r(project_P x) = project_A(S_(r+1) x).
```

`ParserArgumentResolutionNaturality` must be supplied when support is claimed to
transport coherently across parser and argument resolution towers.  Identity
comparison across a support seam still requires independently admitted identity
witnesses at both ends that land on the same canonical entity.

## Contextual representation orbits and stabilizers

`ContextualRepresentationOrbit` reuses `MultiscaleMDL.SymmetryAction` and
`OrbitRelated` rather than defining a second canonicalisation/group-action
system.

A contextual orbit witness adds only numeric scope, region and provenance.  A
`ContextualStabilizerWitness` explicitly permits fixed representatives; no free
action or full orbit cardinality is assumed.  Surface/title/pronoun
representations may therefore be orbit-related in a witnessed context without
being flattened into entity identity.  Orbit relation has no identity-promotion
constructor.

## Numeric occurrence fibres

`NumericOccurrenceFibre` wraps the existing `SpacyNumericProjection` rows.
Repeated strings remain distinct occurrences:

```text
he_1 != he_2
```

while both can project to the same surface or lemma fibre key.  Multiplicity is
therefore occurrence/fibre cardinality, not the magnitude of one semantic
incidence coefficient.

## Token storage: exact codec first, optimal layout only by evidence

`NumericTokenStorageReference` keeps the authoritative post-tokenisation hot
stream numeric (`List SymbolId`) and separates storage coding from semantic
identity.

A `LosslessTokenStreamCodec` must prove

```text
decode(encode(stream)) = stream.
```

When storage has a real coarse/fine tower, the module reuses
`DASHI.Core.MultiscaleMDL.ResidualCodec`, `split`, `join`, `join-split` and
`MDLCost`.  The existing MDL boundary already separates exact reconstruction
from an entropy model, Kraft admissibility, residual-entropy bounds and
rate-distortion optimality.

Accordingly, balanced-ternary packing, CRT packing, dictionary packing or any
other number-theoretic layout is **not** declared physically optimal by algebra
alone.  Hot random-access storage and cold/archive storage may have different
objectives; `StorageMeasurement` and `StorageComparisonReceipt` carry bytes,
lookup work and decode work without promoting one benchmark into a global
optimality theorem.

## PostgreSQL lexical retrieval is a first-class optimisation surface

The PNF lexical coordinates are deliberately separate:

```text
exact surface SymbolId
parser lemma observation
retrieval lexeme SymbolId(s).
```

A PostgreSQL full-text lexeme is not definitionally equal to a parser lemma.
Full-text normalization/stemming is a retrieval projection and may be more
aggressive because it proposes candidate neighbourhoods rather than asserting
semantic identity.

`LexicalRetrievalProjection` represents PostgreSQL FTS, numeric cue automata and
vector neighbourhoods as retrieval producers.  `RetrievalReductionReceipt`
records input and output candidate counts with `output <= input`, so a product
feature earns hot-path use by measurable reduction rather than decoration.

Reference:

- PostgreSQL, *12.6 Dictionaries*:
  https://www.postgresql.org/docs/current/textsearch-dictionaries.html

Full-text state remains a derived retrieval surface rather than canonical token
occurrence geometry.

### Regex boundary

Governed multi-token cue phrases are exact finite words over `SymbolId` after
tokenisation:

```text
NumericCueWord = List SymbolId.
```

A runtime may compile those words to a trie, DFA, Aho-Corasick machine or other
integer-token matcher.  The Agda contract deliberately does not privilege the
implementation.  Regex has no semantic-authority constructor.

## Inductive preference is not deductive resolution

`InductiveDemandPreference` reuses the existing `DemandState` machine.  A
preferred candidate may have an evidence margin and coverage receipt while the
demand remains `openDemand`.

Scalar identity continues to require the existing exact permission:

```text
singular reference + exactly one witness -> scalar identity.
```

This is the formal home for discourse-level inductive preference without
promoting ranking into proof.

## Identity proof existence is not factor utility

`IdentityProofUtility` separates:

```text
admitted identity projection
factor-bearing identity projection
Level-3 identity substitution.
```

A valid identity is not rejected because no current factor uses it.
`FactorApplicableIdentity` requires an independent `FactorParticipation`
witness; only then is the existing `IdentitySubstitutionProof` constructible.

`EvidenceCoverageAudit` supplies the empirical receipt shape for the next corpus
round without changing semantics:

- identity/factor intersection at sentence, paragraph, adaptive and document
  levels;
- the existing `SparseFrontierCertificate` for boundary reduction;
- typed-demand funnel: generated -> has candidate -> unique -> admitted identity
  -> factor substitution;
- admitted witness rows versus distinct source/target identity propositions.

Counts never promote semantic truth, and low factor coverage does not invalidate
an otherwise sound identity proof.

## Local chronology before world alignment

`TemporalRoleWorldAlignment` makes role occupancy temporal:

```text
(entity, role, temporal cell, evidence).
```

Different local entities can occupy the same role in ordered cells.  The GWB
tranche can therefore establish Reagan-as-President and Bush-as-President from
local chronology without requiring Wikidata to create that timeline.

External alignment is later and proof-relevant.  An external candidate does not
become world identity through lexical or vector similarity; promotion still
uses the existing `externalAlignmentEvidence` and `externalAuthority` witness
path from `ProofRelevantIdentityFibres`.

## Sampling, aliasing and coarse/fine lookup

`SemanticSamplingLookupGeometry` reuses
`StratifiedResolutionTowerExact.ResolutionTower` and formalises only the exact
condition required from the Nyquist/Shannon analogy:

```text
fineQuery x = coarseQuery(project x).
```

An `AliasingWitness` is two distinct fine states with the same coarse shadow.
This makes “resolution sufficient for this query” exact without claiming a
classical Fourier bandlimit or Shannon sampling theorem for language.

Sampling sufficiency and description-length optimality remain separate.  A
representation may be sufficient but inefficient; an MDL optimum may be too
coarse if it aliases query-relevant distinctions.

## Lookup geometry and PostgreSQL probe contracts

`DirectDemandLookup` now owns one typed probe spine:

```text
exact equality/hash-style      -> expected constant-budget contract
ordered tree/B-tree-style      -> logarithmic contract
prefix/partition geometry      -> explicit prefix-bound contract.
```

These are supplied storage-engine receipts, not unconditional PostgreSQL
complexity theorems.  Runtime plans/benchmarks must instantiate them.

Reference:

- PostgreSQL, *11.2 Index Types*:
  https://www.postgresql.org/docs/current/indexes-types.html

The semantic address can therefore carry both an exact numeric lookup key and a
structured geometric coordinate.  Equality, prefix/ultrametric neighbourhood,
temporal interval and fuzzy proposal do not need the same physical index.

A prefix/resolution tower is not called p-adic by theorem unless the application
also constructs compatible modular arithmetic.

## Continuous/vector proposal geometry

A floating-point or continuous coordinate is an evaluation/search view, not the
canonical semantic object.  `NeighbourhoodProposalReceipt` therefore places
vector/continuous neighbourhood search below the authority boundary: it proposes
a bounded active fibre and explicitly requires exact downstream checking.

The pgvector project is an appropriate runtime candidate for this proposal
layer; approximate retrieval has no identity-promotion constructor.

Reference:

- pgvector project:
  https://github.com/pgvector/pgvector

This tranche does **not** manufacture a constructive-real continuous semantic
field merely because the discrete signed/interference reference admits such an
interpretation.  A future continuous instance must supply its carrier, metric or
phase field and its coarse-observation theorem explicitly.

## Bounded execution, omitted mass and causal-cone narrowing

`BoundedExecutionCarrier` consolidates the common structure already present in
proper-name enumeration and factor composition:

```text
semantic possibility count
retained execution count
execution limit
coverage / overflow receipt.
```

Overflow has no semantic authority.  `MeasuredBoundedExecutionCarrier` adds an
application-supplied `SplitMeasureReceipt`:

```text
retained mass + omitted mass = total mass.
```

No probability measure or Born rule is manufactured.  This is the exact slot
for future causal-cone / beam reweighting receipts: a branch may become low
weight or leave the active frontier while remaining semantically possible and
reopenable under later evidence.

## Authority summary

The reference spine now enforces:

```text
support/gluing        != identity
orbit relation         != identity
retrieval rank         != semantic admission
inductive preference  != deductive resolution
negative phase         != refutation
soft reweighting       != refutation
execution pruning      != refutation
overflow               != semantic rejection
role identity          != person identity
local entity           != world entity
H9 authority evidence  != automatic world promotion
prefix geometry        != automatically p-adic
query commutation      != classical Nyquist theorem
number-theory packing  != storage optimality
finite P/Q/J reference != universal semantic P/Q/J theorem.
```

The intended runtime direction is pure numeric execution wherever possible after
tokenisation, with source text retained for provenance/presentation and with
PostgreSQL-native retrieval/index products used whenever measurement shows they
reduce work without crossing these authority boundaries.

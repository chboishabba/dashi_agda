# Collatz/Syracuse Same-Object Bridge Design

## Purpose

Build a source-auditable formal bridge from the literal shortcut Syracuse process on positive integers to the repository's existing finite 2-adic/parity-cylinder machinery, without identifying distinct dynamical objects by analogy. The bridge must preserve object identity explicitly, expose every representation seam as a theorem-bearing interface, and support two independent downstream routes: repaired spectral/mixing concentration and finite prefix-absorption/hitting.

This design follows the repo's existing same-object discipline from hyperfabric pants gluing and the P-vs-NP concrete/standard-machine welds.

## Non-goals

This work does not claim the Collatz conjecture, does not reinstate the refuted unit-prefactor one-step spectral bound, and does not infer integer stopping results merely from finite spectral statements. It also does not identify the finite affine chain `z -> 3z` / `z -> 3z - 1` with the shortcut Syracuse map itself.

## Existing reusable machinery

The implementation reuses these already-owned interfaces and consumers:

- `DASHI.Foundations.HyperformChartGluingExact`: explicit same-object chart gluing, observer-with-fibre, and contextual lifts.
- `DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact`: typed seam authorization by independent `InterfaceMatch`; seam certificates do not rewrite topology or erase path memory.
- `DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCookLevinSameObjectWeldExact`: one-literal-object representation weld discipline.
- `DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact`: forward/reverse representation equivalence under explicit hypotheses.
- `DASHI.Analysis.NonArchimedeanPrefactoredL2PowerCompilerExact` and `NonArchimedeanContinuousMixingBidiExact`: repaired finite level-dependent prefactored `L2` power decay and dependency-closed finite correlation/TV consumers.
- `DASHI.Core.FinitePrefixAbsorptionExact`: exact prefix-kill persistence.
- `DASHI.Core.FiniteUniformBranchingHittingTailExact`: generic geometric survivor-count engine.
- `DASHI.Analysis.NonArchimedeanFiniteUniformHittingBlockCompilerExact` and `NonArchimedeanHittingWordPaddingExact`: finite reachability-to-uniform-block compilation and binary word padding.
- `DASHI.Analysis.NonArchimedeanTaoConcentrationSameObjectNoGoExact`: current firewall identifying the object-switch, noncanonical finite-residue logarithm, and missing concentration hypotheses.

## Architecture

### A. Literal Syracuse layer

Create a new namespace under `DASHI/NumberTheory/Collatz/` that owns the actual positive-integer process.

#### `SyracuseExact.agda`

Define:

- positive-natural carrier or a proof-carrying nonzero natural wrapper;
- `shortcutSyracuse` implementing
  - `x / 2` for even `x`,
  - `(3*x + 1) / 2` for odd `x`;
- iteration `syracuseIterate`;
- parity observation for each iterate;
- no probabilistic semantics.

Required exact lemmas:

- positivity/nonzero preservation;
- parity branch equations;
- iteration successor law.

#### `SyracuseParityItineraryExact.agda`

Define the first `m` parity bits of one literal Syracuse orbit and the finite binary word / residue encoding:

`epsilon j x = parity (syracuseIterate j x)`

`Q m x = sum_{j<m} epsilon j x * 2^j`

Required theorems:

- shift law: parity itinerary of `S x` is the tail of the itinerary of `x`;
- finite-prefix shift/commutation theorem;
- exact conversion between repo binary words and parity-prefix vectors.

### B. Forward/reverse parity-cylinder equivalence

#### `SyracuseParityCylinderExact.agda`

For each finite parity word `w : BinaryWord m`, construct an explicit residue `residueOfParityWord w : ZMod (2^m)` or canonical natural representative and prove the two directions:

1. forward classification:
   `Q m x = w -> x mod 2^m = residueOfParityWord w`;
2. reverse reification:
   `x mod 2^m = residueOfParityWord w -> Q m x = w`.

Package them as an iff-equivalent same-object certificate.

The target theorem shape is:

`Q_m(x) = w  <->  x ≡ r_w (mod 2^m)`.

Uniqueness of the residue cylinder is required. No cardinality-counting shortcut may stand in for this theorem.

This is the Collatz analogue of the P-vs-NP concrete/standard forward+reverse acceptance equivalence.

### C. Exact affine iterate and log drift

#### `SyracuseAffineIterateExact.agda`

Define parity count `s_m(x)` and an explicit additive parity-word term `A_m(w)`. Prove by induction:

`2^m * S^m(x) = 3^(s_m(x)) * x + A_m(Q_m(x))`.

The additive term must be recursive and executable on parity words; no existential-only witness is sufficient.

#### `SyracuseLogDriftExact.agda`

Keep logarithms strictly on positive integer/real lifts, never on residue classes. Define the stopped process at threshold `Y` and prove the exact decomposition

`log(S^m x) - log x = s_m log 3 - m log 2 + R_m(x)`

with an explicit nonnegative remainder accumulated only from odd steps.

Before the stopping time `tau_Y`, prove a deterministic bound of the form

`0 <= R_m(x) <= m/(3Y)`

or a stronger bound derivable from the exact increment `log(1 + 1/(3X_j))`.

If the real-analysis library makes the sharp bound expensive, the implementation may expose the exact remainder and a weaker monotone bound first, but must mark the sharper estimate as a separate analytic obligation rather than replacing it with a Boolean receipt.

### D. Same-object observer and finite transfer weld

#### `CollatzSyracuseParityObserverExact.agda`

Instantiate `ObserverWithFibre` from `HyperformChartGluingExact`:

- Fine object: literal integer Syracuse start/orbit data;
- Coarse object: parity prefix / cylinder coordinate;
- observer: `Q_m`;
- fibre: exact congruence class characterized by the forward/reverse cylinder theorem.

The observer fibre must retain lost integer information explicitly.

#### `CollatzSyracuseFiniteTransferSameObjectWeldExact.agda`

Do not assert that the finite affine chain equals `shortcutSyracuse`.

Instead identify the existing finite operator

`P_n f(z) = 1/2 * (f(3z) + f(3z - 1))`

as a transfer/pullback operator on the finite parity-cylinder coordinate only after proving an explicit intertwining theorem.

The desired interface is a theorem-bearing record with fields equivalent to:

- literal fine dynamics;
- parity observer;
- finite cylinder action;
- finite observable action;
- one-step intertwining on the supported observable class;
- iterated intertwining;
- attribution receipt naming the finite source operator;
- negative firewall: intertwining does not imply kernel equality on the fine state space.

If the exact orientation is adjoint/transfer rather than observable-forward, use the orientation already established by `NonArchimedeanAdjointPowerTVWeldExact`; do not force the wrong equation merely to match notation.

#### `CollatzSyracuseCylinderInterfaceMatchExact.agda`

Reuse the hyperfabric seam pattern. Package the integer parity cylinder and finite transfer cylinder as two selected interfaces with an explicit match of all coordinates required downstream:

- cylinder identity / word;
- branch orientation;
- measure/count normalization;
- time-step alignment;
- observable orientation.

A partial coordinate agreement does not authorize a full seam.

### E. Sampling pushforward

#### `CollatzSyracuseSamplingPushforwardExact.agda`

Probability is introduced only through a distribution on starting integers.

Define a finite sampled-start law first, with an explicit support and mass function. Prove exact or bounded pushforward to parity cylinders.

Preferred first theorem: for a complete interval of length divisible by `2^m`, the parity-prefix pushforward is exactly uniform by the residue-cylinder equivalence.

Then add a boundary-error theorem for arbitrary finite intervals:

`TV ((Q_m)_* mu_X) uniform <= delta(X,m)`

with an explicit remainder from incomplete residue blocks.

Logarithmically weighted sampling, if needed for Tao-style applications, is a later source-specific consumer and must not be silently identified with the uniform finite-interval law.

### F. Route 1: repaired mixing/concentration

#### `CollatzSyracuseCylinderCorrelationExact.agda`

Transport the already-owned finite `L2` correlation decay through the same-object cylinder seam. Preserve the finite prefactor `C_n`; never reintroduce the refuted unit-prefactor theorem.

#### `CollatzSyracuseMixingConcentrationCompilerExact.agda`

Provide an explicit concentration-hypothesis record. Support one of two theorem-bearing implementations:

1. derive a strong/rho mixing coefficient from the finite correlation/TV bounds and apply a bounded-observable concentration theorem; or
2. explicitly formalize the nonreversible pseudo-spectral-gap ingredients required by a Paulin-style theorem.

The initial implementation should prefer route 1 if it requires fewer new analytic primitives. No field named `spectralGap` alone may authorize concentration.

Required bounded observable is the centered parity increment `epsilon_j - 1/2` (or an equivalent signed integer encoding avoiding unnecessary rationals until the analysis boundary).

#### `CollatzSyracuseStoppingConcentrationExact.agda`

Combine:

- parity-sum concentration;
- exact negative drift `0.5*log 3 - log 2 < 0`;
- the stopped additive remainder bound;
- sampling pushforward error;

to obtain a theorem explicitly conditional on all concentration hypotheses and the chosen sampling law.

This theorem is a stopping/concentration statement, not the full Collatz conjecture.

### G. Route 2: prefix absorption and hitting

#### `CollatzSyracusePrefixAbsorptionWeldExact.agda`

Instantiate `FinitePrefixAbsorptionExact` with the actual parity-cylinder semantics. Prove that an integer-orbit prefix entering the chosen stopping region corresponds to a killed cylinder prefix, and that padding/extensions remain killed.

This closes the exact source-path same-object weld that `FinitePrefixAbsorptionExact` currently leaves as an explicit requirement.

#### `CollatzSyracuseUniformHittingBlockExact.agda`

Where finite directed reachability is actually available, reuse the existing finite maximum compiler to obtain a uniform block length. The theorem must clearly state the finite state space and target; it must not promote a fixed-level finite hitting result to all integers.

#### `CollatzSyracuseGeometricSurvivalExact.agda`

Instantiate `FiniteUniformBranchingHittingTailExact` only after proving:

- exact branch count;
- at least one killed continuation for every surviving finite state;
- aggregate survivor recurrence.

Then export the generic geometric survivor-count bound and transport it back through the parity-cylinder sampling theorem.

### H. Consolidated max-cut audit

#### `CollatzSyracuseSameObjectMaxCutExact.agda`

Create one non-promoting audit owner exposing statuses for C1-C14:

- literal Syracuse semantics;
- parity observer;
- residue-cylinder iff;
- forward shift;
- reverse reification;
- affine iterate;
- stopped log remainder;
- finite transfer intertwiner;
- cylinder seam certificate;
- repaired finite prefactored mixing;
- sampling pushforward;
- concentration route;
- prefix-absorption route;
- integer stopping transport.

Statuses must distinguish `proved`, `compiledFromRepo`, `conditionalOnHypothesis`, `sourceSpecificOpen`, and `refutedRoute`. A downstream theorem may not be marked paid merely because an interface record exists.

## Cross-pollination invariants

### From hyperfabric/pants

- Every seam has a typed domain interpretation.
- Full interface matching is stronger than one-coordinate agreement.
- A seam certificate authorizes transport only across the stated interface.
- Path/provenance memory remains explicit.
- Gluing does not automatically rewrite topology/dynamics.

### From P-vs-NP

- One literal source object is shared across representation theorems.
- Forward simulation alone is insufficient; reverse reification is a separate theorem.
- Exact resource/time alignment is carried through the weld.
- Representation equivalence does not automatically imply universal lower-bound or complexity conclusions.

### Applied to Collatz

- The shortcut Syracuse map remains the unique fine dynamical object.
- Parity words and residue cylinders are observations/representations of that object.
- The finite affine chain is used only via an explicit transfer/intertwining theorem.
- Finite mixing or finite hitting never automatically promotes to a theorem over all integer starts.

## Testing and proof-audit strategy

Every new module must be source-written with no postulates, holes, unsafe options, or placeholder RHSs.

Add static check scripts following existing repo conventions. Minimum checks:

- module existence and imports;
- absence of `postulate`, `{!!}`, `?`, and unsafe options;
- required theorem/record names;
- negative firewall fields remain false/nonconstructible;
- no occurrence of the refuted unit-prefactor claim as a positive theorem;
- the log observable appears only on positive integer/real lifts, not directly on `ZMod` residues.

Add finite executable/specimen checks for small parity words and small integers to catch orientation errors in the residue-cylinder and transfer laws. These are tests, not replacements for the general proofs.

Where Agda compilation is available, typecheck each leaf module before the consolidated owner. Cross-language Lean adapters may be added only after the Agda same-object interface is stable, unless a needed theorem already exists canonically in Lean and is better treated as an attributed source receipt.

## Implementation order / max-cut

1. C1 literal Syracuse carrier and iteration.
2. C2 parity observer and binary-word conversion.
3. C3 forward residue-cylinder classification.
4. C5 reverse reification and uniqueness.
5. C4 shift/commutation theorem.
6. C6 affine iterate identity.
7. C7 stopped log remainder exact form and deterministic bound.
8. C8 finite transfer/intertwining theorem, respecting adjoint orientation.
9. C9 full cylinder interface match.
10. C11 exact uniform-block sampling pushforward, then boundary TV error.
11. C12b prefix-absorption/hitting route, because it needs less new analysis.
12. C10/C12a repaired correlation-to-concentration route.
13. C13 transport each proved finite tail to the stated integer sampling law.
14. C14 consolidated max-cut audit and promotion firewall.

The implementation should continue until it reaches a genuine new analytic or arithmetic wall. At that point the wall must be represented as a minimal theorem hypothesis with all downstream compilers completed, not hidden behind a Boolean success flag.

## Success criteria

The max-cut is successful when:

1. literal integer Syracuse dynamics and finite parity-cylinder dynamics are connected only through explicit proved observers/welds;
2. every finite parity word has a proved unique residue-cylinder reification and converse;
3. the exact affine iterate identity is source-written;
4. the finite `3z/(3z-1)` operator is either rigorously identified as the relevant transfer action or explicitly rejected if orientation/algebra fails;
5. the existing prefactored finite mixing theorem is reused without reviving the false unit-prefactor claim;
6. sampled-start probability is introduced explicitly and its parity-prefix pushforward is proved;
7. prefix absorption is instantiated on the same object and geometric survival is obtained wherever the finite killed-continuation hypotheses can actually be proved;
8. concentration is exported only from theorem-bearing dependence/pseudo-gap hypotheses;
9. all remaining open mathematics is isolated in minimal named obligations;
10. no result is labelled a proof of the Collatz conjecture unless a separate theorem actually closes the universal integer stopping statement.

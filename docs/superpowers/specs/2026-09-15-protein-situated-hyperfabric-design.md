# Protein Situated Hyperfabric Design

Date: 2026-09-15
Status: approved architecture, implementation not yet started
Parent objective: Feng/TRPA1 protein programme with AdK as an independent worked acquisition exemplar

## 1. Purpose

This design introduces a thin, time-indexed protein situated hyperfabric that composes existing DASHI biological, protein, trajectory, observer, provenance, and non-factorability machinery. It does not replace `ProteinRecoveryBoundary`, `BiologicalRecoveryBoundary`, `TranslationContextEncoding`, `NaturalSystemsHyperfabricExact`, or the generic situated-fibre calculus.

The central question is consumer-relative:

```text
For a protein query Q, through which smallest situated fibre does Q factor?
```

If a coarse projection collides states that the consumer separates, the system must retain the missing coordinate rather than reweighting or relabelling the already-coarse projection.

## 2. Existing owners reused as authoritative repository interfaces

The new layer imports, rather than recreates, the following existing surfaces:

- `DASHI.Biology.BiologicalRecoveryBoundary`
  - supplies the vertical recovery tower and leaves translation/folding dynamics, protein experimental authority, metabolism/viability, and regulatory/bioelectric coupling as separate obligations.
- `DASHI.Promotion.TranslationContextEncoding`
  - supplies context-dependent translation `E : Genome -> MolecularContext -> Protein`; genome alone does not determine translated protein sequence.
- `DASHI.Biology.Protein.ProteinRecoveryBoundary`
  - supplies sequence, conformational ensemble, locality/profile, contextual function, prion/misfolding compatibility, and explicit open obligations.
- `DASHI.Biology.NaturalSystemsHyperfabricExact`
  - supplies multi-layer finite state/coupling patterns and the explicit rule that merged visible endpoints need not erase path residual.
- `DASHI.Core.SituatedFibreDynamicsEverything`
  - supplies observer refinement, intersectional non-factorability, query-indexed adequacy, trajectory residual/history, multiaxial fibres, and refinement scheduling.
- `DASHI.Core.IntersectionalNonFactorability`
  - supplies the generic structural non-factorability calculus only. Social intersectionality remains source-bounded motivation, not a biological theorem or molecular ontology.
- `DASHI.Core.AttributedSourceCore`, snowball attribution, external-identity availability, and typed provenance dependency graphs
  - supply DOI/QID/PDB/UniProt/source-role/provenance discipline. Citation and identity never manufacture proof, mechanism, or biological authority.
- Existing protein witnesses
  - Feng/TRPA1 single-residue thermal adaptation is the residue/query witness.
  - AdK same-sequence/conformation/observer/calibration work is the geometry/context/dynamics witness.

## 3. Rejected implementation shapes

### 3.1 Monolithic `ProteinObservation` record

A single record containing genome, translation context, sequence, conformation, environment, metabolism, history, assay, provenance, and outputs would be easy to construct but would flatten dependencies and turn a situated biological process into a bag of fields. It would underuse the repository's dependent-fibre machinery.

### 3.2 Expanding `ProteinRecoveryBoundary` into mutable world state

Extending the recovery boundary until it contains every temporal and observational coordinate would blur the distinction between a recovery interface and a time-indexed state model. It would also make an existing canonical owner absorb unrelated observer/history/runtime concerns.

### 3.3 Recommended: thin situated hyperfabric

Add a new protein-layer composition whose coordinates reference existing carriers. This keeps identity, translation, realised protein state, environment, metabolism, history, observer, and residual dependency as distinct fibres.

## 4. Core state shape

The conceptual state is:

```text
P_t = Sigma g:G_t.
      Sigma c:C_t.
      Sigma x:X_t(g,c).
      Sigma e:E_t.
      Sigma m:M_t.
      Sigma h:H_{<=t}.
      Sigma o:O_t.
      R_t(g,c,x,e,m,h,o)
```

The implementation need not encode this as one deeply nested raw Sigma if existing records/dependent owners provide a clearer interface. The semantic coordinates are mandatory, but their concrete representation should follow existing repo patterns.

Coordinates:

- `g` — genomic/encoded state or genomic carrier.
- `c` — active translation/reading context.
- `x` — realised protein state; may include sequence, residue state, modification, conformation, ensemble/profile, occupancy, or other protein-local state.
- `e` — local chemical/physical environment.
- `m` — metabolic/resource state relevant to the declared query.
- `h` — retained trajectory/history residual through time `<= t`.
- `o` — situated observer/assay state.
- `R_t` — admissibility/dependency residual stating which coordinate combinations are actually justified.

No theorem may assume that every coordinate is needed for every query.

## 5. Coordinate stability roles

Introduce a local role classification, not a universal stability ontology:

```text
CoordinateRole =
  identityStable
  | slowlyVarying
  | contextual
  | fastDynamical
  | historyDependent
  | observerDependent
```

A role assignment is itself context/time-window relative. Holding a coordinate fixed in one experiment does not prove global stability.

Typical examples are descriptive only:

- genomic locus identity — often identity-stable over a short experiment;
- residue sequence — often slower-changing than conformation;
- modification state — contextual;
- conformation/ligand occupancy — fast dynamical;
- susceptibility after prior exposure — history-dependent;
- FRET/crystal/thermal/activity readout — observer-dependent.

## 6. Observer model

The observer belongs at the state/query interface rather than being treated as a transparent final readout.

Minimum observer surface:

```text
SituatedProteinObserver =
  ( assay,
    samplingWindow,
    resolution,
    perturbation,
    localContext,
    sourceProvenance )
```

Different assays are different projections of the richer process. A FRET distance, crystal structure, thermal assay, activity assay, and sequencing readout are not interchangeable observations and none is definitionally equal to "the protein state".

## 7. Query-indexed adequacy

For a projection `pi` and protein query `Q`, reuse the repository's `FactorsThrough` / query-adequacy machinery:

```text
Q(P_t) ?= Qhat(pi(P_t))
```

The design requires positive factorisation only where constructively witnessed. A collision produces a refinement obligation:

```text
same coarse observation
+ different query answer
-> retain separating coordinate
-> local refinement
-> admissibility
-> consumer-safe projection
```

Reweighting or relabelling the same coarse projection is not a repair when the missing coordinate has been erased.

## 8. First implementation tranche: no new biological claims

Tranche one is structural only. It introduces the generic situated protein carrier and instantiates exactly two already-owned witnesses.

### 8.1 TRPA1 witness

Reuse the Feng/TRPA1 owner as the existing source-bounded biological witness:

```text
protein identity -> protein identity + pore-residue state
```

The consumer is the already formalised thermal-response query. The new generic layer may show that protein identity alone is too coarse for that consumer, but it must not add or strengthen any Feng et al. biological claim.

### 8.2 AdK witness

Reuse the existing AdK owner as the independent conformation/context witness:

```text
sequence/protein identity -> context + retained geometric/observer coordinates
```

The first generic instantiation should consume existing paid facts only: same-sequence open/closed conformation separation and/or query-indexed geometry/observer separation. It must not require new Figure-5 numerics.

### 8.3 Success criterion for tranche one

Tranche one succeeds when one generic protein situated-hyperfabric interface supports both witnesses without collapsing their domain-specific fibres and without adding new empirical claims.

## 9. Temporal production/metabolic chain: tranche two, not tranche one

The next tranche may compose the following time-indexed chain:

```text
DNA / genomic carrier
-> transcription + reading frame
-> translation context
-> nascent sequence
-> folding/chaperone/modification environment
-> conformational ensemble
-> local chemical/metabolic context
-> binding / catalytic / signalling action
-> cellular consequence
-> feedback onto expression/environment
```

This is not a one-way deterministic pipeline. Later coordinates may feed back into expression, environment, translation/folding conditions, and future susceptibility.

Tranche two must reuse existing cell/metabolism/translation owners and keep unsupported bridges as explicit obligations.

## 10. History-dependent susceptibility

The generic carrier must be able to retain history even when visible endpoints coincide:

```text
pi(P_t^1) = pi(P_t^2)
and H_{<=t}^1 != H_{<=t}^2
```

This alone does not prove a susceptibility difference. A source-backed producer is required before concluding:

```text
Q_susceptibility(P_t^1) != Q_susceptibility(P_t^2)
```

Tranche one only exposes the carrier and reuse seam. A real history-dependent protein witness belongs to a later source-acquisition tranche.

## 11. Intersectionality attribution boundary

The protein layer may reuse `IntersectionalNonFactorability` as DASHI's generic mathematical theorem about information loss under coarse projections.

It must not:

- redefine social intersectionality as molecular biology;
- attribute protein multi-axis dynamics to Crenshaw or McCall;
- transfer social-science authorship/authority into biological claims;
- describe multiple protein coordinates as "intersectional" evidence of biological sufficiency.

The source-role statement is:

```text
Crenshaw/McCall source role
-> motivation for non-reductive multi-axis analysis

protein situated-hyperfabric theorem
= DASHI synthesis
```

## 12. Attribution and external identity rules

All empirical instantiations retain the existing source discipline.

Publication/entity identities may include DOI, PMID, PMCID, QID, UniProt, PDB, canonical URL, source role, manifestation, exact locator, method, and uncertainty where available.

Required rules:

```text
citation != proof
QID != scientific authority
DOI != biological mechanism
PDB identity != dynamics
UniProt identity != experimental condition
same identifier != same observational role
unresolved identity != negative evidence
```

A source pays only the proposition/measurement actually acquired at its exact role and locator. Generic protein factorisation/refinement theorems remain DASHI synthesis.

## 13. Non-promotions

The first owner and validation surface must encode these fail-closed boundaries:

```text
genome !-> expressed protein state
sequence !-> conformation
conformation !-> function
current visible state !-> history
metabolic substrate present !-> reaction flux
observer agreement !-> world completeness
multiple useful axes !-> sufficiency for every query
agentic control vocabulary !-> human-like agency
citation/QID/DOI/PDB/UniProt !-> biological authority
TRPA1 residue result !-> AdK mechanism
AdK geometry/rate result !-> TRPA1 thermal mechanism
```

## 14. Proposed tranche-one files

Implementation plan should refine names after repo inspection, but the intended surfaces are:

- `DASHI/Biology/Protein/ProteinSituatedHyperfabricExact.agda`
  - generic time-indexed situated protein carrier;
  - coordinate-role classification;
  - observer and admissibility interfaces;
  - query-relative projection hooks;
  - attribution/non-promotion boundary.
- `DASHI/Biology/Protein/ProteinSituatedHyperfabricValidation.agda`
  - RED-first contract for the generic owner and two witness instantiations.
- `DASHI/Biology/Protein/TRPA1SituatedProteinWitnessExact.agda`
  - thin adapter over existing Feng/TRPA1 owner; no new biology.
- `DASHI/Biology/Protein/AdenylateKinaseSituatedProteinWitnessExact.agda`
  - thin adapter over existing AdK owner; no new numerics or mechanism claims.
- Focused protein validation root update rather than immediate widening of `DASHI.Biology.Everything`, unless the implementation plan finds an already-established rollup pattern that is a better fit.

No CI workflow work is part of this design.

## 15. Testing and TDD contract

Implementation is RED-first.

Required validation behaviours before production owners exist:

1. Generic situated carrier path is required and absent.
2. TRPA1 adapter is required and absent.
3. AdK adapter is required and absent.
4. Validation pins the core non-promotions.
5. Validation requires both witnesses to use the same generic interface while retaining distinct domain-specific fibre coordinates.
6. Validation requires attribution role separation: source claims remain source-owned; generic theorem remains DASHI-owned.

Because the user has explicitly asked not to use CI, verification for this tranche is limited to repository-level RED path checks and source/diff inspection unless a local compiler execution path becomes available independently of CI. No Agda success may be claimed without an observed compiler receipt.

## 16. Error handling / fail-closed behaviour

The new layer must fail closed when:

- a query has no adequacy proof;
- a coordinate is unresolved;
- a source/manifestation/locator is not same-object paid;
- history dependence is hypothesised without a producer;
- a cross-domain adapter attempts to transfer empirical mechanism;
- a source identity is mistaken for measurement authority;
- an observer projection is promoted to complete world state.

Unknown or unpaid coordinates remain typed residuals/obligations, not default values.

## 17. Roadmap after tranche one

After the generic owner and the TRPA1/AdK adapters exist, the next roadmap order is:

1. temporal production/metabolic-chain composition using existing translation, protein, cell, and metabolism owners;
2. source-backed history-dependent protein susceptibility witness;
3. consumer-indexed minimal-fibre selection across identity/residue/conformation/environment/history/observer coordinates;
4. broader protein instantiations only where they add an independent failure/repair pattern;
5. no further AdK-specific infrastructure unless it pays a real outstanding empirical cell or is required by a generic consumer.

The programme-level theorem target is deliberately modest and precise:

```text
Protein identity is a query-relative projection, not a complete predictive state.
For each declared protein query, retain only the situated fibre required for that query, and refine locally when a paid collision proves the current projection inadequate.
```

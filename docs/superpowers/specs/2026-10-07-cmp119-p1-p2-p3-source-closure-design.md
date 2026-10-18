# CMP119 P1/P2/P3 Source Closure Design

Date: 2026-10-07
PR: #1050 (`agent/grqft-ten-d1-readout-maxcut-20260924`)

## Goal

Close the live CMP119 cosmology/antigravity source frontier below the historical P1/P2/P3 abstraction layer without introducing synthetic same-object identifications, false finite=continuum equalities, or physics assumptions disguised as compiler lemmas.

Success means the preferred source route reaches its terminal sign/covariance consumers with:

1. no primitive signed-R144 covariance axiom;
2. no CMP119-specific trace-scalar weld if the renormalized Hilbert/Weyl Ward identity can be instantiated on the existing Local-C package;
3. no exact finite-cutoff Local-C F² = physical-Haar F² equality;
4. no redundant Round109/Eq.(2.23) sign machinery on the preferred route;
5. every surviving source law stated on the actual source/renormalized carriers and normalization used downstream;
6. exact-head Agda CI before any claim of kernel closure.

## Current live frontier

Overlay S already recuts the programme to:

- **S1** — construct the actual CMP109/116 one-parameter source path in the abstract `Background` carrier and prove B4 equivariance with the signed ten-slot source action;
- **S2** — instantiate or internally derive the renormalized Hilbert/Weyl Callan–Symanzik trace-anomaly Ward identity on the exact Local-C stress/F² pair;
- **S3a** — select the R129 completed marked source as the physical F² source;
- **S3b** — identify/construct the finite factorized source expectation as the literal physical Haar expectation, so the Local-C and physical-Haar F² readouts are one common limit.

The following are already compiler-owned or retired:

- primitive P1 signed R144 covariance;
- independent BC2 derivative semantics;
- independent Round143 linearity;
- CMP119-specific trace scalar identity;
- exact finite F² = continuum F² equality;
- finite-DGamma/R109-tail preferred sign transport;
- Eq.(2.23) vacuum-gap preferred sign transport.

## Design principles

### 1. Source-native first

Every new theorem must be formulated on the most concrete existing source carrier that already owns the relevant object. We will not introduce arbitrary intermediate scalar or tensor carriers merely to bridge names.

### 2. Same-object by construction where possible

If two lanes can be recharted onto the same carrier, prefer definitional or structural identity over a post-hoc equality field.

### 3. Continuum statements are limits, not finite equalities

For renormalized Local-C F², the finite Wilson/Haar quantity and continuum Local-C readout must meet through one finite approximation sequence and uniqueness/congruence of its limit. No theorem may identify one arbitrary finite cutoff exactly with the renormalized continuum operator unless that equality is source-proved.

### 4. Imported physics authority must be exact and normalized

If S2 cannot be derived from repository RG/Hilbert data, the imported Ward theorem must be stated directly on the exact Local-C stress/F² pair and exact SU(2) coefficient convention. Applicability must come from existing `ShortDistanceAFMatching`; no additional scalar weld is permitted.

### 5. Max-cut preferred route only

Round109 finite-tail and Eq.(2.23) sign lanes remain useful alternate diagnostics, but they must not re-enter the preferred scheduler unless they remove one of S1/S2/S3 rather than add work.

## Workstream S1 — actual CMP109/116 source-path geometry

### Existing machinery

`CMP119CosmologyP1PreferredPathDefinedPresentCutExact` already proves that, given:

- source-potential Euclidean geometry;
- a source path
  `Background → SymmetricTensorComponent4 → ℝ → Background`;
- signed B4 equivariance of that path;
- ordinary signed path-derivative laws;

then BC2 first variation is definitionally the path derivative, Round143 linearity follows, and signed finite D1/R144 covariance is compiler output.

### New mathematical target

Construct the path on the actual CMP109/116 `Background` carrier rather than leaving `sourcePath` and `sourcePathCovariant` as data fields.

Preferred construction order:

1. inspect the literal source continuation/background operations already owned by CMP109/116;
2. if a source-addition/scaling operation exists, define the path as the affine source deformation along the selected symmetric metric slot;
3. otherwise use the actual compact-gauge exponential/source action only if the source carrier supports it directly;
4. prove the signed B4 equivariance from the existing hypercubic action and the source operation laws;
5. instantiate `PreferredPathDefinedPresentCutSource` and retire S1.

### Trust boundary

Do not assume `Background` is a vector space or compact Lie group unless the live source module provides those operations. If only a weaker torsor/action structure exists, formulate the path with that structure.

## Workstream S2 — renormalized Hilbert/Weyl Ward identity

### Existing machinery

`CMP119CosmologyP2RenormalizedHilbertWardAuthorityExact` already places the imported theorem on:

- the exact Local-C stress tensor;
- the exact Local-C F² operator;
- the exact SU(2) trace coefficient convention;
- the existing `ShortDistanceAFMatching` applicability witness.

### Preferred internal derivation

Attempt to derive the Ward identity from repository data in this order:

1. Hilbert stress definition / metric variation of the renormalized effective action;
2. Weyl rescaling identity for the action/effective action;
3. Callan–Symanzik RG equation on the same Local-C family;
4. beta-function normalization already used by `RealSU2TraceConvention`;
5. AF matching to identify the renormalized operator basis;
6. conclude
   `trace(T_R) = coefficient(beta,g) * [F²]_R`
   on the exact Local-C objects.

### Fallback imported theorem

If one of the renormalization steps is not represented in-repo, keep exactly one `standardImported` Ward authority, but remove all auxiliary calibration fields that can be proved from the repository normalization.

The imported theorem must cite primary sources and state only the operator identity actually required downstream.

## Workstream S3 — physical F² common-limit closure

### Existing machinery

The branch already has:

- R129 completed marked-curvature F² on the same completion carrier;
- Local-C recharting where Local-C F² is definitional after selecting that marked source;
- finite→Local-C anomaly limit transport;
- physical-Haar expectation representation as a finite CMP119 expectation limit;
- `LocalCF2PhysicalHaarCommonLimit`, which proves equality of the two continuum readouts once their finite sequences are pointwise the same.

### S3a target

Construct the R129 selected marked source specifically as the physical F² source.

Required evidence should be pushed to the lowest source representation:

- identify the selected curvature polynomial with the physical F² polynomial;
- use the existing R129 completed marked-source carrier;
- make Local-C operator equality definitional through the existing rechart;
- avoid any post-hoc `LocalOperator` equality field if carrier identity suffices.

### S3b target

Prove that the finite approximation sequence used by Local-C transport is the same sequence represented by the physical Haar expectation.

Preferred route:

1. instantiate both sides from the same selected finite state/measure family;
2. use the existing constant selected-state construction where available;
3. prove the quadrature/finite-factorized expectation is the literal physical Haar expectation on that state family;
4. prove pointwise equality of the finite F² sequence;
5. invoke `LocalCF2PhysicalHaarCommonLimit` to get the continuum equality;
6. transport strict physical Haar positivity to Local-C F² positivity.

If exact finite quadrature equality is unavailable, use the existing combined vanishing-error representation and uniqueness of the common limit; do not strengthen to finite equality.

## Composition / terminal theorem

After S1–S3 are paid:

1. S1 constructs signed finite D1 covariance and removes primitive P1;
2. S2 gives the Local-C renormalized trace anomaly identity;
3. S3 gives positivity of the same Local-C F² readout from the physical Haar source;
4. the existing SU(2) coefficient sign gives negative Local-C trace;
5. existing R136/Local-C same-stress + Hilbert trace/readout compiler gives negative R136 trace;
6. existing marked-OS/vacuum compiler gives negative active stress and positive matter acceleration contribution under positive gravity factor.

No finite-DGamma/R109-tail or Eq.(2.23) source-envelope theorem is required on this preferred composition.

## Files expected to change

Existing files likely to be strengthened or instantiated:

- `CMP119CosmologyP1PreferredPathDefinedPresentCutExact.agda`
- `CMP119CosmologyP1PreferredPresentCutSourceExact.agda`
- `CMP119CosmologyP2RenormalizedHilbertWardAuthorityExact.agda`
- `CMP119CosmologyP2HilbertTraceAnomalyExact.agda`
- `CMP119CosmologyP3MarkedCurvatureLocalCRechartExact.agda`
- `CMP119CosmologyP3R129RechartedLocalCF2Exact.agda`
- `CMP119CosmologyP3SelectedStateHaarQuadratureExact.agda`
- `CMP119CosmologyP3ApproximateExpectationHaarExact.agda`
- `CMP119CosmologyP3LocalCF2PhysicalHaarCommonLimitExact.agda`
- `CMP119CosmologyP23HilbertHaarToR136SignExact.agda`
- the live Pareto overlay / latest frontier owner;
- focused exact-head workflows.

New source-specific constructor modules should be added only when an existing owner would otherwise mix unrelated responsibilities.

## Testing and verification

Each source closure is developed TDD-style:

- add or tighten a regression theorem naming the desired source constructor/closure;
- implement the smallest source-native theorem that makes it pass;
- add no postulates or unsafe options;
- preserve explicit `conditional`/`standardImported` proof levels until genuinely discharged.

Focused CI should typecheck:

- S1 source-path construction through signed R144 covariance;
- S2 Ward identity instantiation/internal derivation;
- S3 R129/Local-C/Haar common-limit chain;
- terminal Hilbert–Haar→R136 sign composition;
- latest Pareto/frontier accounting.

Completion claim requires an exact-head Agda kernel run. If GitHub Actions still does not trigger, the implementation may be reported as source-written/static-audited only.

## Non-goals

- proving a full Friedmann trajectory;
- reviving the Eq.(2.23) vacuum-gap lane as preferred;
- proving arbitrary off-diagonal GRQFT observables unrelated to the terminal route;
- replacing the published RG/trace-anomaly theorem with a stronger claim than the literature/source normalization supports;
- assuming exact finite=continuum equality.

## Exit criteria

The design is complete when the live preferred frontier can truthfully state one of:

### Strong exit

- S1, S2, S3 are all machine-checked;
- remaining novel source attachment count = 0;
- remaining imported authority count = 0;
- exact-head focused CI passes.

### Acceptable literature exit

- S1 and S3 are machine-checked;
- S2 is one exact `standardImported` renormalized Hilbert/Weyl Ward identity on the correct Local-C pair with its normalization proved in-repo;
- remaining novel source attachment count = 0;
- remaining imported authority count = 1;
- exact-head focused CI passes.

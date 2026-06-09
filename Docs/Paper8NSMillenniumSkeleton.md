# Paper 8 Skeleton: Navier-Stokes Regularity As The Millennium Tower Analogue Of Yang-Mills Mass Gap

Date: `2026-05-29`
Status: substantive skeleton plus introduction; docs-only; fail-closed; non-promoting
Owner lane: `Manager A / worker A5`

## Target Framing

Primary target journals or venues should be chosen for formal methods,
mathematical physics, or proof-engineering transparency rather than for a
claimed solution of a Millennium problem.  Plausible targets include
`Journal of Formalized Reasoning`, `Logical Methods in Computer Science`,
`Mathematical Structures in Computer Science`, or a mathematical-physics
workshop track that accepts formal proof-boundary reports.  A Clay-facing or
analysis-journal submission would require a different document: a complete
continuum Navier-Stokes regularity proof, not the tower-isomorphism and
receipt-boundary paper described here.

This paper is therefore framed as a formal-methods contribution.  It records
how the DASHI receipt system exposes the same structural proof obligations in
two Millennium-adjacent towers:

- the Yang-Mills mass-gap tower, where finite-depth and local finite-carrier
  spectral-gap evidence is present but continuum Clay promotion is false;
- the Navier-Stokes regularity tower, where finite-depth weak-solution,
  energy, vorticity, enstrophy, and BKM-style rungs are present but continuum
  smoothness and Clay promotion are false.

The contribution is not a proof of Navier-Stokes regularity and not a proof of
Yang-Mills mass gap.  The contribution is the formal structural isomorphism:
both lanes have inhabited finite-depth control, both attempt a tower or
colimit lift, both hit a continuum promotion obligation, and both require an
external authority boundary before any Millennium-facing statement can be
accepted.

## Abstract Draft

We present a proof-engineering skeleton for comparing two DASHI Millennium
frontier towers: Yang-Mills mass gap and Navier-Stokes regularity.  On the
Yang-Mills side, the current Agda surfaces record finite-depth lattice or
finite-carrier spectral-gap evidence, a depth-indexed pro-object shape, a
quantifier-exchange boundary, a colimit/Hamiltonian lift thread, and explicit
Clay-facing blockers.  On the Navier-Stokes side, the current Agda surfaces
record a finite carrier weak formulation, divergence-free/Leray interfaces,
finite-depth L2 energy estimates, vorticity equation rungs, enstrophy control,
finite-depth BKM continuation rungs, and explicit continuum regularity
blockers.  We show that these receipts instantiate a common four-stage tower
schema:

```text
finite-depth local control
  -> depth-indexed tower or pro-object family
  -> tower/colimit lift attempt
  -> continuum promotion and external authority obligation
```

The formal result is a structural isomorphism of proof obligations, not an
analytic theorem.  In particular, finite-depth Navier-Stokes estimates do not
exclude continuum blowup, finite-depth Yang-Mills gaps do not produce a
continuum Hamiltonian mass gap, and neither lane supplies a Clay authority
receipt.  The value of the comparison is fail-closed: it identifies exactly
which proof obligations must be inhabited before the repo can promote a
Millennium claim.

## Introduction

The DASHI codebase contains two recurring patterns that should be separated
from any claim of solving a Millennium problem.  First, it contains finite
formal surfaces: typed carriers, bounded towers, finite-depth witnesses,
canonical receipts, and boolean promotion fields.  Second, it contains
continuum and authority boundaries: Hilbert completion, self-adjoint
Hamiltonians, continuum PDE regularity, uniform estimates, Osterwalder-Schrader
or BKM-style analytic authority, and external Clay acceptance.  Paper 8 is
about the interface between these two patterns.

The motivating observation is that the current Navier-Stokes regularity lane
and the current Yang-Mills mass-gap lane have the same formal shape even
though their mathematical content differs.  Yang-Mills mass gap asks for a
positive lower spectral gap in a continuum quantum gauge theory.  Navier-Stokes
regularity asks for global smoothness or controlled breakdown exclusion for
the three-dimensional incompressible flow problem.  In DASHI, both are staged
as towers because the machine-checkable part is finite, while the theorem
asked by the Millennium statement is continuum and uniform.

The Yang-Mills side is anchored by
`DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface`,
`DASHI.Physics.Closure.ColimitGapLiftOnHamiltonian`,
`DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation`, and
`DASHI.Physics.Closure.YangMillsMassGapBoundary`.  These surfaces record
finite-depth lattice-gap or finite-carrier spectral-gap receipts, the
depth-indexed pro-object family, the pointwise-depth versus uniform-continuum
quantifier exchange, a Hamiltonian/colimit lift thread, and explicit false
promotion bits for continuum mass gap, physical Stone spectral lower bound,
and Clay-facing acceptance.  The repo can say that certain finite witnesses
are present; it cannot say that the continuum Yang-Mills mass-gap theorem is
proved.

The Navier-Stokes side is anchored by
`DASHI.Physics.Closure.NavierStokesWeakSolutionInterface` and
`DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt`.  These surfaces
record a carrier-level weak formulation, divergence-free and Leray projection
interfaces, finite-depth L2 energy estimates, finite-depth enstrophy and
vorticity control, finite-depth vorticity equation rungs, finite-depth
BKM-style continuation criteria, and a `ContinuumRegularityObligation`.
Again, the repo can say that finite tower rungs are inhabited.  It cannot say
that finite-depth energy or vorticity estimates exclude continuum blowup, that
the BKM criterion has been discharged in the continuum, or that the Clay
Navier-Stokes regularity problem is solved.

Paper 8 turns this parallel into a controlled formal claim.  The claim is that
there is a structural isomorphism between the two proof-obligation towers.  By
structural isomorphism we mean a correspondence of roles, not an equivalence
of PDE and gauge theory.  A Yang-Mills finite-depth spectral-gap receipt
corresponds to a Navier-Stokes finite-depth energy/enstrophy/vorticity receipt
as a local-control rung.  A Yang-Mills depth-indexed pro-object corresponds to
a Navier-Stokes depth-indexed weak-solution and BKM tower as the family over
finite depths.  A Yang-Mills colimit/Hamiltonian spectral lift corresponds to
a Navier-Stokes continuum regularity lift as the promotion attempt.  A
Yang-Mills Clay mass-gap authority boundary corresponds to a Navier-Stokes
Clay regularity authority boundary as the external acceptance layer.

This positioning is deliberately conservative.  The paper should be useful
because it makes overclaiming mechanically harder.  Each stage names the
receipt that is available and the receipt that is missing.  The paper does not
replace analytic estimates with formal analogy, and it does not infer
Navier-Stokes regularity from Yang-Mills mass gap or vice versa.  It provides a
shared scaffold for future workers: if a worker claims progress, the claim can
be located as finite-depth control, tower compatibility, colimit or continuum
lift, or external authority.  If the claim crosses from one layer to the next,
the required receipt must be explicitly inhabited.

## 1. The Structural Isomorphism Of The Two Towers

The central object of Paper 8 is the following tower schema:

```text
T0 finite local control
T1 uniform finite-depth family
T2 tower or colimit lift
T3 continuum promotion obligation
T4 external authority boundary
```

The schema is intentionally typed by proof role rather than by mathematical
domain.  It does not say that vorticity is a gauge curvature or that a
Hamiltonian spectral gap is a PDE continuation criterion.  It says that both
lanes need the same kind of promotion discipline: a pointwise finite witness
must not be silently reclassified as a uniform continuum theorem.

### 1.1 Yang-Mills Mass Gap Tower

The Yang-Mills lane currently inhabits the finite side and blocks the
continuum side.

At `T0`, `FiniteDepthLatticeGapReceipt` records a positive gap for a fixed
lattice depth before the continuum limit.  The stronger
`BalabanRGMassGapReceiptSurface` records that `finiteDepthMassGapPromoted` and
`localFiniteCarrierSpectralGapPromoted` are true inside the finite-carrier
scope.  These are local control receipts.

At `T1`, `FiniteDepthLatticeGapProObjectReceipt` records the depth-indexed
family of finite lattice-gap receipts.  `MassGapDepthIndexedVsContinuumStatus`
and `MassGapQuantifierExchangeReceipt` make the key quantifier exchange
explicit: `forall d, Delta_d > 0` is not the same as `exists epsilon, forall
d, Delta_d >= epsilon`.  The latter uniform continuum gap is not discharged.

At `T2`, `ColimitGapLiftOnHamiltonianReceipt` and
`ColimitHamiltonianGapThreadReceipt` thread the finite witness chain into the
Hamiltonian/colimit target.  This is a lift attempt, not a completed analytic
promotion.  The named blockers include reflection positivity, polymer-cluster
convergence, physical Hamiltonian spectral lift, and Clay continuum authority.

At `T3`, `ContinuumClayMassGapReceiptObligation` records the components that
would be needed before a Clay-facing mass-gap claim could be promoted:
Hilbert self-adjointness, the pressure-bound-to-Yang-Mills spectral theorem,
the continuum Yang-Mills construction, and an external Clay or authority
receipt.  The canonical dependency receipt keeps internal Clay composition
false.

At `T4`, `YangMillsMassGapBoundaryReceipt` and the authority surfaces inside
`BalabanRGMassGapReceiptSurface` separate candidate literature or preprint
lineages from accepted authority.  The receipt names include
`VerifiedMassGapAuthorityStatusReceipt`,
`FiniteDepthVsContinuumClayAuthorityBoundary`, and
`U1ConditionalPreprintAuthorityBoundary`.  Their shared boundary is that
external candidate evidence, preprint authority, and finite-carrier evidence
do not promote the continuum Clay theorem.

### 1.2 Navier-Stokes Regularity Tower

The Navier-Stokes lane has the same proof-role shape.

At `T0`, `NavierStokesWeakSolutionInterfaceReceipt` records the finite carrier
weak formulation.  Inside `NavierStokesRegularityTowerReceipt`, the available
local rungs include `DivergenceFreeCarrier`,
`NavierStokesWeakSolutionInterface`, `EnstrophyBound`,
`FiniteDepthVorticityControl`, `FiniteDepthL2EnergyEstimate`,
`FiniteDepthVorticityEquationRung`, and `FiniteDepthBKMVorticityIntegral`.
These are finite-depth controls over the carrier tower.  Their false promotion
fields state that they do not produce continuum smoothness.

At `T1`, the receipt quantifies these rungs over depth: finite-depth weak
solutions, enstrophy bounds, vorticity control, energy estimates, vorticity
equation rungs, and BKM continuation criteria are available as a
depth-indexed family.  This is the Navier-Stokes analogue of a pro-object
family: the repo has a tower of finite formal witnesses, not a completed
continuum PDE object.

At `T2`, the receipt explicitly reuses the Gate 2 colimit-gap lift only as an
analogy.  The field `colimitRegularityLiftReusedOnlyAsAnalogy` is true, while
`continuumRegularityLiftConstructed` is false.  This is the exact analogue of
the Yang-Mills Hamiltonian/colimit lift boundary: the tower shape is present,
but the continuum theorem is not.

At `T3`, `ContinuumRegularityObligation` names the analytic obligations:
smooth divergence-free initial data, Leray projection and pressure transport,
continuum BKM authority, and Clay regularity acceptance.  The receipt keeps
`continuumClayNavierStokesPromoted` false.  The BKM-related surfaces make the
same point locally: a finite-depth BKM integral or finite-depth continuation
criterion does not discharge continuum blowup exclusion.

At `T4`, the authority boundary is external.  Paper 8 may cite classical PDE
criteria such as Beale-Kato-Majda as mathematical context, but the repo must
not treat citation or analogy as an inhabited authority receipt.  The current
field `continuumBKMAuthorityAvailable` is false, and the Clay acceptance
obligation remains open.

### 1.3 Isomorphism Map

The isomorphism can be presented as the following role-preserving map:

| Tower role | Yang-Mills mass-gap side | Navier-Stokes regularity side |
| --- | --- | --- |
| `T0`: finite local control | `FiniteDepthLatticeGapReceipt`, local finite-carrier spectral gap | finite weak formulation, L2 energy, enstrophy, vorticity, BKM rungs |
| `T1`: uniform finite-depth family | `FiniteDepthLatticeGapProObjectReceipt`, pointwise depth gap family | depth-indexed weak-solution and regularity tower |
| `T2`: lift attempt | `ColimitGapLiftOnHamiltonianReceipt`, `ColimitHamiltonianGapThreadReceipt` | `colimitRegularityLiftReusedOnlyAsAnalogy`, regularity lift target |
| `T3`: continuum promotion | `ContinuumClayMassGapReceiptObligation` | `ContinuumRegularityObligation` |
| `T4`: external authority | Clay/YM boundary, preprint and alternative authority receipts, accepted authority absent | BKM/Clay regularity authority obligation, accepted authority absent |

The map preserves the most important negative invariant:

```text
finite-depth inhabited != continuum promoted
```

For Yang-Mills, this invariant blocks the move from pointwise depth gaps to a
uniform continuum mass gap.  For Navier-Stokes, it blocks the move from
finite-depth energy or vorticity control to global continuum smoothness.  In
both cases the missing step is not cosmetic.  It is the hard analytic content
of the Millennium-facing problem.

### 1.4 Honest Non-Proof Caveat

Paper 8 should state the caveat in the introduction, again in Section 1, and
again in the conclusion: this is not a proof of either Millennium problem.
The structural isomorphism is a contribution to claim governance and proof
engineering.  It identifies where the current formal artifacts stop and which
receipts would be needed to go further.  Any future version that claims more
must replace the false fields with inhabited receipts, including a genuine
continuum promotion theorem and the relevant external acceptance boundary.

## 2. Proposed Remaining Paper Skeleton

Section 2 should formalize the common tower schema as a small definition:
objects are receipt layers, arrows are promotion obligations, and forbidden
arrows are exactly the promotion jumps whose boolean receipts remain false.

Section 3 should read the Yang-Mills receipts in detail:
`BalabanRGMassGapReceiptSurface`, `ColimitGapLiftOnHamiltonian`,
`ContinuumClayMassGapReceiptObligation`, and `YangMillsMassGapBoundary`.

Section 4 should read the Navier-Stokes receipts in detail:
`NavierStokesWeakSolutionInterface` and
`NavierStokesRegularityTowerReceipt`.

Section 5 should give the side-by-side blocker lattice and prove only the
governance theorem: any promoted Millennium claim must consume the continuum
promotion receipt and the external authority receipt for its lane.

Section 6 should discuss target venue positioning, related formalization
efforts, and why the paper is submitted as formal proof-boundary work rather
than as a Clay solution.

## Blocker Map

Current blockers for any stronger Navier-Stokes claim:

- no continuum smooth divergence-free initial-data encoding;
- no continuum pressure projection and Leray transport theorem;
- no uniform enstrophy persistence to the continuum;
- no uniform BKM vorticity integral to the continuum;
- no continuum BKM theorem authority receipt;
- no continuum Navier-Stokes regularity theorem;
- no Clay external acceptance receipt.

Current blockers for any stronger Yang-Mills claim:

- no reflection positivity or transfer-matrix positivity receipt sufficient
  for the continuum construction;
- no spectral-projection isolation and continuum-limit stability theorem;
- no physical Stone generator equals Yang-Mills Hamiltonian theorem;
- no self-adjoint domain for the real quotient Hamiltonian;
- no selected-carrier gap transport to the physical spectrum;
- no accepted continuum Clay mass-gap authority receipt.

The publishable claim is therefore narrow: DASHI has a formal, fail-closed
isomorphism between the proof-obligation towers.  The Millennium theorems
remain open at the continuum promotion and external authority layers.

# 6. GR Boundary and Future Work

This section is a boundary statement, not a promotion claim. The present paper
does not prove non-flat general relativity, a sourced discrete Einstein
equation, Schwarzschild recovery, continuum GR recovery, GRQFT closure, or W4
matter/stress-energy closure. It records the typed interfaces that make those
claims precise enough to pursue in later work.

The current positive GR-adjacent result is limited to the finite-difference
surface: prime-indexed finite differences commute on the current carrier, and
the antisymmetrized double-difference diagnostic is therefore zero at that
level. This is useful because it identifies the exact adapter boundary between
the arithmetic carrier and a future non-flat connection. It is not yet a
Riemann tensor, a covariant derivative, a Bianchi identity, or an Einstein
tensor.

## Non-flat GR adapter boundary

The first future-work item is to inhabit the adapter from prime finite
differences to a non-flat connection target. The current boundary is named by
`PrimeDifferenceToRiemannConnectionAdapterReceipt` and the uninhabited bundle
`PrimeDifferenceToRiemannConnectionAdapterBundle`. The exact blocker is
`missingPrimeDifferenceToRiemannConnectionAdapter`.

Until that adapter bundle is constructed for a concrete target, the paper may
only say that the finite-difference commutation theorem provides a candidate
source equality for a later connection adapter. It may not say that a non-flat
connection, Riemann curvature carrier, covariant divergence law, contracted
Bianchi identity, or Einstein tensor has been derived.

The next internal construction would have to supply carrier-internal non-flat
CRT/J connection or shift data. The first kill condition for that thread is
`missingCarrierInternalNonFlatConnectionFromCRT`. CRT/J period diagnostics and
flat finite-radius checks do not by themselves supply connection coefficients,
parallel transport, or curvature.

## Discrete Einstein tensor

A discrete Einstein tensor requires a sequence of typed constructions that are
not present in the current proof surface:

1. non-flat connection or shift data on the selected finite-radius carrier;
2. discrete Riemann curvature, such as a bracket or parallel-transport defect;
3. curvature symmetries and a finite-radius Bianchi witness;
4. Ricci contraction and scalar trace;
5. metric compatibility and contraction laws;
6. the tensor law `G_mu_nu = Ricci_mu_nu - 1/2 R g_mu_nu`.

The current exact blockers include `missingCurvatureToRicciContraction`,
`missingFiniteRBianchiWitness`, and `missingDiscreteEinsteinTensorLaw`. Because
these blockers are still live, any discrete Einstein tensor language in this
paper must remain diagnostic or request-only.

The sourced equation is even more constrained. A future sourced law would have
to consume the theorem-facing W4 interface
`EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt`. That receipt
is currently blocked by `missingW4MatterStressEnergyInterfaceReceipt`, so
`matterFieldFromW4`, `stressEnergyTensorFromW4`, and
`G_mu_nu = 8 pi T_mu_nu` remain obligation shapes rather than constructed
objects.

## Schwarzschild boundary

The Schwarzschild lane is currently a request surface. Flat finite-radius
Minkowski diagnostics, CRT/J scalar diagnostics, and candidate metric
expressions do not establish a Schwarzschild derivation.

A later Schwarzschild result must at least provide:

1. a radial valuation and spherical-symmetry predicate;
2. a W4 mass-source receipt;
3. a Birkhoff or equivalent carrier theorem;
4. a weak-field Newtonian-potential diagnostic binding;
5. a standard metric-match theorem.

The current exact blocker for the advertised match is
`missingSchwarzschildMetricMatch`. Related live blockers include
`missingWeakFieldNewtonianPotential` and `missingW4MassSource`. Until those
receipts are inhabited, the paper must not claim a Birkhoff theorem,
Schwarzschild metric recovery, weak-field limit, or physical mass-source
calibration.

## Continuum recovery

Continuum GR recovery is also future work. A continuum theorem would require a
lattice or realization embedding, field convergence, metric and connection
error bounds, Einstein-tensor continuity, and a resolved W2 bridge or explicit
obstruction policy. The current blocker set includes `missingMetricErrorBound`,
`missingConnectionErrorBound`, `missingEinsteinTensorContinuity`, and
`missingW2BridgeOrObstructionResolution`.

Consequently, this paper may describe continuum recovery only as a theorem
shape. It must not claim a continuum limit, a convergence rate, or
realization-independent GR recovery from the current finite-radius diagnostics.

## W4 matter, stress-energy, and GRQFT

The W4 matter/stress-energy interface is the gateway from geometric diagnostics
to sourced physics. The current W4 path remains fail-closed behind external
authority and calibration gates: accepted DY/PDF convention authority, accepted
W4 adequacy, Candidate256 physical calibration, and the theorem-facing W4
matter/stress-energy receipt. The exact GR-facing blocker is
`missingW4MatterStressEnergyInterfaceReceipt`.

Without that interface, there is no constructed matter field, no constructed
stress-energy tensor, no sourced non-flat geometry, and no discrete Einstein
law coupled to W4. Local exploratory packets, preflight-compatible surfaces, or
public-source evidence cannot substitute for the missing receipt.

GRQFT closure is further downstream. A limited GRQFT claim would require a
discrete GR equation law, QFT interaction law, downstream consumer witnesses,
empirical GRQFT validation, and a closure-promotion receipt with the required
authority. None of those are supplied by the current GR request surfaces.
Therefore this paper must not claim limited SM+GR closure, GRQFT validation, or
full unification.

## Boundary rule for this paper

The admissible statement is:

> The current formalization isolates a typed future-work boundary from
> prime-indexed finite-difference commutation toward non-flat discrete GR. The
> required adapter, non-flat connection, curvature, contraction, sourced W4
> stress-energy, Schwarzschild, continuum, and GRQFT receipts remain open.

The inadmissible statements are:

- that the project has constructed non-flat GR;
- that the project has constructed a discrete Einstein tensor;
- that the project has proved a sourced Einstein equation;
- that W4 supplies a matter field or stress-energy tensor;
- that Schwarzschild or weak-field Newtonian recovery has been derived;
- that a continuum GR theorem or convergence rate has been proved;
- that GRQFT or limited SM+GR closure follows from the current diagnostics.

Any later manuscript revision may upgrade this section only after the exact
missing receipt or theorem named above is inhabited and bounded validation has
passed for the imported surface.

# Navier–Stokes Round 35 — strain Gram geometry, cutoff invariance and fail-closed shell gluing

Round 35 follows the Round-34 shortest cut. It uses the fibre/interference suggestions only where they can be attached immediately to literal repository mathematics. No terminal Clay wrapper is added and no still-open physical PDE estimate is promoted.

## 1. The exact strain multiplier is a half-isometry on each transverse fibre

Round 34 proved

```text
||S_k omega||_F^2 = (1/2) |omega|^2
```

for `k . omega = 0`. Round 35 polarizes that theorem instead of treating it merely as an L2 estimate.

For arbitrary mode fibres `k,l`, with

```text
a = k cross omega
b = l cross eta,
```

the exact Frobenius Gram kernel is

```text
<S_k omega, S_l eta>_F
  = (1/2) |k|^-2 |l|^-2
      [ (k.l)(a.b) + (k.b)(a.l) ].
```

On one transverse fibre this collapses to

```text
<S_k omega, S_k eta>_F = (1/2) (omega.eta),
```

so the radical-free partial-isometry statement is

```text
2 <S_k omega, S_k eta>_F = omega.eta.
```

`FourierStrainHalfIsometry` packages this exact inner-product preservation without introducing `sqrt 2` into the rational Fourier layer.

This strengthens A3/A4 materially. The same-fibre geometry is completely rigid; the only non-diagonal information left is cross-fibre interference.

## 2. Finite strain energy is diagonal half-energy plus cross-fibre interference

For a finite family of transverse modes Round 35 proves

```text
|| sum_k S_k omega_k ||_F^2
  = (1/2) sum_k |omega_k|^2
    + 2 sum_{k<l} <S_k omega_k, S_l omega_l>_F.
```

The proof is literal finite matrix algebra, using the new polarized Gram identity. Thus every departure from the exact diagonal half-energy is an explicit cross-fibre term.

This is the useful form for `HH-good`: same-fibre stretching has already depleted exactly. The remaining physical theorem must control the cross-fibre interference by the periodic principal-value kernel and directional/increment defect. `physicalCrossFibreInterferenceDecayConstructed` and `physicalHHGoodCrossFibreEstimateConstructed` remain false.

## 3. F1 is now a fixed-cutoff support invariance problem

The old generic reconstructed vector field mapped over the complete retained mode list. That list already contains both signs, while `ReconstructedPhysicalState` stores positive reality representatives and reconstructs the negative sheet. For proving invariance of the same representative carrier, mapping all retained modes as new positive representatives is too coarse.

Round 35 therefore constructs `fixedSupportPhysicalDerivative` by mapping the exact Round-30 viscous-plus-quadratic coefficient only over the state's existing positive representatives.

For every output coefficient the module proves:

```text
output mode = source representative mode;
output value = literalViscousQuadraticCoefficient at that mode;
output remains transverse and nonzero.
```

It then proves the complete reconstructed positive/negative support identity

```text
reconstructedStateModes (fixedSupportPhysicalDerivative datum)
  = reconstructedStateModes state,
```

and hence, for one `CutoffSameObjectDatum`,

```text
reconstructedStateModes derivative
  = nonzeroCutoffModes cutoff.
```

So the literal Galerkin derivative is tangent to the **fixed-cutoff support fibre**. Zero-mode exclusion, transverse typing and the positive/negative mode support are invariant by construction.

The remaining F1 compatibility leaf is narrower: prove the literal Fourier reality law for the nonlinear coefficient strongly enough that Round-33 positive/negative overlap compatibility is invariant. That is not inferred from the support theorem, so `fixedCutoffSameObjectCompatibilityInvariantConstructed` stays false.

## 4. The coordinate seam now transports the vector field, not just points

Round 30 already had an exact finite physical-coordinate equivalence and the coordinatewise theorem `physicalFieldEncodedExactly`. Round 35 makes that theorem one face of `VectorFieldIndexedGluing`.

The forward commuting square is

```text
encode (V_phys state) variable
  = V_coord (encode state) variable.
```

No function extensionality is introduced. The reverse face is proved coordinatewise from the encode/decode round trip:

```text
encode (decode (V_coord (encode state))) variable
  = encode (V_phys state) variable.
```

Thus the finite dynamics themselves are transported across the seam.

This generic square is immediately inhabited by every existing Round-30 literal coordinate representation. The still-open F2/F3 producer is the corresponding **physical Fourier state <-> Bishop-real coordinate equivalence** and commuting square on the Round-34 complete-real semantics. `physicalBishopVectorFieldIndexedGluingConstructed` remains false.

## 5. The triad orbit is factored as permutation × reality

Round 34 already used twelve concrete permutation/reality actions. Round 35 separates them into

```text
PermutationAction6
RealityAction2
```

and proves that

```text
applyFactoredAction permutation reality triad
  = applyAction (flattenAction permutation reality) triad.
```

The existing canonical orbit relation is equivalent to the existence of one such factored witness. This is the precise `6 x 2` structure behind the canonical packet quotient.

No freeness is assumed. Degenerate triads may have stabilizers, so the module does **not** claim every orbit contains twelve distinct elements. This preserves the safe Round-34 quotient while exposing the group-action structure needed by the eventual three-leg energy theorem.

## 6. `Com` is reduced to a literal operator-realisation theorem

The Round-34 centered `(L6,L3)` calculation already supplies the scalar overlap candidate

```text
strong_d + weak_d <= (1/2) 2^-d.
```

Round 35 introduces an immediately inhabited Gram factorisation cell:

```text
pairProduct <= leftOuter * overlap * rightOuter,
leftOuter <= 1,
rightOuter <= 1.
```

For nonnegative factors it proves

```text
pairProduct <= overlap.
```

Therefore an overlap satisfying the half-dyadic envelope yields the same pair-product decay. The actual six-three coefficient is inserted as a concrete Gram candidate and proves

```text
pairProduct(candidate_d) <= (1/2) 2^-d.
```

`PhysicalComPairProductGramRealization` then states the exact missing operator step for both Cotlar products:

```text
T_q^* T_r
T_q T_r^*
```

must be realized by such contracted Gram cells with the same overlap envelope. From that realization the two physical pair decays are proved automatically.

The shell arithmetic and contraction algebra are therefore no longer the frontier. The remaining A1 theorem is **operator-realisation**: construct these Gram cells from the literal commutator operators and their adjoints. `physicalComPairProductGramRealizationConstructed` remains false.

## 7. HH-bad summability is now exact finite shell gluing

Round 34 proved the unique target profile

```text
g_q(eta) = (eta/2) 2^-q
```

and its finite prefix. Round 35 records the cutoff decomposition as two literal resources:

```text
internalBudget_Q = sum_{q=0}^Q g_q(eta)
boundaryBudget_Q = eta 2^(-(Q+1)).
```

The gluing law is exactly

```text
internal budget plus boundary budget = eta.
```

Advancing the cutoff proves simultaneously:

```text
new internal - old internal = next shell gain;
new boundary = (1/2) old boundary;
new total = old total.
```

`ShellBudgetTransferStep` is therefore a proof-carrying finite cutoff transition. This is the form needed later by L1: the unresolved seam is explicit and decays geometrically while the total owner allocation is invariant.

The physical production of this shell profile remains open.

## 8. The HH-bad gain is already typed as a dissipation subsection

The Round-35 review found that the proposed

```text
G_q <= D_q
```

subsection design should **not** be duplicated: Round 34 already has exactly

```text
HHBadGainBelowCriticalDissipation cell
```

with a nonnegative physical gain and a proof that it lies below the localized dissipation in the same shell cell. `PhysicalLuoHHBadBridge` then combines that subsection with the scale-weighted dissipation smallness and proves absorption.

Accordingly Round 35 preserves that existing single-fibre interface. The hard analytic producer remains

```text
lambda_q D_q <= (eta/2) nu
```

on the actual trajectory, plus construction of the actual physical subsection witness. No duplicate receipt type is introduced.

## 9. Analytic resources and dyadic scale are separate fail-closed ledgers

Round 32 already tracks

```text
(dissipation, data, critical integral, forbidden).
```

Round 35 adds an independent `ScaleValuation` with

```text
shellGrowth
shellDecay
viscosityDegree.
```

Net shell degree is compared without signed-integer normalization by cross-adding growth and decay coordinates.

The actual HH-bad scale calculation becomes a checked identity:

```text
raw ratio lambda^(+1)
  * critical dissipation (nu lambda^(-1))
    ~ nu.
```

But a scale-free viscous gain produces an impossible equality and is refuted constructively:

```text
raw ratio lambda^(+1)
  * scale-free nu gain
    !~ nu.
```

`FailClosedAbsorption` therefore requires both a clean analytic resource valuation and a matching scale valuation. The missing inverse shell power cannot be hidden by otherwise acceptable eta bookkeeping.

## 10. Frontier after Round 35

Closed or materially narrowed:

```text
F1a fixed-cutoff support tangency of the literal derivative
F2a vector-field commuting-square formulation and reverse coordinate face
F4a canonical triad action factored as 6 permutations x 2 reality choices
A1a Gram contraction reduction for two-sided Com products
A1b actual six-three half-dyadic overlap candidate inserted
A3c exact cross-fibre strain Gram formula
A3d exact half-isometry/polarization on one transverse fibre
A4a finite diagonal + cross-interference strain decomposition
A6a finite HH-bad budget gluing with exact cutoff transfer
A6/A7 existing same-shell dissipation subsection interface preserved
scale/resource dual fail-closed absorption ledger
```

Still physical/open:

```text
F1b literal nonlinear Fourier reality law preserving same-object compatibility
F2b physical Fourier state <-> Bishop-real coordinates
F2c Bishop-real physicalFieldEncodedExactly
F3  Bishop-real finite Picard-Lindelof / contraction theorem
F4b literal complex three-leg Galerkin energy transfer on the factored orbit
F5-F6 real finite energy integration and global finite flow
S1  literal trajectory shell authority

A1  construct literal T_q^*T_r and T_qT_r^* Gram realizations
A2  physical Com owner estimate
A3  periodic principal-value strain kernel + increment theorem
A4  physical cross-fibre HH-good estimate
A5  physical directional-defect evolution
A6  physical Luo-style localized dissipation smallness
A7  actual physical gain-subsection witness
A8  physical HH-bad owner estimate
A9-A14 remaining owners

C1-C3 actual nine-owner family with strict total eta < 1
L1-L6 cutoff limits, compactness, continuation and final witness
```

The highest-alpha next experiments are now unusually concrete: prove the literal commutator operator Gram realization, prove the periodic real-space kernel/increment identity that controls the explicit strain interference sum, and prove the localized high-frequency dissipation smallness which feeds the already-typed HH-bad subsection.

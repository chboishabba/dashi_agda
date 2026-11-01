# Navier–Stokes Round 35 — strain Gram geometry, same-object cutoff invariance and fail-closed shell gluing

Round 35 implements the fibre/interference continuation on top of Round 34 only where it produces literal Navier–Stokes mathematics. It does **not** add a terminal Clay wrapper and it does not promote any still-open physical PDE estimate.

## 1. The Fourier strain map is an exact half-isometry on each transverse fibre

Round 34 proved

```text
||S_k omega||_F^2 = (1/2) |omega|^2
```

for `k . omega = 0`. Round 35 polarizes that identity. For arbitrary mode fibres `k,l`, with

```text
a = k cross omega
b = l cross eta,
```

it proves the exact Gram formula

```text
<S_k omega,S_l eta>_F
 = (1/2)|k|^-2|l|^-2
   [ (k.l)(a.b) + (k.b)(a.l) ].
```

On one transverse fibre this becomes

```text
<S_k omega,S_k eta>_F = (1/2)(omega.eta),
2 <S_k omega,S_k eta>_F = omega.eta.
```

`FourierStrainHalfIsometry` packages the radical-free partial-isometry statement; no square root is introduced into the exact rational Fourier layer.

## 2. Finite strain energy is diagonal half-energy plus cross-fibre interference

For any finite transverse family Round 35 proves

```text
||sum_k S_k omega_k||_F^2
 = (1/2) sum_k |omega_k|^2
   + 2 sum_{k<l}<S_k omega_k,S_l omega_l>_F.
```

Every departure from the exact diagonal half-energy is therefore explicit **cross-fibre interference**. Same-fibre geometry is already rigid and depleted. The physical `HH-good` producer is now specifically a bound on these cross terms from the periodic principal-value kernel and directional/increment defect. `physicalCrossFibreInterferenceDecayConstructed` and `physicalHHGoodCrossFibreEstimateConstructed` remain false.

## 3. F1: the complete strengthened same-object cutoff carrier is invariant under the literal Galerkin vector field

Round 34 constructed `CutoffSameObjectDatum`: one compatible reconstructed state, one literal cutoff, the inverse-square geometry, viscosity, and exact equality of reconstructed support with the nonzero cutoff cube.

Round 35 first constructs `fixedSupportPhysicalDerivative` by evaluating the literal viscous-plus-quadratic coefficient only on the state's existing positive reality representatives. It proves

```text
reconstructedStateModes derivative
  = reconstructedStateModes state
  = nonzeroCutoffModes cutoff.
```

Thus the RHS is tangent to the **fixed-cutoff support** fibre and preserves zero-mode exclusion and transversality by construction.

### 3.1 Inverse-square evenness is derived from the existing geometry

The nonlinear reality proof exposed a genuine hidden seam: `ModeInverseSquare` did not separately assume

```text
inverseNormSquared (-k) = inverseNormSquared k.
```

Round 35 derives it. The literal coordinate norm gives

```text
normSquared (-k) = normSquared k.
```

For nonzero `k`, the two inverse-square values are both right inverses of that same scalar; uniqueness of inverses in the exact commutative field therefore gives the inverse equality. The zero mode is definitional. **Inverse-square evenness** is now a theorem, not a new audit premise.

### 3.2 The Leray projector satisfies the exact reality laws

Using inverse-square evenness, the branch proves

```text
P_-k v = P_k v,
P_k(conjugate v) = conjugate(P_k v).
```

These theorems directly inhabit the repository's older `CorrectComplex3RealityLaws` interface.

### 3.3 The ordered nonlinear interaction satisfies exact Fourier reality

For the literal **ordered nonlinear interaction**

```text
N_{k,p,q}(u_p,u_q)
  = -i P_k [ (u_p dot q) u_q ],
```

Round 35 proves

```text
N_{-k,-p,-q}(conj u_p,conj u_q)
  = conj(N_{k,p,q}(u_p,u_q)).
```

The proof explicitly transports the sign of `q`, mode-evenness and conjugation of the Leray projector, and the outer `-i` factor. It specializes to the repository's literal `projectedOrderedTerm`.

### 3.4 Proof-bearing output fibres are reindexed without proof irrelevance

The physical triad enumeration is proof-bearing. Completeness returns a listed representative with the same `p/q/k` labels rather than asserting equality between incidence records containing potentially different resonance proofs. Round 35 respects that design.

It first constructs the **labelled output-fibre conjugation**: every fibre member at `k` has a listed representative at `-k` with labels `(-p,-q,-k)`, and conversely.

It then proves every physical incidence is equal to the canonical `pairTriad` determined by `p,q`, defines

```text
canonicalConjugate(p,q) = pairTriad(-p,-q),
```

and proves this map is injective and involutive. The repository's structural no-duplicate proof is transported to stdlib `Unique`; membership equivalence is upgraded by `Bag.∼bag⇒↭` to the actual list permutation

```text
map canonicalConjugate (physicalOutputFiber cutoff k)
  ↭ physicalOutputFiber cutoff (-k).
```

No proof-irrelevance axiom, arbitrary ordering, or function extensionality is used.

### 3.5 Summed projected-nonlinearity reality is now closed

The literal `Complex3` fold is proved permutation-invariant and conjugation is proved to commute with it. Combining those facts with the local term theorem and the output-fibre permutation yields

```text
projectedNonlinearity(-k)
  = conj(projectedNonlinearity(k)).
```

This is the full finite summed nonlinear Fourier-reality theorem, not merely a single-triad identity.

### 3.6 The viscous term and the complete RHS satisfy Fourier reality

The viscosity coefficient is real and `|k|^2` is even, so Round 35 proves

```text
literalViscousCoefficient(-k)
  = conj(literalViscousCoefficient(k)).
```

Together with the summed nonlinear theorem this gives Fourier reality of the entire literal viscous-plus-quadratic RHS.

### 3.7 The executable Round-33 velocity lookup has global Fourier reality

`literalVelocityAt` prioritizes a positive representative on positive/negative sheet overlap. Round 35 proves that the Round-33 compatibility laws are exactly sufficient for

```text
literalVelocityAt(-k) = conj(literalVelocityAt(k))
```

for **all** modes. The outside-support case is proved rather than assumed: if neither `k` nor `-k` occurs positively, both negative lookups are forced to zero.

### 3.8 Same-object compatibility of the derivative is now a theorem

For the positive representatives of `fixedSupportPhysicalDerivative`, Round 35 proves:

```text
equal output modes -> equal RHS values;
positive/negative sheet overlap -> conjugate RHS values.
```

The second implication uses the full RHS Fourier-reality theorem above. Consequently

```text
fixedSupportDerivativeCompatibleState
```

constructs `SameObjectCompatibleState` for the derivative, and

```text
derivativeCutoffSameObjectDatum
```

constructs a new `CutoffSameObjectDatum` with the **same cutoff, inverse-square geometry and viscosity**.

Therefore the full strengthened **same-object cutoff carrier** is invariant under the literal finite Galerkin vector field. F1 is no longer “construct a compatible derivative”; the remaining finite-flow work is F2/F3: coordinate this invariant finite vector field on a complete real carrier and integrate it.

## 4. The coordinate seam transports dynamics, not only points

Round 30 already had an exact finite physical-coordinate equivalence and `physicalFieldEncodedExactly`. Round 35 packages this as `VectorFieldIndexedGluing` with the forward commuting face

```text
encode(V_phys state) variable
  = V_coord(encode state) variable
```

and proves the reverse coordinate face from encode/decode exactness, without function extensionality.

This generic square is immediately inhabited by the existing Round-30 coordinate representation. The remaining F2/F3 producer is the corresponding physical Fourier state ↔ **Bishop-real** coordinate equivalence and commuting square on the complete-real semantics constructed in Round 34.

## 5. The canonical triad orbit factors as six permutations × reality

The twelve concrete Round-34 actions are factored into

```text
PermutationAction6
RealityAction2
```

and their product action is proved exactly equivalent to the existing `TriadAction`. The canonical orbit relation is equivalent to existence of one factored witness.

No free twelve-element orbit is assumed. Degenerate triads may have stabilizers.

## 6. `Com` is reduced to literal operator-realisation

The existing centered `(L6,L3)` calculation already proves

```text
strong_d + weak_d <= (1/2) 2^-d.
```

Round 35 defines a nonnegative `GramInterferenceCell` with

```text
pairProduct <= leftOuter * overlap * rightOuter,
leftOuter <= 1,
rightOuter <= 1,
```

and proves `pairProduct <= overlap`. The actual six-three coefficient is inserted as an immediately inhabited Gram candidate, so its candidate pair product obeys the half-dyadic envelope.

`PhysicalComPairProductGramRealization` states the exact remaining theorem for both Cotlar products `T_q^*T_r` and `T_qT_r^*`. Once the literal operators are realized by those cells, both pair decays follow automatically. Thus A1 is now an **operator-realisation** problem, not another geometric-series calculation.

## 7. HH-bad summability is exact finite shell gluing

The uniquely required profile is represented by

```text
internalBudget_Q = sum_{q=0}^Q g_q(eta)
boundaryBudget_Q = eta 2^(-(Q+1)).
```

with exact conservation

```text
internal budget plus boundary budget = eta.
```

A cutoff advance transfers exactly the next shell gain into the internal budget, halves the boundary seam, and preserves the total resource. `ShellBudgetTransferStep` is therefore the proof-carrying finite transition needed by the later shell-cutoff limit.

Physical production of the profile remains open.

## 8. The physical bad gain already lives inside one dissipation fibre

The suggested `G_q <= D_q` subsection type was not duplicated: Round 34 already has `HHBadGainBelowCriticalDissipation cell`, with a nonnegative gain and a proof that it lies below localized dissipation in the same shell cell. `PhysicalLuoHHBadBridge` combines that subsection with scale-weighted dissipation smallness.

The hard physical producer remains

```text
lambda_q D_q <= (eta/2) nu
```

on the actual trajectory, plus construction of the actual gain-subsection witness.

## 9. Analytic resources and dyadic scale are independent fail-closed ledgers

Round 32 already tracks

```text
(dissipation, data, critical integral, forbidden).
```

Round 35 adds `ScaleValuation(shellGrowth,shellDecay,viscosityDegree)`. Net shell degree is compared without signed normalization by cross-adding growth and decay coordinates.

The HH-bad calibration becomes a checked identity

```text
lambda^(+1) * (nu lambda^(-1)) ~ nu,
```

while a **scale-free** viscous gain is constructively refuted as a target-scale mismatch. `FailClosedAbsorption` therefore requires both admissible analytic resources and the correct scale valuation.

## 10. Frontier after Round 35

Closed or materially narrowed:

```text
F1  COMPLETE AS A FINITE VECTOR-FIELD INVARIANCE PRODUCER:
    fixed-cutoff support tangency
    inverse-square evenness
    Leray mode/conjugation reality
    ordered nonlinear reality
    labelled output-fibre conjugation
    exact output-fibre list permutation
    summed projected-nonlinearity reality
    viscous + whole RHS reality
    global canonical velocity reality
    derivative same-object compatibility
    derivativeCutoffSameObjectDatum at the same cutoff

F2a generic vector-field commuting square + reverse coordinate face
F4a canonical triad action factored as 6 permutations x 2 reality choices
A1a Gram contraction reduction for both Com pair products
A1b actual six-three half-dyadic overlap candidate
A3c exact cross-fibre strain Gram formula
A3d exact half-isometry/polarization on one transverse fibre
A4a finite diagonal + cross-interference strain decomposition
A6a finite HH-bad shell-budget gluing with exact cutoff transfer
A6/A7 same-shell dissipation subsection interface preserved
resource/scale dual fail-closed absorption ledger
```

Still open at the narrowest current interfaces:

```text
F2b physical finite Fourier cutoff carrier <-> Bishop-real coordinates
F2c Bishop-real physicalFieldEncodedExactly / commuting square
F3  finite Bishop-real Picard-Lindelof / contraction theorem
F4b literal complex three-leg Galerkin energy transfer on the factored orbit
F5  real integrated finite energy identity
F6  literal global finite flow
S1  literal trajectory shell authority

A1  literal T_q^*T_r and T_qT_r^* Gram realizations
A2  physical Com owner estimate
A3  periodic principal-value strain kernel + increment theorem
A4  physical cross-fibre HH-good estimate
A5  physical directional-defect evolution
A6  physical Luo-style localized high-frequency dissipation smallness
A7  actual physical gain-subsection witness
A8  physical HH-bad owner estimate
A9-A14 remaining physical owners

C1-C3 one physical nine-owner family with strict total eta < 1
L1-L6 cutoff limits, compactness, Serrin continuation and final witness
```

The highest-alpha physical work remains unchanged in character but is sharper in form: construct the literal Com operator Gram realization, prove the periodic principal-value kernel/increment theorem that controls the explicit strain interference sum, and prove the localized dissipation smallness that feeds the existing HH-bad subsection. The finite same-object carrier itself is now invariant; the finite-flow lane should move directly to Bishop-real coordinates and Picard–Lindelöf rather than reopen support/reality bookkeeping.

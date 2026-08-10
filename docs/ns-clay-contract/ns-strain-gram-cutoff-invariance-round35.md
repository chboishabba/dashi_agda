# Navier–Stokes Round 35 — strain Gram geometry, cutoff invariance and fail-closed shell gluing

Round 35 follows the Round-34 shortest cut. It uses the fibre/interference suggestions only where they attach immediately to literal repository mathematics. No terminal Clay wrapper is added and no still-open physical PDE estimate is promoted.

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
2 <S_k omega, S_k eta>_F = omega.eta.
```

`FourierStrainHalfIsometry` packages this exact inner-product preservation without introducing `sqrt 2` into the rational Fourier layer. This is the radical-free partial-isometry statement implicit in Round 34.

## 2. Finite strain energy is diagonal half-energy plus cross-fibre interference

For a finite family of transverse modes Round 35 proves

```text
|| sum_k S_k omega_k ||_F^2
  = (1/2) sum_k |omega_k|^2
    + 2 sum_{k<l} <S_k omega_k, S_l omega_l>_F.
```

The proof is literal finite matrix algebra. Every departure from the exact diagonal half-energy is therefore an explicit cross-fibre interference term. Same-fibre geometry has already depleted exactly; the remaining physical `HH-good` theorem must control those cross terms by the periodic principal-value kernel and directional/increment defect. `physicalCrossFibreInterferenceDecayConstructed` and `physicalHHGoodCrossFibreEstimateConstructed` remain false.

## 3. F1 is a fixed-cutoff support invariance theorem, and most local reality algebra is now closed

The generic Round-30 reconstructed vector field mapped over the complete retained mode list, while `ReconstructedPhysicalState` stores positive reality representatives and reconstructs the negative sheet. Round 35 instead constructs `fixedSupportPhysicalDerivative` by mapping the exact Round-30 viscous-plus-quadratic coefficient over the state's existing positive representatives.

For each output representative it proves

```text
output mode = source representative mode;
output value = literalViscousQuadraticCoefficient at that mode;
output remains transverse and nonzero.
```

and then

```text
reconstructedStateModes derivative
  = reconstructedStateModes state
  = nonzeroCutoffModes cutoff.
```

So the literal Galerkin derivative is tangent to the fixed-cutoff support fibre.

### 3.1 Inverse-square evenness is derived, not assumed

Trying to prove the nonlinear Fourier reality law exposed a hidden geometric seam: `ModeInverseSquare` did not contain a separate field for

```text
inverseNormSquared (-k) = inverseNormSquared k.
```

Round 35 proves that law from the fields already present. The literal norm formula gives

```text
normSquared (-k) = normSquared k.
```

For nonzero `k`, both stored inverse-square values are right inverses of that same scalar, and uniqueness of inverses in the exact commutative field gives

```text
inverseNormSquared (-k) = inverseNormSquared k.
```

The zero-mode branch is definitional. Thus **inverse-square evenness** is a theorem of the existing Fourier geometry, not a new audit premise.

### 3.2 The exact Leray reality laws are now producers

Using inverse-square evenness, Round 35 proves

```text
P_{-k} v = P_k v,
P_k (conjugate v) = conjugate (P_k v).
```

These inhabit the repository's older `CorrectComplex3RealityLaws` record directly. The projection reality seam is therefore closed without importing an analytic estimate.

### 3.3 The ordered nonlinear interaction satisfies exact Fourier reality

For the literal ordered Galerkin interaction

```text
N_{k,p,q}(u_p,u_q)
  = -i P_k [ (u_p dot q) u_q ],
```

Round 35 proves the genuinely nonlinear local identity

```text
N_{-k,-p,-q}(conjugate u_p, conjugate u_q)
  = conjugate (N_{k,p,q}(u_p,u_q)).
```

The proof accounts explicitly for the sign of `q`, the evenness of the Leray projector, conjugation of the projector, and the outer `-i`. It then specializes this to the repository's actual `projectedOrderedTerm` on a conjugated physical triad.

So the **ordered nonlinear interaction** reality theorem is closed. What remains is not local Fourier algebra.

### 3.4 Conjugation bijects the literal output fibres at the mode-label level

The physical triad enumerator is intentionally proof-bearing: completeness returns a listed representative with the same `p/q/k` labels rather than claiming propositional equality between records carrying potentially different resonance proofs. Round 35 preserves that distinction.

For every member of the output fibre at `k`, it constructs a listed representative in the output fibre at `-k` with labels exactly

```text
(-p,-q,-k).
```

The reverse construction is obtained by conjugating again. This **labelled output-fibre conjugation** is exactly the carrier bijection required by the local nonlinear reality theorem, because `projectedOrderedTerm` depends on the `p/q/k` labels and the corresponding velocity values.

The final finite combinatorial leaf is to package that labelled bijection as the permutation/reindexing used by the vector sum. `outputFiberConjugationListPermutationConstructed` and `summedProjectedNonlinearityRealityConstructed` remain false. F1 has therefore narrowed from “prove nonlinear reality” to a finite-list permutation theorem followed by the already-proved local conjugation identity.

## 4. The coordinate seam transports the vector field, not just points

Round 30 already had an exact finite physical-coordinate equivalence and the coordinatewise theorem `physicalFieldEncodedExactly`. Round 35 makes that theorem one face of `VectorFieldIndexedGluing`:

```text
encode (V_phys state) variable
  = V_coord (encode state) variable.
```

No function extensionality is introduced. The reverse face follows coordinatewise from encode/decode round-trip exactness:

```text
encode (decode (V_coord (encode state))) variable
  = encode (V_phys state) variable.
```

The existing Round-30 representation immediately inhabits this square. The live F2/F3 producer is the analogous physical Fourier state ↔ Bishop-real coordinate equivalence and commuting square on the Round-34 complete-real semantics.

## 5. The canonical triad orbit is factored as six permutations × reality

Round 34 already used twelve concrete permutation/reality actions. Round 35 separates them into

```text
PermutationAction6
RealityAction2
```

and proves that their product action is exactly the repository's concrete `TriadAction`. The existing canonical orbit relation is equivalent to existence of one such factored witness.

No freeness is assumed. Degenerate triads may have stabilizers, so Round 35 does not claim that every orbit contains twelve distinct elements.

## 6. `Com` is reduced to a literal operator-realisation theorem

The Round-34 centered `(L6,L3)` calculation already supplies

```text
strong_d + weak_d <= (1/2) 2^-d.
```

Round 35 introduces `GramInterferenceCell`:

```text
pairProduct <= leftOuter * overlap * rightOuter,
0 <= leftOuter <= 1,
0 <= rightOuter <= 1.
```

For nonnegative factors it proves

```text
pairProduct <= overlap.
```

The existing six-three coefficient is then inserted as an actual Gram candidate, yielding

```text
pairProduct(candidate_d) <= (1/2) 2^-d.
```

`PhysicalComPairProductGramRealization` states the exact remaining operator step for both Cotlar products `T_q^*T_r` and `T_qT_r^*`. Once that operator-realisation is constructed, both half-dyadic pair decays follow automatically. The shell arithmetic and contraction algebra are no longer the frontier.

## 7. HH-bad summability is exact finite shell gluing

Round 35 records the unique Round-34 target profile as

```text
internalBudget_Q = sum_{q=0}^Q g_q(eta)
boundaryBudget_Q = eta 2^(-(Q+1)).
```

with the exact gluing law

```text
internal budget plus boundary budget = eta.
```

Advancing the cutoff proves simultaneously

```text
new internal - old internal = next shell gain;
new boundary = (1/2) old boundary;
new total = old total.
```

`ShellBudgetTransferStep` is therefore a proof-carrying finite cutoff transition suitable for the later L1 limit. Physical production of the profile remains open.

## 8. The HH-bad gain was already typed as a dissipation subsection

The proposed new `G_q <= D_q` subsection type was not duplicated. Round 34 already has exactly

```text
HHBadGainBelowCriticalDissipation cell
```

with nonnegative physical gain and a proof that it lies below localized dissipation on the same shell. `PhysicalLuoHHBadBridge` combines that subsection with scale-weighted dissipation smallness and proves absorption.

The hard analytic producer therefore remains

```text
lambda_q D_q <= (eta/2) nu
```

on the actual trajectory, plus construction of the actual physical subsection witness.

## 9. Analytic resources and dyadic scale are separate fail-closed ledgers

Round 32 already tracks the analytic resource vector

```text
(dissipation, data, critical integral, forbidden).
```

Round 35 adds an independent `ScaleValuation` with shell growth, shell decay and viscosity degree. Net shell degree is compared by cross-adding growth and decay coordinates.

The HH-bad scale calculation is then checked as

```text
lambda^(+1) * (nu lambda^(-1)) ~ nu,
```

while a **scale-free** viscous gain cannot match the target and is constructively refuted. `FailClosedAbsorption` consequently requires both admissible analytic resources and matching scale valuation.

## 10. Frontier after Round 35

Closed or materially narrowed in this tranche:

```text
F1a fixed-cutoff support tangency of the literal derivative
F1b norm/inverse-square evenness under k -> -k
F1c P_-k = P_k
F1d P_k(conj v) = conj(P_k v)
F1e exact ordered nonlinear triad reality
F1f labelled conjugation bijection between output fibres k and -k
F2a vector-field commuting-square formulation + reverse coordinate face
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

Still open, stated at the narrowest current interfaces:

```text
F1g labelled output-fibre bijection -> finite list permutation
F1h summed projectedNonlinearity(-k) = conj(projectedNonlinearity(k))
F1i viscous-term reality + whole derivative same-object compatibility
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

The highest-alpha analytic experiments remain the literal commutator operator Gram realization, the periodic real-space kernel/increment theorem controlling the now-explicit strain interference sum, and the localized high-frequency dissipation smallness feeding the existing HH-bad subsection. On the finite-flow side, the only remaining nonlinear reality content is now finite reindexing rather than local PDE algebra.

# Gate 2-A Near-Extremizer Transport Target

## Status

Gate 2-A is not an exact identity theorem and not a global worst-case
operator domination theorem.

The audits show:

- exact restriction identity: false
- Schur linearity: false
- coarse transport route: fails
- extremizer-aware transport: stable and subcritical on N = 6, 8, 10

Observed directional ratios:

| N | ρ_N | coarse upper | θ_N | improvement |
|---:|---:|---:|---:|---:|
| 6 | 0.60816 | 17.7656 | 0.1681546 | 105.65× |
| 8 | 0.61283 | 17.7399 | 0.1677930 | 105.72× |
| 10 | 0.61508 | 20.4922 | 0.1678154 | 122.11× |

Thus the live target is an extremizer-aware transport theorem.

The current proof split is:

- Lemma A, additive defect ledger: abstractly proved.
- Lemma B, cone-width defect scaling: abstract model proved, NS-seam realization open.
- Lemma C, quarter-margin ledger: abstract model proved, NS-seam realization open.
- EP3 directional budgeting: partially installed.
- EP4 margin closure: still open.

## Near-extremizer cone

Let

```
ρ_N = sup_{x⟂1_C} (x^T L_bad,N x) / (x^T L_good,N x).
```

For ε > 0, define the Gate 1 near-extremizer cone:

```
𝒮_N(ε) = { x ∈ 1_C^⊥ : (x^T L_bad,N x) / (x^T L_good,N x) ≥ ρ_N − ε }.
```

These are the directions that matter for the Gate 1 bad/good domination problem.

## Transport map

Let J_N denote the Schur/Gram comparison lift from the seam carrier
1_C^⊥ into the normalized Gram/leakage carrier.

Gate 2-A does not require J_N to preserve all directions sharply.
It only requires sharp control on 𝒮_N(ε).

## Target theorem

There exist constants ε_* > 0 and θ_* < 1, independent of N, such that

```
sup_{x∈𝒮_N(ε_*)} ⟨J_N x, L_neg,N J_N x⟩ / ⟨J_N x, L_abs,N J_N x⟩ ≤ θ_*.
```

A conservative analytic target is θ_* ≤ 1/4.

The observed numerical value is θ_N ≈ 0.168 ≈ 1/6.

## Proof obligations

**EP1. Extremizer classification**
Show that Gate 1 near-extremizers belong to a controlled anisotropic seam
family.  Depends on O(4) representation theory (cf. 2602.0087 Thm 3.6).
Dedicated theorem surface:
`DASHI/Physics/Closure/NSTriadKNGate2AEP1ExtremizerClassification.agda`.

Structural properties recorded:
- Non-axis character (~86% 0-zero coordinate-permutation mass at N=12)
- Top-shell concentration (mass in shells N-1 and N)
- Persistent orbit family (0,1,N-1) across N=6,8,10,12,14,16
- Mixed-shell seam is the locally hardest direction
- O(4) anisotropic quotient is 1-dimensional (2602.0087 Thm 3.6, imported)

Status: `ep1ClaimStated = true`, `ep1NumericallySupported = true`,
`ep1O4ClassificationImported = true`, `ep1ProofConstructed = false`,
`ep1Promoted = false`.

**EP2. Cone stability**
Show that the near-extremizer family 𝒮_N(ε) is stable under the admissible
seam symmetries and under the Schur comparison lift.

**EP3. Directional Schur transport**
Prove that J_N transports vectors in 𝒮_N(ε) with leakage ratio bounded
by θ_* < 1. The live version of this step is quotient-aware:

`J_neg = J_abs + ΔJ`

with separate principal, cross-defect, and pure-defect budgeting on the
near-extremizer cone.

**EP4. Margin closure**
Show that the transported margin combines with the Gate 1 domination margin
without crossing 1, and that outside-seam pollution is absorbed rather than
reintroducing an uncontrolled bad term.

Current sharp split:

- concrete seam-local closure model: installed
- seam-local margin proof: carried
- outside-seam zero/absorption lemma on the seam carrier: proved

The EP4 local chain is now closed:

- `crossEstimateProved = true`
- `pureEstimateProved = true`
- `combinedEstimateProved = true`
- `crossDefectLinearInConeWidthProved = true`
- `pureDefectQuadraticInConeWidthProved = true`
- `quarterMarginCompatibilityProved = true`
- `combinedDefectBudgetProved = true`
- `quotientAwareTransportProved = true`
- `ep4DirectionalMarginUniformlyClosed = true`
- `ep4OutsideSeamPollutionAbsorbed = true`
- `ep4ProofConstructed = true`

## Receipt boundary

Observed:

```agda
gate2aExtremizerAwareTransportObservedShells = [6 , 8 , 10]
gate2aDirectionalRatioStableObserved = true
gate2aDirectionalRatioApproxOneSixthObserved = true
gate2aTransportMarginPositiveObserved = true
gate2aCoarseTransportClosesObserved = false
```

Conditional surface installed:

```agda
gate2aExtremizerAwareTransportTheoremStated = true
gate2aExtremizerAwareTransportProofPlanInstalled = true
gate2aExtremizerAwareTransportNumericallySupported = true
gate2aExtremizerAwareTransportConditional = true
gate2aConcreteSeamLocalClosureModel = true
gate2aSeamLocalMarginProofCarried = true
gate2aSeamLocalExtremizerAwareTransportModelClosed = true
gate2aSeamLocalConditionalLemmaCarried = true
gate2aExtremizerAwareTransportProved = false
gate2aConditionalLemmaProved = false
```

## Implementation Order

The implemented closure path was:

1. Install concrete near-extremizer cross/pure/combined defect bounds.
2. Realize cone-width scaling on the same seam carrier.
3. Realize the quarter-margin ledger in twelfths with `2 + 1 = 3`.
4. Consume those bounds into the combined defect budget.
5. Close the quotient-aware transport theorem.
6. Close EP4 by taking outside-seam pollution to be exactly `0#` on the seam carrier.

## Interpretation

Gate 2-A is a near-extremizer transport theorem surface.

The Schur comparison is too lossy on arbitrary directions, but the
Gate 1 extremizer direction is transported with a stable subcritical
ratio near 1/6.  Therefore the proof should track the extremizer cone,
not a global operator norm.

Gate 2-A is locally closed only as a seam-local model on the shared budget
carrier. The remaining nonlocal work is the exact `K_N(A)` operator transfer
and the analytic outside-seam absorption theorem.

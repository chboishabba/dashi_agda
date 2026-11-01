# Yang–Mills Round 36 — finite atom closure and admissible variation selector

## Status

Round 36 takes the shortest proof-bearing continuation from Round 35. It closes the literal finite pair and deep channels under the selected-background radius and turns the remaining Euler–Lagrange instruction into an exact local variation-selector interface.

It does **not** claim that the selected plaquette variation has already been constructed. The remaining open theorem is now the actual gauge-admissible, constraint-tangent selector and its sharp spillover estimate.

A static audit is not an Agda-kernel result. Kernel acceptance is claimed only after the focused workflow succeeds.

## 1. Exact atom ownership

Every nonempty subset in the ordered four-factor telescope has one owner:

```text
correlated:
  4 singleton + 6 pair = 10 atoms

deep:
  4 triple + 1 quartic = 5 atoms
```

The branch proves all fifteen constructors are accounted for and that no atom can have both owners. This prevents pair terms from leaking into the `rho/144` diagonal channel and prevents double payment.

## 2. Literal selected-factor envelopes

For either a positive or inverse physical link jet, each selected factor is treated at its actual slot and placement. If `w` is the identity-factor norm weight, the branch proves

```text
N(B_selected) = w,
N(A_selected - B_selected) <= epsilon^2 w,
epsilon = 2 rho.
```

The link-defect input is the same selected-background radius already derived in Round 34. The four slot envelopes are assembled into the existing generic `FourFactorDeepEnvelope` for every one of the sixteen named placements. The weight product is proved equal to that placement's literal left/right Young charge.

This supersedes the loose unit/insertion application that could not type against the repository's physical `positiveLinkJet` and `inverseLinkJet` signatures: Round 36 works through the actual plaquette slots, background, field, site and axes.

## 3. Six-pair lower theorem

The generic pair theorem proves, for one placement,

```text
-6 epsilon^2 * (leftCharge + rightCharge)/2
  <= WilsonScalar(pair01 + pair02 + pair03 + pair12 + pair13 + pair23).
```

All six ordered subset products are retained explicitly; no symmetry orbit is assumed.

Summing the sixteen placement budgets gives

```text
4 q_p(h).
```

Hence the local pair channel costs

```text
24 epsilon^2 q_p(h).
```

Using `C_p(h)=3 q_p(h)` and `epsilon=2 rho`, exact rational arithmetic gives

```text
24 epsilon^2 q_p(h)
  = (rho/256) C_p(h).
```

Therefore

```text
P_p(A,h) >= -(rho/256) C_p(h).
```

## 4. Cubic–quartic physical lower theorem

The physical envelope instantiates Round 35's generic deep theorem on all sixteen placements. It yields

```text
D_p(A,h)
  >= -(16 epsilon^3 + 4 epsilon^4) q_p(h).
```

The existing coefficient theorem proves

```text
16 epsilon^3 + 4 epsilon^4
  = 16385/70368744177664
  < rho/144,
```

with exact slack

```text
536723447/633318697598976.
```

Thus

```text
D_p(A,h) >= -(rho/144) q_p(h).
```

The finite nonlinear channel is therefore closed from the same physical radius as the terminal selected-background theorem.

## 5. Local admissible variation selector

The remaining singleton theorem is represented by

```text
SingletonExtractionWitness A h p
```

which owns:

```text
FineVariation
variation
GaugeAdmissible variation
ConstraintTangent variation
SupportedNearPlaquette variation
variationNormSq variation <= K_selector C_p(h)
firstVariation variation = 0
firstVariation variation = S_p(A,h) + extractionSpillover
extractionSpillover <= 55/18874368 C_p(h).
```

The equality `firstVariation variation = 0` is the selected Euler–Lagrange stationarity clause. The second equality requires the same variation to extract the literal four-singleton Wilson sum, not an independently supplied curvature scalar.

The reducer proves

```text
S_p(A,h) >= -55/18874368 C_p(h).
```

Combining this with the exact pair theorem gives

```text
S_p(A,h) + P_p(A,h)
  >= -(rho/36) C_p(h),
```

because

```text
55/18874368 + rho/256 = rho/36.
```

Together with the closed deep theorem, an actual selector constructs the repository's literal physical W-local witness.

## 6. Direct terminal composition

For the exact `SelectedVariationalPerturbationFamily`, the physical radius is not accepted independently: it is recovered from

```text
selectedVariationalRadiusAt family h.
```

Therefore an actual selector on that same background and field directly produces

```text
H_A[h,h]
  >= 10739/196608 ||h||^2
  >= 1/32 ||h||^2.
```

No separate radius, W-local or terminal-Hessian receipt is required.

## Exact remaining Gate-I frontier

Round 36 closes:

```text
WilsonAtomOwnerExact
physicalSelectedFactorEnvelopeInstantiation
physicalPairWilsonLower
physicalDeepWilsonRemainderLower
singletonSelectorReducer
selectorToPhysicalWLocal
selectorToOneThirtySecondHessian
```

The remaining proof-bearing sequence is:

```text
selectedPlaquetteVariationFrame
selectedPlaquetteVariationSelector
selectedPlaquetteVariationGaugeAdmissible
selectedPlaquetteVariationConstraintTangent
selectedPlaquetteVariationLocal
selectedPlaquetteVariationChargeBound
selectedPlaquetteFirstVariationExtractsSingleton
selectedPlaquetteExtractionSpilloverUpper
```

The last coefficient must fit

```text
55/18874368.
```

This is the only remaining Gate-I analytic producer. Radius-only or flat-cancellation arguments cannot supply it; Round 35 contains an exact rational stress witness demonstrating that failure mode.

## Validation

```bash
AGDA_JOBS=1 bash scripts/check_yang_mills_clay_highest_alpha_round36.sh
```

The checker cascades through Round 35, rejects holes, postulates, unsafe escapes, trust primitives and imported theorem receipts, checks the exact ownership, envelope, pair/deep coefficients and selector boundaries, then invokes the pinned Agda 2.9 cumulative root.

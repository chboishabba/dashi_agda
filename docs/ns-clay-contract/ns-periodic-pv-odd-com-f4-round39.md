# NS Round 39 — periodic PV split, odd-Com round trips, F4 closure, and exact reserve no-go

Round 39 implements the concrete next-step analysis from the post-Round-38 highest-alpha cut. The rule for this tranche is physical producer first: preserve the exact cancellations already found, narrow each remaining analytic theorem, and refuse to spend viscosity reserve on algebraically or geometrically removable terms.

No unconditional Navier–Stokes regularity theorem is claimed. The genuinely periodic HH-good estimate, physical HH-bad gain density/Luo smallness, and physical Com Gram realization remain explicit open producers.

## 1. Periodic HH-good is split into singular near and smooth global pieces

The periodic character carrier is now closed under an exact near/smooth kernel split on the *same* torus, integral and characters. From a pointwise identity

```text
K = K_near + K_smooth
```

Round 39 proves

```text
Khat = Khat_near + Khat_smooth,
mass K = mass K_near + mass K_smooth,
Delta_K = Delta_near + Delta_smooth.
```

This is the algebra needed by the physical torus decomposition

```text
K_T3 = chi K_R3^hom + R_T3.
```

The future analytic proof can therefore estimate the local singular piece using directional depletion while sending the smooth periodic correction only to admissible data/critical remainders.

`PeriodicPVHHGoodNearSmoothEstimate` makes this distinction part of the owner theorem. It accepts

```text
Near <= eta D + A_near + B_near X,
Smooth <= A_smooth + B_smooth X
```

and proves

```text
Near + Smooth
  <= eta D
   + (A_near + A_smooth)
   + (B_near + B_smooth) X.
```

It then constructs the literal `HH-good` `AdmissibleOwnerEstimate`. The smooth correction cannot silently consume extra viscosity reserve.

Sources: Constantin–Fefferman, DOI `10.1512/iumj.1993.42.42034`; Bahouri–Chemin–Danchin, DOI `10.1007/978-3-642-16830-7`.

## 2. The vorticity-line residual survives shell/PV decomposition exactly

Round 38 identified the division-free HH-good residual

```text
delta_v(w) = w cross v.
```

Round 39 proves its exact linear transport laws

```text
delta_v(w1 + w2) = delta_v(w1) + delta_v(w2),
delta_v(a w) = a delta_v(w),
```

and therefore for every finite weighted shell/kernel sum

```text
delta_v(sum_i a_i w_i)
  = sum_i a_i delta_v(w_i).
```

Parallel perturbations remain invisible after weighting. This formally enforces the useful implementation rule: **do not replace `|w cross v|` by `|w||v|` before shell decomposition and PV cancellation have finished.**

Sources: Constantin–Fefferman and Constantin–Fefferman–Majda, DOI `10.1080/03605309608821197`.

## 3. HH-good threshold selection has an exact rational squared criterion

Round 38 proved

```text
|stretch|^2 <= delta a^2 b^4.
```

The natural unsquared owner scaling is `eta_HHg ~ C_PV sqrt(delta)`. Rather than add a square-root primitive to the rational owner layer, Round 39 proves the equivalent division-free sufficient condition

```text
C_PV^2 delta <= eta_HHg^2
```

and derives

```text
C_PV^2 |stretch|^2
  <= eta_HHg^2 a^2 b^4.
```

Thus once the physical PV constant is known, the good threshold can be solved against the reserve with exact rational arithmetic. The unsquared singular-integral absorption is still part of the real A3/A4 theorem.

## 4. HH-bad gain is a density over the same restricted viscous charge

The bad mask is never differentiated. A `RawBadGainSample` contains the same Round-38 bad-tagged energy sample and an actual nonnegative nonlinear gain. `maskedGain` is definitionally zero on good samples.

A `RestrictedGainDensityCell` proves, sample by sample,

```text
gain_i <= c * maskedViscousCharge_i.
```

Round 39 proves the finite Radon–Nikodym analogue

```text
sum gain_i <= c * sum maskedViscousCharge_i.
```

and the corresponding inverse-shell-target form. This cleanly separates occupation/dissipation from the already-existing crossing/BV coordinate and introduces no `d/dt chi_bad` term.

The open physical work is now very precise:

```text
physicalHHBadGainDensityCells
physicalLuoCriticalDissipationSmallness
```

followed by the physical owner estimate.

Source: Luo, DOI `10.1007/s00021-019-0411-z`, arXiv DOI `10.48550/arXiv.1803.05569`.

## 5. Com has nilpotent cross channels and diagonal round trips

Write

```text
U = PTQ,
V = QTP.
```

Round 39 proves on the exact two-channel carrier

```text
U^2 = 0,
V^2 = 0,
T_odd^2 = UV + VU.
```

The surviving second-order terms are therefore exactly the two round trips

```text
P -> Q -> P,
Q -> P -> Q,
```

and both have the scalar coefficient `b*c`. This sharpens the physical Gram target: Round-35 pair products should be realized as cross-fibre round-trip overlaps, not arbitrary full-space products.

The Round-37 involution `J` also proves

```text
J U J = V(JTJ),
J V J = U(JTJ).
```

If the literal physical transport is `J`-equivariant, the two cross-channel coefficients are equal and one physical channel theorem determines the other. `physicalComJEquivarianceConstructed` remains false until that property is proved for the actual shell operator.

Source: Kato–Ponce, DOI `10.1002/cpa.3160410704`.

## 6. The proposed F4 pointwise half-symmetry was tested and corrected

The repository convention matters. Its stored `orderedPair` coefficient is not

```text
1/2 (Ordered + Ordered o swap).
```

It is literally

```text
Pair = Ordered + Ordered o swap.
```

with **no hidden half**. Therefore at a swap-fixed incidence

```text
Pair = 2 Ordered,
```

so the naive pointwise statement `Pair = Ordered` is false in the actual carrier.

Round 39 defines the correct normalized quantity

```text
NormalizedPair = 1/2 Pair
```

and proves both

```text
NormalizedPair = Ordered
```

at swap-fixed incidences and globally

```text
1/2 sum Pair = sum Ordered
```

using the Round-38 exact swap permutation. This resolves the factor-two seam without a free-action assumption.

## 7. F4 is now closed on the actual projected Galerkin convection pairing

Round 39 goes further than normalization. The existing finite Galerkin system defines

```text
projectedNonlinearity(k)
```

as the literal vector sum over `physicalOutputFiber cutoff k`.

First, Hermitian pairing and real part are distributed through that actual sum. Output-fibre soundness then proves

```text
Re <u_k, projectedNonlinearity(k)>
  = sum_{tau in outputFiber(k)} OrderedPower(tau).
```

Second, all output fibres over the duplicate-free literal `Cube.cutoffModes N` are concatenated. Round 39 proves:

- every fibre member belongs to the physical triad enumeration;
- every physical triad appears in the fibre indexed by its output;
- different output fibres are disjoint;
- the concatenated fibre list has no duplicates;
- hence the concatenation is an exact K-free permutation of `physicalTriadEnumeration N`.

Therefore

```text
literalConvectionPairingEqualsOrderedIncidenceFold :
  sum_k Re <u_k, projectedNonlinearity(k)>
  = sum_tau OrderedPower(tau).
```

Combining with Round 38's ordered-incidence cancellation yields

```text
literalProjectedGalerkinConvectionEnergyZero :
  sum_k Re <u_k, projectedNonlinearity(k)> = 0
```

for the exact rational cutoff system under the existing reality and divergence-free hypotheses.

This flips the new Round-39 F4 marker

```text
literalConvectionPairingEqualsOrderedIncidenceFoldConstructed = true.
```

The older Round-38 false marker remains historical and fail-closed in that file; Round 39 supplies the theorem that supersedes it.

Sources: Leray, DOI `10.1007/BF02547354`; Temam, DOI `10.1090/chel/343`.

## 8. The reserve optimizer now has an exact dual no-go certificate

Round 37 had a certified primal minimizer. Round 39 adds the complementary exact rational failure witness.

A physical lower constraint has the form

```text
b_j <= a_j . eta.
```

A `DualConstraintCell` carries a nonnegative rational multiplier `lambda_j`. If a finite family satisfies

```text
sum_j lambda_j a_j = (1,...,1),
sum_j lambda_j b_j >= 1,
```

Round 39 proves for every primal point satisfying all physical constraints

```text
1 <= eta_1 + ... + eta_9.
```

So numerical search may discover dual coefficients, but Agda verifies a small exact rational Farkas certificate. A failed architecture can now return a mathematical no-go witness instead of “the optimizer found no slack.”

Source: Gyula Farkas, *Theorie der einfachen Ungleichungen* (1902), historical article with no assigned DOI.

## 9. The good/bad threshold is now an optimization variable

`ThresholdTaxProfile` treats the physically proved quantities

```text
eta_HHg(delta),
eta_HHb(delta),
eta_other(delta)
```

as functions of the admissible rational threshold. A `CertifiedThresholdMinimizer` proves one threshold has no larger total tax than any other admissible threshold.

Round 39 proves the exact go/no-go statement:

```text
minimum total >= 1
```

implies

```text
for every admissible delta, total(delta) >= 1.
```

Thus a bad reserve cannot be blamed on poor hand tuning after the physical threshold profile is known.

## 10. Cancellation order is now enforced before positive taxation

A `PreTaxCancellationDecomposition` records exact nonnegative savings from

```text
raw positive term
  -> exact algebraic cancellation
  -> geometric/spectral cancellation
  -> pre-tax positive remainder.
```

Round 39 proves

```text
preTaxPositive <= rawPositive.
```

If a typed physical signed-owner edge is then applied, it also proves

```text
finalTaxAfterAllCancellations <= rawPositive.
```

This formalizes the intended order

```text
raw nonlinear term
 -> exact triad cancellation
 -> geometric/Gram cancellation
 -> signed owner flow
 -> positive tax.
```

No cancellation saving is manufactured: the physical decomposition and physical owner edge remain explicit inputs.

## Revised highest-alpha frontier after Round 39

F4 is removed from the frontier cut. The remaining three decisive physical packages are now:

1. **A3/A4 — periodic PV HH-good:** prove the literal torus decomposition `K_T3 = chi K_hom + R`, realize the exact strain kernel/zero mode, preserve the residual through the physical shell/PV operator, prove the singular near estimate with uniform constants, and prove the smooth correction remainder bound. The new near/smooth owner reducer then yields `physicalHHGoodOwnerEstimate`.
2. **A6/A8 — physical restricted HH-bad gain:** construct actual gain-density cells on the real trajectory bad set, prove the density bound against restricted viscous charge, and prove Luo's separate upper critical-dissipation smallness. Crossing/BV remains separate and is used only if dynamic switching needs it.
3. **A1/A2 — physical Com round-trip Gram:** identify the literal odd shell transport with the two Round-35 cross-fibre Gram round trips and prove physical `J` equivariance if it is genuinely available. Then consume the already-proved half-dyadic Cotlar decay.

After those three owner producers land, instantiate the six lower-risk owners and immediately run both sides of the reserve test:

```text
success: exact primal eta with sum eta < 1;
failure: exact dual certificate forcing sum eta >= 1.
```

The threshold itself should be included in that physical optimization. Only a successful strict reserve should trigger the downstream `CanonicalAnalyticPhysicalLeaves`, maximal-time contradiction, continuum promotion, and submission audit.

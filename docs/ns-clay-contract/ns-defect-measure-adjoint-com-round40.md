# NS Round 40 — unified HH defect measure, annular PV localization, and one-channel Com

Round 40 implements the strongest concrete post-Round-39 hypotheses before any further continuation packaging. It reuses mature repository mathematics where it actually matches the physical object, and rejects attractive same-object identifications when they do not.

No unconditional Navier--Stokes regularity theorem is claimed. Physical shell/time owner rates and the final same-object odd-P/Q-to-Gram realization remain explicit fail-closed seams.

## 1. One energy-weighted directional defect controls both HH strata

For

```text
Theta(xi,eta) = 1 - (xi.eta)^2 = |xi cross eta|^2,
0 <= Theta <= 1,
```

the existing weighted Markov theorem is now instantiated on actual physical vorticity pairs. On bad cells,

```text
delta * E_bad <= sum_i E_i Theta_i.
```

The same quantity is exactly the energy-weighted squared cross residual. Thus

```text
Theta <= delta  -> HH-good stretching depletion,
Theta >= delta  -> HH-bad occupation controlled by E*Theta.
```

No derivative of the Boolean classifier is introduced.

The new physical cells also feed the existing normalized weighted-defect rarity transfer. A physical envelope

```text
weightedDefectMass_q <= delta_q rarity_q
```

now directly gives

```text
badMass_q <= rarity_q,
rarity_q -> 0  =>  badMass_q -> 0.
```

There is therefore no new abstract defect-evolution layer to build; the remaining producer is the physical normalized weighted-defect envelope itself.

The same cells connect to Round-39 restricted bad gain. Round 40 proves

```text
delta * Gain_bad
  <= density * nu * lambda_q^2 * sum_i E_i Theta_i.
```

Since `Theta <= 1`,

```text
sum_i E_i Theta_i <= sum_i E_i,
```

and exact inverse-threshold cancellation gives

```text
Gain_bad <= delta^-1 * density * D_bad.
```

Thus the hard HH-bad work has narrowed to the physical inverse-shell gain-density factor required by the existing Round-33 obstruction, plus Luo's separate upper critical-dissipation smallness.

Sources: Constantin--Fefferman, DOI `10.1512/iumj.1993.42.42034`; Grujic, DOI `10.1088/0951-7715/26/1/289`; Luo, DOI `10.1007/s00021-019-0411-z`.

## 2. Exact threshold optimization, including shell-dependent diagnostics

Represent the physical classifier threshold by a positive rational scale `r`:

```text
delta = r^2,
delta^-1 = r^-2.
```

If the physical HH taxes really take the complementary form

```text
f(r) = A r + B r^-2,
```

Round 40 proves a global rational minimum without calculus. Any positive rational `r` satisfying

```text
A r^3 = 2 B
```

obeys, for every positive rational `x`,

```text
f(r) <= f(x),
```

using

```text
2 x^2 (f(x)-f(r)) = A (x-r)^2 (2x+r) >= 0.
```

At the balanced point,

```text
B r^-2 = (1/2) A r,
f(r) = (3/2) A r.
```

If exact rational balance is unavailable, Round 39's generic certified optimizer remains the correct fallback.

The same theorem is lifted shellwise to `A_q,B_q,r_q`. A scale-independent threshold is recovered only if the physical certificates prove all selected `r_q` coincide.

## 3. HH-good enforces PV cancellation before scalarization

A fixed angle threshold does not regularize the unsmoothed `|x-y|^-3` strain kernel. Round 40 therefore makes the proof order exact:

```text
PV cancellation
 -> preserve w cross v residual
 -> shell localization
 -> directional threshold
 -> weighted Cauchy / viscous absorption.
```

For zero-mass finite kernel weights,

```text
sum_i w_i = 0
```

kills an arbitrary constant source before taking the line residual, and then

```text
delta_v(sum_i w_i(s_i+c))
  = sum_i w_i delta_v(s_i).
```

For nonnegative shell-localized kernel magnitudes `k_i` and good stretching scalars satisfying

```text
s_i^2 <= delta W_i,
```

exact weighted Cauchy gives

```text
(sum_i k_i s_i)^2
  <= delta (sum_i k_i)(sum_i k_i W_i).
```

## 4. The Fourier strain multiplier is now proved order zero

Round 38 had

```text
S_k = |k|^-2 S_ang(k).
```

Round 40 proves directly on the rational projection-mode carrier that for every positive rational scale `r`,

```text
S_ang(r k) = r^2 S_ang(k),
|r k|^-2 = r^-2 |k|^-2,
S_{r k}(omega) = S_k(omega).
```

The scaled projection mode is proved to satisfy the exact inverse-norm law. Thus degree-zero homogeneity is no longer an imported analytic assumption.

This audit also caught an important false shortcut. The repository's existing `PeriodizedDyadicKernelL1Theorem` describes Luo's **scalar radial low-pass kernel**. It is not literally the matrix-valued shell-localized strain kernel. Round 40 therefore does **not** identify them.

The remaining standard analytic theorem is stated honestly as an annular strain-kernel authority: smooth compact support away from zero, L1 integrability of the fixed Euclidean master kernel, and shell-uniform torus periodization. Once the literal strain-shell sample mass is identified with that kernel L1 norm,

```text
|good shell stretching|^2
  <= C_strain * delta * weightedLocalMass
```

follows from the already-proved finite Cauchy theorem.

Sources: Beale--Kato--Majda, DOI `10.1007/BF01240221`; Constantin--Fefferman, DOI `10.1512/iumj.1993.42.42034`; Bahouri--Chemin--Danchin, DOI `10.1007/978-3-642-16830-7`.

## 5. Physical incompressible transport is skew-adjoint entry by entry

For an actual physical Fourier transport entry with

```text
m + q = k,
c(k,q) = i (q . u_m),
```

reality and divergence freedom give

```text
u_-m = conjugate(u_m),
m.u_m = 0,
k.u_m = q.u_m.
```

Round 40 proves

```text
conjugate(c(q,k)) = -c(k,q).
```

The reverse resonance `-m+k=q` is proved on the exact integer lattice, and the theorem is promoted to the physical matrix-entry statement

```text
conjugate T(q,k) = -T(k,q).
```

The official hard projector is already self-adjoint. Therefore on the exact P/Q carrier,

```text
U = PTQ,
V = QTP = -U*,
[P,T] = U + U*,
[P,T]^* = [P,T],
[P,T]^2 = diag(UU*,U*U).
```

Round 40 also proves the grading audit invariant

```text
Gamma T_odd = -T_odd Gamma.
```

## 6. The Round-35 two-face Cotlar input reduces to one physical Gram cell

Round 35 asks for two physical pair-product Gram cells. Round 40 adds

```text
PhysicalComSingleChannelGramRealization
```

with one Gram cell, one exact product identification, one half-dyadic overlap estimate, and the adjoint-face equality. It constructs the existing mature

```text
PhysicalComPairProductGramRealization
```

via

```text
fullRound35GramRealizationFromSingleChannel
```

and both Round-35 pair decays follow automatically.

Thus A1/A2 no longer needs two independent analytic estimates. The remaining same-object theorem is the literal odd P/Q physical block = one Round-35 `GramInterferenceCell`, together with the adjoint-face equality supplied by the physical operator semantics.

Sources: Kato--Ponce, DOI `10.1002/cpa.3160410704`; Temam, DOI `10.1090/chel/343`; Cotlar--Stein historical conference source, no DOI assigned.

## 7. Farkas dual pressure is an exact sensitivity diagnostic

Round 39's dual no-go certificate satisfies

```text
combinedLower = sum_j lambda_j b_j.
```

Round 40 exposes each exact contribution

```text
pressure_j = lambda_j b_j
```

and proves exact head-removal/improvement laws. This is not claimed to be a derivative of the optimum; it is a rigorous decomposition of the current rational obstruction and can guide proof effort before all nine owner constants land.

## Revised shortest frontier after Round 40

F4 remains closed. The decisive physical packages are now:

1. **HH-good / A3-A4:** construct the standard smooth-annular periodized strain-kernel L1 theorem on the literal torus carrier; identify the physical shell samples with it; prove the time/dissipation absorption and smooth periodic correction. PV cancellation, residual preservation, order-zero homogeneity, and finite shell Cauchy are already exact.
2. **HH-bad / A6-A8:** prove the physical inverse-shell gain-density factor and Luo's separate upper critical-dissipation smallness. Bad occupation, weighted-defect rarity transfer, restricted dissipation, and exact `delta^-1` scaling are already same-object.
3. **Com / A1-A2:** identify the literal odd P/Q block with one Round-35 Gram cell. Physical transport skew-adjointness and the reduction from one Gram cell to the mature two-face Cotlar input are already exact.

Then instantiate the six lower-risk owners and run the threshold-aware exact primal/dual reserve test. A strict rational primal certificate `sum eta < 1` advances to the existing `CanonicalAnalyticPhysicalLeaves` route; an exact dual certificate forcing `sum eta >= 1` rejects the architecture before downstream continuation work.

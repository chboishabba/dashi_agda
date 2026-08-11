# NS/Luo filtered defect and bad-excursion route — Round 21

This round starts from the complete Round 20 NEMGRO audit and periodic Fourier-symbol branch. It integrates the exact mathematical content of Runlong Yu's 2026 filtered-vortex paper without promoting its conditional finite-scale result to an unconditional regularity theorem.

Primary source:

- Runlong Yu, *Filtered Vortex Stretching and Subgrid Defects for the Three-Dimensional Navier-Stokes Equations*, arXiv `2606.27560`, DOI `10.48550/arXiv.2606.27560`.

Related obstruction-calculus sources:

- Runlong Yu, *A Structural Audit of Navier-Stokes Obstruction Calculus*, arXiv `2606.25341`, DOI `10.48550/arXiv.2606.25341`;
- Runlong Yu, *Critical Ledgers and Scale-Defect Cascades for Navier-Stokes*, arXiv `2606.13887`, DOI `10.48550/arXiv.2606.13887`;
- Runlong Yu, *Invisible Defect Cascades for Navier-Stokes Regularity*, arXiv `2606.12756`, DOI `10.48550/arXiv.2606.12756`.

The key strategic correction is that Yu already proves a finite-scale whole-space near-field stretching mechanism of the shape sought in K4–K6: pairwise filtered-direction defect, magnitude-weighted conversion to a vorticity increment, diffusion absorption, and an explicit residual surplus. The unresolved step is not the local angular inequality itself. It is the scale-uniform closure of far-field strain, commutator increments, localization, recurrence/crossing charges and the infinite critical sum.

No theorem from these sources is imported without its hypotheses.

## 1. Magnitude-weighted direction increments

For unit directions `xi`, `eta` and amplitudes

```text
0 <= a <= b,
```

`NSTriadKNLuoMagnitudeWeightedDirectionIncrementExact.agda` proves the exact identity

```text
|a xi - b eta|^2
  = (b-a)^2 + a b |xi-eta|^2.
```

Consequently,

```text
a^2 |xi-eta|^2 <= |a xi-b eta|^2.
```

This is a radical-free, ordered-amplitude constant-one estimate. It is stronger at the squared algebraic level than the conservative constant-two unsquared inequality used in the source. Most importantly, no derivative of `xi = omega/|omega|` occurs.

## 2. Sharp angular strain contraction

For unit `xi` and unit radial direction `r`, define

```text
c^2 = (xi dot r)^2,
s^2 = |xi cross r|^2 = 1-c^2.
```

`NSTriadKNLuoFilteredDirectionContractionExact.agda` proves

```text
4 c^2 s^2 + (1-2c^2)^2 = 1,
```

hence

```text
4 (xi dot r)^2 |xi cross r|^2 <= 1.
```

This is the squared form of the sharp `|cos theta sin theta| <= 1/2` factor in the filtered strain-kernel contraction.

## 3. Finite pairwise defect to increment envelope

`NSTriadKNLuoFilteredPairwiseDefectFiniteExact.agda` represents a finite quadrature of the near-field kernel by literal nonnegative cells. Cellwise,

```text
weight * min(a,b)^2 |xi-eta|^2
  <= weight * |a xi-b eta|^2.
```

Recursive summation yields

```text
finitePairwiseDefect <= finiteIncrementEnvelope.
```

A finite kernel-contraction coefficient no larger than one then transports the positive near-field term into the increment envelope. A separately proved increment-to-diffusion estimate closes the finite coercivity chain. The continuum principal-value contraction and difference-quotient estimate remain separate analytic obligations.

## 4. Exact filtered-enstrophy surplus

`NSTriadKNLuoFilteredEnstrophySurplusExact.agda` starts from the literal balance

```text
Eout + P
  <= Ein + Vnear + Vfar + Fcom + L,
```

and the two producer estimates

```text
Vnear <= etaNear P + lowerEnstrophy,
Fcom  <= etaCom P + incrementDefect + commutatorLocalization.
```

It proves exactly

```text
Eout + (1-etaNear-etaCom) P
  <= Ein
     + lowerEnstrophy
     + Vfar
     + incrementDefect
     + localization
     + commutatorLocalization.
```

The same inequality is then multiplied by literal nonnegative critical weights and summed over a finite scale list. No far-field, increment or localization term is discarded as harmless.

This reproduces the source's finite-scale surplus architecture while preserving its authority boundary: an unweighted scale-uniform theorem still requires independent summability of the surviving positive terms.

## 5. Deterministic bad-excursion residence tax

`NSTriadKNLuoBadExcursionResidenceTaxExact.agda` replaces an empirical residence slogan by a finite deterministic theorem.

On each bad interval assume

```text
rightDefect + lambda * integratedDefect
  <= leftDefect + positiveForcing,

threshold * duration <= integratedDefect.
```

Then

```text
lambda * threshold * duration
  <= leftDefect + positiveForcing.
```

Finite recursive summation gives

```text
lambda * threshold * totalBadDuration
  <= totalEntryCharge + totalPositiveForcing.
```

An explicit crossing budget then yields

```text
lambda * threshold * totalBadDuration
  <= initialDefect + crossingCharge + totalPositiveForcing.
```

Thus repeated bad excursions are not free. Either the PDE forcing or a quantified boundary-crossing charge must pay for recurrence. The Navier–Stokes estimate controlling that crossing charge remains open.

## 6. Bad-lane amplitude absorption

A small bad-set measure alone does not control a large transfer. `NSTriadKNLuoBadExcursionYoungAbsorptionExact.agda` therefore keeps both factors.

Under

```text
4 epsilon q = 1,
```

it proves the exact scaled Young factorization

```text
epsilon x^2 + q y^2 - x y
  = q (2 epsilon x-y)^2 >= 0.
```

If

```text
Tbad <= A M + R0,
A^2 <= cA V + RA,
q M^2 <= cM V + RM,
```

then

```text
Tbad
  <= (epsilon cA + cM) V
     + epsilon RA + RM + R0.
```

The unresolved physical inputs are now sharp: a defect-square budget and an amplitude-square budget with a combined coefficient strictly below the allocated bad-lane margin.

## 7. Three-lane strict critical closure

`NSTriadKNLuoThreeLaneCriticalClosureExact.agda` combines independently proved good-high-high, bad-high-high and lower-interaction estimates:

```text
G <= etaG V + RG,
B <= etaB V + RB,
L <= etaL V + RL.
```

It proves

```text
G+B+L
  <= (etaG+etaB+etaL)V + RG+RB+RL.
```

Given the finite critical balance

```text
Xout + V <= Xin + G+B+L,
```

it derives

```text
Xout + (1-etaG-etaB-etaL)V
  <= Xin + RG+RB+RL.
```

The strict numerical theorem remains exactly

```text
etaG + etaB + etaL < 1.
```

## 8. Five-class dyadic filtered-vorticity ledger

`NSTriadKNLuoDyadicFilteredVorticityLedgerExact.agda` gives each shell five named source coordinates:

```text
HH, LH, HL, comparable, commutator.
```

For each shell,

```text
Eout + D = Ein + HH + LH + HL + comparable + commutator.
```

The module multiplies this identity by the literal nonnegative critical weight and proves the exact finite weighted equality. There is no generic remainder constructor. Deriving the physical filtered equation and exact paraproduct index ranges remains a PDE/Fourier task.

## 9. Residual-basis comparison

Yu's filtered-vorticity residual basis is

```text
far-field strain,
increment/commutator defect,
localization.
```

DASHI's broader ledger is

```text
collar, tail, pressure, low, phase, passive, fragmentation.
```

`NSTriadKNLuoYuResidualBasisComparisonExact.agda` keeps these bases distinct. Only after explicit physical identification proofs are supplied does it derive

```text
sevenTotal = yuFilteredTotal + pressure.
```

This exposes a real formulation difference: pressure disappears from the curl equation but remains present in local-energy and CKN routes. It is not legitimate to identify the two ledgers merely because their prose descriptions overlap.

## 10. Physical angular kernel cancellation

The Round 20 Fourier multiplier is complemented by `NSTriadKNLuoPeriodicBiotSavartAngularCancellationExact.agda`.

For

```text
K(r,omega)
  = (r cross omega) tensor r
    + r tensor (r cross omega),
```

it proves:

```text
K is symmetric,
trace K = 0,
K(-r,omega) = K(r,omega),
K(e1,omega)+K(e2,omega)+K(e3,omega)=0.
```

The final identity is an exact coordinate spherical-cubature witness of the mean-zero angular structure needed by the strain principal value. It is not yet the continuum spherical integral or the periodic distribution construction.

## 11. Polynomial cross-product defect evolution

`NSTriadKNLuoCrossProductDefectEvolutionAlgebraExact.agda` proves the complete perturbation formula

```text
(a+hA) cross (b+hB)
  = a cross b
    + h(A cross b + a cross B)
    + h^2(A cross B).
```

Squaring gives a fourth-order polynomial whose linear coefficient is exactly

```text
2 (a cross b) dot (A cross b + a cross B).
```

Derivative pairs are added recursively, and the defect rate is proved additive. This produces an exact five-source split for

```text
advection, stretching, subgrid, kernel, tail.
```

The source terms are therefore structurally ready for K7. What remains is to instantiate them from the filtered Navier–Stokes equation and prove the dissipative differential inequality.

## Updated highest-alpha frontier

The earlier K1–K16 roadmap remains useful, but the source audit changes the weighting of its steps.

Substantially closed at finite/algebraic level in this branch:

```text
K1 angular numerator and finite cancellation,
K2-K3 five-class finite weighted ledger,
K4 angular contraction,
K5 pairwise-defect to increment bridge,
K6 finite near-field surplus algebra,
K7 polynomial defect evolution and exact source split,
K8 deterministic excursion tax,
K9-K10 two-factor bad-lane coefficient algebra,
K13-K14 three-lane finite critical closure.
```

Still genuinely analytic and open:

```text
1. construct the periodic principal-value strain kernel from the multiplier;
2. prove continuum spherical cancellation and Calderon-Zygmund bounds;
3. derive the literal dyadic filtered equation and all paraproduct ranges;
4. adapt Yu's whole-space finite-scale near-field estimate to the chosen
   periodic shell normalization;
5. prove unweighted far-field annular/Carleson control;
6. prove scale-summability of the commutator increment defect;
7. prove localization and periodic smooth-remainder summability;
8. instantiate the five-source cross-product defect evolution from NS;
9. prove the PDE crossing-charge and amplitude-square budgets;
10. publish explicit etaGood + etaBad + etaLower < 1;
11. pass uniformly to the infinite critical shell sum;
12. invoke the critical restart/continuation theorem.
```

The most concentrated remaining original theorem is no longer merely “finite residence.” It is:

```text
filtered residual taxation + recurrence taxation
  -> strict scale-uniform critical absorption.
```

Every far-field, increment, localization, crossing and amplitude term must be charged to diffusion or to a summable data-controlled reservoir.

## Validation

```bash
AGDA_JOBS=1 bash scripts/check_ns_luo_filtered_defect_excursion_round21.sh
```

The checker cascades through Round 20, rejects holes, postulates, unsafe escapes, trust primitives and placeholders, checks theorem and source markers, and invokes the pinned Agda 2.9 cumulative root.

No Agda kernel success, continuum regularity theorem or Clay-level solution is asserted until independently observed and proved.

# NS Luo Galerkin defect diffusion — Round 22

## Scope

Round 22 attacks the finite Galerkin, one-shell falsification tranche identified after Round 21.  It does not assume that a two-point angular defect automatically acquires a favorable Laplacian sign.  Instead it computes that sign exactly, records the obstruction, and repairs the damping at the level where it is genuinely available: the two input frequencies.

The selected route remains global, periodic and pressure-free after taking curl.  The live finite quantities are indexed by both a Galerkin cutoff `N` and a shell cutoff `Q`; no continuum or infinite-cutoff conclusion is inferred from finite algebra alone.

## 1. Exact filtered-vorticity stress equation

`NSTriadKNLuoFilteredVorticitySubfilterStressExact.agda` derives the componentwise exact stress identity

```text
d (F(ab) - a_bar b_bar)
  = F(a db) - a_bar db_bar
```

under the primitive product rule and divergence-free identities.  Applied to transport and stretching, it yields

```text
d_t omega_bar + u_bar . grad omega_bar
  = omega_bar . grad u_bar + nu Delta omega_bar
    - div tau^{u omega} + div tau^{omega u}.
```

The stresses are exact residuals, not closure models.

`NSTriadKNLuoFiniteParaproductRangePartitionExact.agda` then gives literal finite shell-range constructors for strict-low, comparable and strict-high inputs.  Eight supported non-low-low triadic patterns map to

```text
HH, LH, HL, CC,
```

while the differentiated commutator remains a distinct fifth constructor.  There is no generic remainder constructor.

## 2. Galerkin filtered-enstrophy identity before ledger abstraction

`NSTriadKNLuoGalerkinCriticalFilteredEnstrophyExact.agda` starts from the finite coordinate equation

```text
omega_t - nu Delta omega = HH + LH + HL + CC + Com
```

and proves after multiplication by `2 omega`

```text
2 omega omega_t - 2 nu omega Delta omega
  = 2 omega (HH + LH + HL + CC + Com).
```

The result is summed over coordinates, supplied with the periodic integration-by-parts identity, and multiplied by a literal critical shell weight.  Thus the five source coordinates occur inside the differential equation before the energy ledger is formed.

## 3. The physical-space F3 damping shortcut fails

Let

```text
C = a cross b,
A = |C|^2.
```

For one spatial derivative, Round 22 proves

```text
C_1 = a_1 cross b + a cross b_1,
C_2 = a_2 cross b + 2 a_1 cross b_1 + a cross b_2,
```

and

```text
d_2 |C|^2 = 2 |C_1|^2 + 2 C dot C_2.
```

Consequently the diffusion acting separately on the two vorticity inputs obeys

```text
2 C dot (a_2 cross b + a cross b_2)
  = d_2 |C|^2
    - 2 |C_1|^2
    - 4 C dot (a_1 cross b_1).
```

`NSTriadKNLuoTwoPointCrossDefectDiffusionExact.agda` proves this identity and its finite spatial sum.  It also gives explicit rational jets for which the mixed term is `+4` and `-4`.

Therefore the desired damping cannot be justified merely by applying a Poincare inequality to the product `a cross b`.  The high-high product can collapse to a low or zero output frequency, and the mixed-gradient term is not sign-definite.

## 4. Correct F3 repair: retain both input frequencies

`NSTriadKNLuoPairFrequencyDefectDiffusionExact.agda` records two input Laplacian eigenvalues `lambda_L`, `lambda_R`, a shell floor `kappa`, viscosity `nu` and a nonnegative defect amplitude `A`.  From

```text
kappa <= lambda_L,
kappa <= lambda_R,
```

it proves

```text
2 nu kappa A
  <= nu (lambda_L + lambda_R) A.
```

This estimate is recursively summed over a finite interaction list.

The same module contains a high-high-to-zero-output witness: output-frequency damping is zero while the two unit input frequencies still supply two units of diffusion.  This fixes the correct location of the coercivity mechanism.

`NSTriadKNLuoGalerkinPairDefectEvolutionExact.agda` then proves that an exact finite pair evolution

```text
A_t + nu (lambda_L + lambda_R) A
  = F_adv + F_stretch + F_subgrid + F_kernel + F_tail
```

implies

```text
A_t + 2 nu kappa A
  <= F_adv + F_stretch + F_subgrid + F_kernel + F_tail.
```

Nonnegative quadrature and critical weights are transported through a finite sum.  This closes the finite spectral damping algebra of F3.  Constructing the cells from the actual periodic Fourier convolution remains analytic work.

## 5. Five-source F4 taxation

`NSTriadKNLuoFiveSourceDefectCriticalTaxExact.agda` keeps the five sources named.  If each source satisfies

```text
F_i <= eta_i D + A_i + B_i X_integrated,
```

then it proves

```text
sum_i F_i
  <= eta_total D + A_total + B_total X_integrated.
```

Combined with an integrated defect balance, this gives

```text
A_out + (1-eta_total)D
  <= A_in + A_total + B_total X_integrated.
```

No physical source estimate is manufactured by this algebra.  The required theorem is still the Navier-Stokes production of the five taxes with `eta_total < 1` after all other lanes are included.

## 6. F6 must use hysteresis

A single threshold gives no positive cost for repeated crossings: a continuous quantity may oscillate across it arbitrarily often.  `NSTriadKNLuoBadExcursionHysteresisTaxExact.agda` therefore replaces the single boundary by lower and upper thresholds separated by a gap `h`.

Every re-entry rise satisfies

```text
h <= positiveRise.
```

For upper entry charge `delta`, the module proves

```text
h delta <= delta positiveRise
```

and recursively

```text
h * totalEntryCharge
  <= delta * totalPositiveCrossingVariation.
```

The physical F6 producer is now precise: prove a scale-uniform bound on the positive variation of the defect and choose a nondegenerate hysteresis gap.  Merely enumerating components of `{A_q > delta}` is insufficient.

## 7. Raw Bernstein cannot close F7

At three-dimensional shell scale `s`, a direct pointwise Bernstein model gives

```text
M_Bernstein = s^3 E,
D            = s^2 E.
```

`NSTriadKNLuoBadAmplitudeBernsteinScalingNoGoExact.agda` chooses `s = C+1` for any proposed scale-independent coefficient `C` and proves

```text
s^3 - C s^2 = s^2.
```

Thus raw shell amplitude is supercritical by one full frequency power.

`NSTriadKNLuoDissipationWavenumberAmplitudeRepairExact.agda` records the correct conditional repair.  If a dynamically viscous high shell satisfies

```text
amplitude <= c nu lambda^2,
```

then

```text
amplitude * E <= c (nu lambda^2 E).
```

`NSTriadKNLuoFiniteDissipationWavenumberSplitExact.agda` implements the exact finite low/high partition:

```text
sum transfer
  <= eta * sum high diffusion + sum low reservoir.
```

The unresolved theorem is to derive the high-shell condition from Navier-Stokes and critically integrate the low reservoir without assuming the target norm.

## 8. Lower-lane reduction

`NSTriadKNLuoPeriodicLowTransportSkewCancellationExact.agda` proves the finite product rule

```text
d_j (u_j omega_i^2)
  = (d_j u_j) omega_i^2
    + 2 omega_i u_j d_j omega_i
```

and, under periodic flux cancellation and divergence-free low velocity,

```text
2 <u_< . grad omega_q, omega_q> = 0.
```

The bare resolved low transport therefore consumes no viscosity.  F9 is reduced to the filter commutator, low-frequency stretching, comparable interactions and tails.

## 9. Periodic kernel and near-field progress

`NSTriadKNLuoStrainKernelSphericalMeanZeroExact.agda` upgrades the Round 21 coordinate cubature to the complete algebraic spherical cancellation.  From the isotropic moment law

```text
<r_i r_j> = m delta_ij
```

all nine averaged entries of

```text
(r cross omega) tensor r + r tensor (r cross omega)
```

are proved to vanish.  The value of `m` and the sphere normalization are irrelevant to the cancellation.

`NSTriadKNLuoFiniteFilterIncrementJensenExact.agda` proves, for rational-square quadrature weights,

```text
|sum_i w_i delta_i|^2
  <= (sum_i w_i) sum_i w_i |delta_i|^2.
```

For normalized weight one this is a contraction from a filtered increment to the weighted unfiltered increment energy.

The remaining F5 work is analytic: construct the periodic principal-value distribution, prove the isotropic moment law for the actual sphere integral, establish the periodic Calderon-Zygmund bounds, pass the finite quadrature to convolution, and prove the difference-quotient-to-diffusion estimate uniformly in scale.

## 10. Residual and terminal closure algebra

`NSTriadKNLuoFiniteGeometricResidualTailExact.agda` proves

```text
(1-rho) sum_{j=0}^n rho^j = 1-rho^(n+1)
```

and transports a residual coefficient through the finite sum.  Physical F10 producers must still supply a uniform ratio `0 <= rho < 1` for the actual far-field, commutator and truncation tails.

`NSTriadKNLuoCriticalProductionGronwallClosureExact.agda` implements the admissible final finite-cutoff form

```text
X_out + D <= X_in + N,
N <= eta D + A + B X_integrated
```

implying

```text
X_out + (1-eta)D
  <= X_in + A + B X_integrated.
```

The parameters `eta`, `A` and `B` are shared by a family indexed by both Galerkin and shell cutoffs.  An uncontrolled critical supremum or BKM norm is not part of the interface.

## Updated highest-alpha frontier

Round 22 changes the dependency graph materially.

The finite F3 damping mechanism is no longer mysterious:

```text
input pair frequencies
  -> nu(lambda_L+lambda_R)A
  -> 2 nu kappa A.
```

The genuinely open chain is now:

```text
actual periodic Fourier pair cells
  -> uniform five-source taxes
  -> hysteretic positive-variation tax
  -> dissipation-wavenumber amplitude/low-reservoir tax
  -> strict total eta < 1.
```

In exact theorem form, the remaining original analysis is:

1. construct the actual Galerkin/Fourier cells and prove the shell-range support theorem;
2. derive the five source expressions with constants uniform in `q`, `Q` and `N`;
3. prove the positive-variation estimate required by hysteretic re-entry;
4. prove the dynamic high-mode amplitude condition and critical low-mode reservoir bound;
5. complete the periodic principal-value and difference-quotient analysis;
6. sum far-field, commutator and cutoff tails with uniform ratios;
7. prove the combined strict coefficient is below one;
8. apply continuous Gronwall, pass both cutoffs to infinity and invoke critical restart.

## Authority boundary

The branch records peer-reviewed sources for Bony calculus, Fourier analysis, periodic Navier-Stokes energy identities, Constantin--Fefferman direction geometry, Leonard's exact subfilter stress terminology, and the Cheskidov--Shvydkoy dissipation-range strategy.  Runlong Yu's 2026 filtered-vortex paper remains explicitly identified as an arXiv preprint.

Independent website, PhilArchive, Scribd and Substack sketches are not used as proof authorities.  Their recurring architecture is treated only as evidence that the same coercivity gap is repeatedly encountered.

Round 22 does not assert unconditional Navier-Stokes regularity or Clay-level completion.

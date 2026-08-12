# NS Round 42 — master defect, derivative relocation, amplitude allocation, and support-overlap Com

This tranche continues the shortest post-Round-41 Navier–Stokes path. It does **not** instantiate the six lower-risk owners, fabricate a nine-owner reserve, or advance downstream submission receipts before the three hard physical owners are real. No GitHub Actions workflow is added or triggered.

## 1. HH-good: literal amplitude allocation

Round 41 proved that the raw shortcut

```text
W <= C X D
```

cannot hold uniformly for the literal local weight

```text
W(a,b) = a^2 b^4,
```

because the two sides have different amplitude degree.

Round 42 factors the actual monomial in the two natural quadratic ways:

```text
a^2 b^4 = a^2 (b^2 b^2),
a^2 b^4 = b^2 (a^2 b^2).
```

`HHGoodAmplitudeAllocation` selects a quadratic factor `E_quad` and proves, samplewise and after the actual kernel weights are summed,

```text
weightedLocalMass <= E_quad * weightedQuarticCore.
```

A second same-object estimate

```text
weightedQuarticCore <= integralCritical * dissipation
```

then yields

```text
weightedLocalMass <= E_quad * integralCritical * dissipation.
```

`periodizedHHGoodOwnerFromLiteralAmplitudeAllocation` feeds this directly into the existing Round-41 periodized Young owner.

## 2. HH-good correction: bare kinetic energy is not a pointwise vorticity resource

The vorticity amplitudes `a,b` are not velocity amplitudes. The repository's exact Biot–Savart theorem gives for every transverse nonzero Fourier mode

```text
|u_k|^2 = |k|^-2 |omega_k|^2,
```

and Round 42 rearranges this to

```text
|omega_k|^2 = |k|^2 |u_k|^2.
```

Therefore a modewise kinetic-energy bound `|u_k|^2 <= E0` only gives

```text
|omega_k|^2 <= |k|^2 E0,
```

not `|omega_k|^2 <= E0` uniformly in shell.

The exact rational witness

```text
k=(2,0,0),
omega=(0,0,-2),
u=B_k omega=(0,1,0)
```

has

```text
|u|^2=1,
|omega|^2=4.
```

`NSTriadKNHHGoodKineticEnergyAllocationNoGoRound42Exact` formally refutes the bare pointwise kinetic allocation.

### The order-zero strain kernel does not repair this pointwise loss

Round 40 proves the literal Fourier strain multiplier is order zero:

```text
S_(r k)(omega) = S_k(omega).
```

Round 42 places this beside the exact Biot–Savart scaling on the same scaled projection mode:

```text
|B_(r k) omega|^2 = r^-2 |B_k omega|^2,
S_(r k)(omega)     = S_k(omega).
```

Hence the already-absolute-valued order-zero strain multiplier/kernel does not contain the missing `r^-2` factor. A kinetic-energy repair must recover the inverse derivative before/outside that order-zero kernel estimate.

## 3. HH-good positive route: the parabolic window recovers the kinetic scale

The pointwise kinetic route fails, but Luo's terminal window has the exact parabolic scale

```text
|I_q| ~ lambda_q^-2.
```

Round 42 proves on the repository's dyadic scales

```text
lambda_q^2 * lambda_q^-2 = 1
```

and a finite positive-measure version of the time-localized estimate. If

```text
sum_i dt_i <= c lambda_q^-2
```

and each selected vorticity square obeys the modewise kinetic consequence

```text
omega_i^2 <= lambda_q^2 E0,
```

then

```text
sum_i dt_i omega_i^2 <= c E0.
```

`NSTriadKNHHGoodParabolicWindowKineticRecoveryRound42Exact` proves this exactly.

Round 42 then carries the same cancellation through the literal amplitude allocation. If, on the same time cells,

```text
omega_i^2 <= lambda_q^2 E0,
Q_i <= Q,
sum_i dt_i <= c lambda_q^-2,
```

then

```text
sum_i dt_i omega_i^2 Q_i <= c E0 Q.
```

And if the common quartic envelope obeys

```text
Q <= integralCritical * dissipation,
```

then `NSTriadKNHHGoodParabolicAmplitudeAllocationRound42Exact` proves

```text
sum_i dt_i omega_i^2 Q_i
  <= c E0 * integralCritical * dissipation.
```

This is the concrete repaired version of the false pointwise `W<=E0 X D` shortcut. The remaining physical theorem is to identify the actual HH-good terminal-window integral with these positive cells after the mandatory

```text
PV cancellation -> residual -> shell localization -> directional threshold
```

ordering, and to prove the quartic envelope on that same object. The annular strain-kernel/sample identity and smooth torus correction remain separate physical seams.

## 4. Keep the HH-good Young split until the reserve stage

For the localized quadratic factor,

```text
P <= epsilon D + (C delta E_quad)/(4 epsilon) X,
```

Round 42 proves from the exact positive-threshold inverse law

```text
epsilon1 <= epsilon2  ==>  epsilon2^-1 <= epsilon1^-1.
```

Thus the critical coefficient is antitone in `epsilon`. Subject to the final viscosity budget, the largest admissible Young split minimizes this remainder. `epsilon` should remain free until the other owner costs are known.

## 5. HH-bad: derivative relocation is exact, but two real derivatives remain two

On the actual integer Fourier / `Complex3` physical triad `p+q=k`, Round 42 proves

```text
k . u_p = q . u_p,
k . u_q = p . u_q
```

from resonance and divergence freedom.

The two-factor diagnostic is also exact:

```text
(k.u_p)(k.u_q) = (q.u_p)(p.u_q).
```

Therefore incompressibility can relocate an output derivative but cannot turn two genuine derivative-bearing factors into one.

## 6. HH-bad stronger same-object audit: the literal vorticity nonlinearity is order zero

The repository already contains the actual finite Fourier vorticity interaction

```text
F(p,r) = (omega_p.r) u_r - (u_p.r) omega_r,
u_p = |p|^-2 (p cross omega_p).
```

Round 42 now scales the *literal object*, not the schematic Schur expression. Under common positive rational frequency scaling

```text
p -> s p,
r -> s r,
```

with vorticity amplitudes fixed, it proves exactly

```text
u_(s p) = s^-1 u_p,
F(s p,s r) = F(p,r).
```

Both the ordered and symmetrized vorticity interactions are invariant. Pairing them with a fixed output vorticity is invariant as well:

```text
omega_k . F(s p,s r) = omega_k . F(p,r).
```

So the raw vorticity convolution and its fixed-output enstrophy-production scalar carry **no net common HH derivative**. The explicit derivative in the vorticity equation is already cancelled by the Biot–Savart inverse derivative.

This materially sharpens the HH-bad frontier. The Round-33 growth

```text
R_q = 2 lambda_q
```

belongs to the later half-kernel/Bernstein bounding lane; it is not the scaling of the literal vorticity convolution itself. Consequently the next same-object theorem must trace

```text
literal vorticity interaction
  -> shell/source/curvature/energy normalization
  -> RawBadGainSample.rawGain
```

before assigning a one-derivative inverse-shell Schur cost. If that trace never reintroduces one net `lambda_q`, the current inverse-shell compensation architecture should be simplified/redesigned rather than imposed on the raw dynamics.

## 7. HH-bad conditional reserve constant, if the later lane really has one derivative

If the same-object trace above does produce the Round-41 one-derivative density

```text
c_q = C_q lambda_q^-1,
```

then Round 42 composes it exactly with the Round-33 raw bounded-lane ratio

```text
R_q = 2 lambda_q
```

to prove

```text
c_q R_q = 2 C_q.
```

If `C_q <= C_bad`, the raw shell-growth neutralization cost is at most `2 C_bad`. The directional bad-set threshold contributes the separate `delta^-1` cost, so the actual bounded HH-bad reserve coefficient is

```text
eta_HHb <= 2 C_bad / delta.
```

The Round-40 symbolic optimizer therefore has conditional bad constant

```text
B = 2 C_bad
```

and balance law

```text
A r^3 = 4 C_bad,
delta = r^2.
```

`NSTriadKNHHOneDerivativeThresholdOptimizerRound42Exact` reuses the existing Round-40 global-minimum theorem with this coefficient. These constants are now explicitly conditional on the missing same-object bridge; they are not attributed to the raw vorticity interaction.

## 8. Master directional defect: threshold profile and packing reduction

Round 41 proved on one full classified carrier

```text
D_dir = D_good + D_bad,
delta E_bad <= D_bad <= D_dir,
```

and a finite layer-cake identity.

Round 42 constructs the rational superlevel classifier directly from

```text
Theta = 1 - (xi.eta)^2
```

and proves

```text
s1 <= s2  ==>  M(s2) <= M(s1).
```

It also proves the exact finite reduction needed for a stopping-time/Carleson experiment. If a selected family of shell-time boxes satisfies

```text
sum_box D_dir(box) <= P,
```

then automatically

```text
sum_box E_bad(box) <= delta^-1 P
```

and any local

```text
G_box^2 <= C_good delta D_good(box)
```

bounds sum to

```text
sum_box G_box^2 <= C_good delta P.
```

No physical Carleson estimate is asserted. A genuine theorem needs an actual stopping/packing family rather than uncontrolled repeated boxes.

## 9. Com: support overlap is enough

Round 41 asked for the exact model equality

```text
physical pair product = pairProduct(sixThreeGramCell(gap)).
```

Round 42 proves this is stronger than necessary. It suffices to establish on the literal one-channel product

```text
P(q,r) <= m(q,r) * g(|q-r|),
0 <= m(q,r) <= 1,
```

where `g` is the already-certified centered `(L6,L3)` two-branch squared gap.

From this, Round 42 constructs an actual Round-35 `GramInterferenceCell` whose `pairProduct` is the literal physical product, whose overlap is `g`, and whose outer factors are one. The Round-40 single-channel realization and both existing half-dyadic Cotlar decays then follow. A Boolean `0/1` support graph is included as the canonical specialization.

The shortest remaining Com theorem is therefore

```text
literal U_q^* U_r product
  <= shellSupport(q,r) * sixThreeGap(|q-r|),
```

plus the adjoint-face equality already supplied by skew adjunction. No additional finite singular-value theorem is needed because Round 41 already proved the exact full commutator energy is the one-channel square.

## Revised falsification / implementation order

1. **HH-bad same-object shell audit** — trace the literal scale-invariant vorticity interaction into the actual bad gain and determine exactly where, if anywhere, the Round-33 `lambda_q` growth re-enters. Apply the one-derivative Schur lane only if that trace justifies it.
2. **Com support-overlap theorem** — prove the literal `U_q^* U_r` support/product bound and construct the Com owner.
3. **HH-good parabolic physical realization** — annular strain-kernel/sample identification, kinetic-to-vorticity `lambda_q^2` inside the actual `lambda_q^-2` terminal window, residual quartic envelope, and smooth torus correction.
4. Instantiate the six lower-risk owners.
5. Run the exact threshold/Young-aware nine-owner primal/dual reserve test.

Only a certified

```text
sum eta_i < 1
```

should trigger the downstream `CanonicalAnalyticPhysicalLeaves` / maximal-time / global-solution / submission tail. If the exact dual certificate forces `sum eta_i >= 1`, redesign the architecture rather than continuing downstream.

The downstream 28-lemma cutset should then be audited as **new analytic estimates versus same-object/provenance reopenings**. That classification is deliberately deferred until the reserve gate succeeds.
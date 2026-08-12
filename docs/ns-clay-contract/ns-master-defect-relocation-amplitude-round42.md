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

Round 42 now places this beside the exact Biot–Savart scaling on the *same scaled projection mode*:

```text
|B_(r k) omega|^2 = r^-2 |B_k omega|^2,
S_(r k)(omega)     = S_k(omega).
```

Hence the already-absolute-valued order-zero strain multiplier/kernel does not contain the missing `r^-2` factor. A kinetic-energy repair must recover the inverse derivative before/outside that order-zero kernel estimate.

## 3. HH-good positive route: parabolic time localization exactly recovers the kinetic scale

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

This is `NSTriadKNHHGoodParabolicWindowKineticRecoveryRound42Exact`.

So the current highest-alpha HH-good route is no longer “find some mysterious extra quadratic resource”. A concrete candidate exists:

```text
pointwise kinetic -> costs lambda_q^2
parabolic time window -> returns lambda_q^-2
net localized cost -> E0.
```

The remaining physical theorem is to identify the actual HH-good time integral with this positive parabolic-window measure **while preserving the quartic core, PV cancellation, shell localization, and directional threshold ordering**. No continuum time-integral theorem is assumed by the finite reduction.

## 4. Keep the HH-good Young split until the reserve stage

For the abstract localized quadratic factor,

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

The decisive diagnostic is also exact:

```text
(k.u_p)(k.u_q) = (q.u_p)(p.u_q).
```

Therefore if the literal bad-gain symbol contains two independent derivative-bearing contractions, incompressibility alone leaves two derivative factors. The Round-41 inverse-shell route must be justified by the literal bad-gain symbol containing only one genuine derivative factor, or by an upstream exact cancellation/defect subtraction that removes the other. If neither occurs, this branch is falsified.

## 6. HH-bad: the reserve constant is explicit

Round 33 has

```text
R_q = 2 lambda_q.
```

The Round-41 one-derivative certificate has

```text
c_q = C_q lambda_q^-1.
```

Round 42 proves exactly

```text
c_q R_q = 2 C_q.
```

If `C_q <= C_bad`, the raw shell-growth neutralization cost is at most `2 C_bad`.

The directional bad-set threshold contributes the separate `delta^-1` cost, so the actual bounded HH-bad reserve coefficient is

```text
eta_HHb <= 2 C_bad / delta.
```

The Round-40 symbolic optimizer therefore has

```text
B = 2 C_bad
```

and balance law

```text
A r^3 = 4 C_bad,
delta = r^2.
```

`NSTriadKNHHOneDerivativeThresholdOptimizerRound42Exact` reuses the existing Round-40 global-minimum theorem with this coefficient.

## 7. Master directional defect: threshold profile and packing reduction

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

No physical Carleson estimate is asserted. A genuine theorem will need an actual stopping/packing family rather than uncontrolled repeated boxes.

## 8. Com: support overlap is enough

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

1. **HH-bad literal symbol audit** — prove one genuine derivative factor after all exact cancellations, or falsify the inverse-shell route.
2. **Com support-overlap theorem** — prove the literal `U_q^* U_r` support/product bound and construct the Com owner.
3. **HH-good parabolic physical realization** — annular strain-kernel/sample identification, kinetic-to-vorticity `lambda_q^2` allocation inside the actual `lambda_q^-2` terminal window, residual quartic estimate, and smooth torus correction.
4. Instantiate the six lower-risk owners.
5. Run the exact threshold/Young-aware nine-owner primal/dual reserve test.

Only a certified

```text
sum eta_i < 1
```

should trigger the downstream `CanonicalAnalyticPhysicalLeaves` / maximal-time / global-solution / submission tail. If the exact dual certificate forces `sum eta_i >= 1`, redesign the architecture rather than continuing downstream.

The downstream 28-lemma cutset should then be audited as **new analytic estimates versus same-object/provenance reopenings**. That classification is deliberately deferred until the reserve gate succeeds.
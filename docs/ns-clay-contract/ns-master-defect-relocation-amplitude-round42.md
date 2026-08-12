# NS Round 42 — master defect, derivative relocation, amplitude allocation, and support-overlap Com

This tranche continues the shortest post-Round-41 Navier–Stokes path.  It does **not** instantiate the six lower-risk owners, fabricate a nine-owner reserve, or advance the downstream submission receipts before the three hard physical owners are real.  No GitHub Actions workflow is added or triggered.

## 1. HH-good: the missing quadratic resource is allocated literally

Round 41 proved that the raw shortcut

```text
W <= C X D
```

cannot hold uniformly for the literal local weight

```text
W(a,b) = a^2 b^4,
```

because the two sides have different amplitude degree.

Round 42 now factors the *actual* monomial in the only two natural quadratic-energy ways:

```text
a^2 b^4 = a^2 (b^2 b^2),
a^2 b^4 = b^2 (a^2 b^2).
```

`HHGoodAmplitudeAllocation` lets the physical proof choose the leg that is genuinely controlled by the data energy `E0`.  It then proves, samplewise and after the real kernel weights are summed,

```text
weightedLocalMass <= E0 * weightedQuarticCore.
```

A single remaining physical estimate

```text
weightedQuarticCore <= integralCritical * dissipation
```

therefore yields the required

```text
weightedLocalMass <= E0 * integralCritical * dissipation.
```

`periodizedHHGoodOwnerFromLiteralAmplitudeAllocation` feeds this result directly into the Round-41 periodized Young owner.  Thus the HH-good data-energy seam is no longer one opaque degree-six inequality: it is two same-object physical questions.

1. Which amplitude square is bounded by the actual data energy?
2. Does the corresponding residual quartic core obey the actual critical-times-dissipation bound?

The annular strain-kernel/sample identification and smooth torus correction remain separate physical seams.

## 2. Keep the HH-good Young split until the reserve stage

The Round-41 owner has

```text
P <= epsilon D + (C delta E0)/(4 epsilon) X.
```

Round 42 proves directly from the exact `PositiveThreshold` inverse law that

```text
epsilon1 <= epsilon2  ==>  epsilon2^-1 <= epsilon1^-1.
```

For nonnegative effective kernel constant, the critical coefficient is therefore antitone in `epsilon`.  Subject to the final viscosity budget, the largest admissible Young split minimizes this particular critical remainder.  `epsilon` should not be frozen before the other owner costs are known.

## 3. HH-bad: incompressibility relocates derivatives but does not delete two of them

On the actual integer Fourier / `Complex3` physical triad `p+q=k`, Round 42 proves

```text
k . u_p = q . u_p,
k . u_q = p . u_q
```

from resonance and divergence freedom.  This is the correct pre-Schur derivative relocation.

The decisive diagnostic is also exact:

```text
(k.u_p)(k.u_q) = (q.u_p)(p.u_q).
```

Therefore if the literal bad-gain symbol contains two independent derivative-bearing contractions, incompressibility alone leaves two derivative factors.  It cannot justify the Round-41 inverse-shell route.  The physical same-object theorem must show that only one derivative-bearing factor is genuinely present, or an upstream exact cancellation/defect subtraction must remove the other.  If neither occurs, this branch is falsified.

## 4. HH-bad: the reserve constant is now explicit

Round 33 has the raw ratio

```text
R_q = 2 lambda_q.
```

Round 41's one-derivative certificate has

```text
c_q = C_q lambda_q^-1.
```

Round 42 proves exactly

```text
c_q R_q = 2 C_q.
```

If `C_q <= C_bad`, the pre-threshold shell-growth cost is at most `2 C_bad`.

The directional bad-set threshold is a separate `delta^-1` cost.  Composing it gives the actual bounded HH-bad reserve coefficient

```text
eta_HHb <= 2 C_bad / delta.
```

Consequently the Round-40 symbolic optimizer has the concrete bad constant

```text
B = 2 C_bad.
```

For a good-side coefficient `A`, the balanced rational scale is therefore characterized by

```text
A r^3 = 4 C_bad,
delta = r^2.
```

`NSTriadKNHHOneDerivativeThresholdOptimizerRound42Exact` reuses the existing Round-40 global-minimum theorem with precisely this constant.

## 5. Master directional defect: threshold profile and packing reduction

Round 41 already proved on one full classified carrier

```text
D_dir = D_good + D_bad,
delta E_bad <= D_bad <= D_dir,
```

and a finite layer-cake identity.

Round 42 now constructs the rational superlevel classifier directly from the literal physical directional defect

```text
Theta = 1 - (xi.eta)^2
```

and proves the threshold profile is monotone:

```text
s1 <= s2  ==>  M(s2) <= M(s1).
```

It also proves the exact finite reduction needed to test a Carleson/stopping-time route.  If a family of shell-time boxes satisfies one common packing estimate

```text
sum_box D_dir(box) <= P,
```

then automatically

```text
sum_box E_bad(box) <= delta^-1 P
```

and any local good-square bounds of the form

```text
G_box^2 <= C_good delta D_good(box)
```

sum to

```text
sum_box G_box^2 <= C_good delta P.
```

No physical Carleson estimate is asserted.  The new experiment is sharply typed: prove a cutoff-uniform packing theorem for the actual shell-time directional-defect measure, and it feeds both HH strata at once.

## 6. Com: exact equality with the model Gram value was stronger than necessary

Round 41 asked for

```text
physical pair product = pairProduct(sixThreeGramCell(gap)).
```

Round 42 replaces that with the weaker and more physical support-overlap target.  If the literal one-channel product obeys

```text
P(q,r) <= m(q,r) * g(|q-r|),
0 <= m(q,r) <= 1,
```

where `g` is the already-certified six-three two-branch squared gap, then Round 42 constructs an actual Round-35 `GramInterferenceCell` whose `pairProduct` is **the literal physical product** and whose overlap is `g`.

The existing Round-40 single-channel realization and both half-dyadic Cotlar decays then follow.  A Boolean `0/1` support graph is included as the canonical specialization.

Thus the shortest remaining Com theorem is now:

```text
literal U_q^* U_r product
  <= shellSupport(q,r) * sixThreeGap(|q-r|),
```

plus the adjoint-face equality already supplied by the skew-adjoint transport analysis.  No finite singular-value theorem is needed: Round 41 already proved the exact full commutator energy is the one-channel square.

## Revised falsification / implementation order

The highest-information order is now:

1. **HH-bad symbol audit** — prove one genuine derivative factor after all exact cancellations, or falsify the inverse-shell route.
2. **Com support-overlap theorem** — prove the literal `U_q^* U_r` support/product bound and construct the Com owner.
3. **HH-good physical factorization** — identify annular strain samples, select the data-energy amplitude leg, prove the residual quartic `<= X D`, and close the smooth torus correction.
4. Instantiate the six lower-risk owners.
5. Run the exact threshold/Young-aware nine-owner primal/dual reserve test.

Only a certified

```text
sum eta_i < 1
```

should trigger the downstream `CanonicalAnalyticPhysicalLeaves` / maximal-time / global-solution / submission tail.  If the exact dual certificate forces `sum eta_i >= 1`, redesign the architecture rather than continuing downstream.

The attached downstream 28-lemma cutset should then be audited as **new analytic estimates versus same-object/provenance reopenings**.  That classification is deliberately deferred until the reserve gate succeeds, because doing it now would not advance the present mathematical bottleneck.

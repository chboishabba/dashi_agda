# NS Round 40 — unified HH defect measure, shell-localized PV, and one-channel Com

Round 40 tests the strongest concrete post-Round-39 hypotheses before attempting more downstream continuation packaging. The tranche deliberately reuses mature repository mathematics where it already exists: the weighted Markov bad-set estimate, exact directional-defect Gram identity, official hard-projector self-adjointness, the finite weighted Cauchy theorem, and the standard periodized dyadic-kernel L1 authority. The new work is the same-object bridge into the physical Navier--Stokes carriers and the resulting sharper owner geometry.

No unconditional Navier--Stokes regularity theorem is claimed. The physical shell/time owner rates and the final odd-P/Q-to-Gram realization remain explicit fail-closed seams.

## 1. HH-good and HH-bad are complementary strata of one defect

The directional defect is

```text
Theta(xi,eta) = 1 - (xi.eta)^2 = |xi cross eta|^2,
0 <= Theta <= 1.
```

The repository already had the abstract weighted Markov theorem

```text
delta * badWeightMass <= weightedDefectMass.
```

Round 40 instantiates it on actual physical vorticity pairs and physical energy weights. For bad cells,

```text
delta * E_bad <= sum_i E_i Theta_i.
```

The same quantity is exactly the weighted squared cross-residual by the physical directional-defect identity. Thus the good set and bad set are now visibly two uses of one measure:

```text
Theta <= delta     -> HH-good stretching depletion,
Theta >= delta     -> bad occupation controlled by E*Theta.
```

No derivative of the Boolean classifier is introduced.

Round 40 also connects the same defect to the Round-39 same-object bad-gain cells. If the physical gain density satisfies the required local charge estimate, then

```text
delta * Gain_bad
  <= density * nu * lambda_q^2 * sum_i E_i Theta_i.
```

Since `Theta <= 1`, the exact finite theorem further gives

```text
sum_i E_i Theta_i <= sum_i E_i,
```

and therefore

```text
Gain_bad
  <= delta^{-1} * density * D_bad.
```

This proves the inverse-threshold dependence algebraically. The remaining hard HH-bad theorem is the physical shell/time density with the inverse-dyadic gain required by the existing Round-33 obstruction, together with Luo's separate upper critical-dissipation smallness.

Sources: Constantin--Fefferman, DOI `10.1512/iumj.1993.42.42034`; Luo, DOI `10.1007/s00021-019-0411-z`.

## 2. The A sqrt(delta) + B/delta optimizer is exact when the physical scaling has that form

Write the positive rational threshold scale as `r` and represent the physical classifier threshold by

```text
delta = r^2,
delta^{-1} = r^{-2}.
```

Then the proposed HH tax becomes

```text
f(r) = A r + B r^{-2}.
```

Rather than formalize real differentiation or cube roots merely to optimize this one expression, Round 40 proves an exact rational global-minimum certificate. If

```text
A r^3 = 2 B,
```

then for every positive rational `x`,

```text
f(r) <= f(x).
```

The proof uses the exact factorization

```text
2 x^2 (f(x)-f(r))
  = A (x-r)^2 (2x+r) >= 0.
```

At the balanced point,

```text
B r^{-2} = (1/2) A r,
f(r) = (3/2) A r.
```

If the physical constants do not admit an exact rational balanced scale, the more general Round-39 certified threshold optimizer remains the fallback.

## 3. Scale-dependent thresholds are a diagnostic, not an assumption

Round 40 also allows shellwise physical constants `A_q`, `B_q` and shellwise positive scales `r_q`. If

```text
A_q r_q^3 = 2 B_q,
```

then each `r_q` is a global minimizer for its shell. The pointwise theorem is lifted to arbitrary finite shell lists.

If the physical certificates later prove all selected `r_q` are equal, the common global threshold minimizes the whole finite HH tax. Thus scale independence can be recovered as a theorem rather than imposed before the scale laws are known.

## 4. HH-good now has the correct PV -> residual -> shell -> threshold order

A fixed coherence threshold by itself does not regularize the unsmoothed `|x-y|^-3` strain kernel. Round 40 therefore formalizes the order in which the existing cancellations must be consumed.

For zero-mass finite kernel weights,

```text
sum_i w_i = 0
```

implies an arbitrary constant source is killed before residual scalarization:

```text
sum_i w_i (s_i+c) = sum_i w_i s_i.
```

The vorticity-line residual then commutes with the already-cancelled weighted sum:

```text
delta_v(sum_i w_i (s_i+c))
  = sum_i w_i delta_v(s_i).
```

Hence the cross-product residual is preserved through PV cancellation instead of being replaced prematurely by `|w||v|`.

The next finite step is also closed. For nonnegative shell-localized kernel magnitudes `k_i` and good stretching scalars satisfying

```text
s_i^2 <= delta W_i,
```

weighted Cauchy gives

```text
(sum_i k_i s_i)^2
  <= (sum_i k_i)(sum_i k_i s_i^2)
  <= delta (sum_i k_i)(sum_i k_i W_i).
```

The repository already contains the standard periodized dyadic-kernel theorem

```text
||K_q^T||_L1 <= ||check chi||_L1 = C_chi
```

uniformly in `q`. Once the actual strain-shell sample mass is identified with that literal periodized-kernel L1 norm, Round 40 therefore gives

```text
|good shell stretching|^2
  <= C_chi * delta * weightedLocalMass.
```

This is a sharper A3/A4 frontier than absolute integration of the full singular kernel. The remaining same-object/PDE seams are:

```text
physicalShellLocalizedStrainKernelSamples
physicalStrainShellKernelMassIdentification
physicalHHGoodTimeDissipationAbsorption
physicalHHGoodSmoothPeriodicCorrectionBound
```

followed by the already-built Round-39 near/smooth HH-good owner reducer.

Sources: Constantin--Fefferman, DOI `10.1512/iumj.1993.42.42034`; Constantin--E--Titi, DOI `10.1007/BF02099744`; Bahouri--Chemin--Danchin, DOI `10.1007/978-3-642-16830-7`; Luo, DOI `10.1007/s00021-019-0411-z`.

## 5. Com collapses to one cross channel under physical skew adjunction

Round 39 proved

```text
U = PTQ,
V = QTP,
U^2 = V^2 = 0.
```

The official finite hard projector is already self-adjoint in the repository's Hermitian/Parseval development. Round 40 tests the stronger structural property of the actual incompressible transport rather than the optional `J` symmetry.

For a physical Fourier transport matrix entry with

```text
m + q = k,
c(k,q) = i (q . u_m),
```

reality and divergence freedom give

```text
u_-m = conjugate(u_m),
m.u_m = 0,
k.u_m = q.u_m,
```

and Round 40 proves the literal coefficient identity

```text
conjugate(c(q,k)) = - c(k,q).
```

The reverse resonance `-m+k=q` is also proved on the exact integer lattice, and the result is promoted to the actual matrix-entry statement

```text
conjugate T(q,k) = - T(k,q).
```

Thus the physical low transport is pointwise skew-adjoint on the finite Fourier carrier. On the exact P/Q two-channel algebra this implies

```text
V = - U*,
[P,T] = U + U*,
[P,T]^* = [P,T],
[P,T]^2 = diag(UU*, U*U).
```

The two Gram faces are therefore the two sides of one cross-channel operator, not independent physical estimates. Round 40 also proves the audit invariant

```text
Gamma T_odd = - T_odd Gamma,
```

so any diagonal `P->P` or `Q->Q` contribution attributed to `Com` before a later identification is an algebraic red flag.

The remaining A1/A2 seam is now narrowly:

```text
physicalOddPQBlockToRound35Gram
```

or equivalently the single-channel `physicalOddTransportSingleGramRealization`; after that the existing half-dyadic Cotlar estimate should be consumed rather than reproved.

Sources: Kato--Ponce, DOI `10.1002/cpa.3160410704`; Temam, DOI `10.1090/chel/343`; Bahouri--Chemin--Danchin, DOI `10.1007/978-3-642-16830-7`.

## 6. The dual reserve certificate is now also a sensitivity diagnostic

Round 39 proved the exact Farkas no-go theorem. Round 40 decomposes its lower obstruction as

```text
combinedLower = sum_j lambda_j b_j.
```

Each exact rational quantity

```text
pressure_j = lambda_j b_j
```

therefore records that constraint's current contribution to the dual obstruction. Removing or improving a constraint has an exact corresponding change in the certificate lower bound.

This is not claimed to be a derivative of the optimal value. It is an exact sensitivity diagnostic for the current certificate and can guide proof effort before all nine physical owner constants have landed.

Source: Gyula Farkas, *Theorie der einfachen Ungleichungen* (1902), no DOI assigned to the historical article.

## Revised shortest frontier after Round 40

F4 remains closed. The three decisive physical packages have narrowed again:

1. **HH-good / A3-A4:** identify the actual shell-localized strain kernel with the periodized L1 carrier, prove the time/dissipation bound for the resulting weighted local mass, and bound the smooth periodic correction. PV cancellation and the finite shell Cauchy/depletion step are already exact.
2. **HH-bad / A6-A8:** prove the physical gain-density inverse-shell factor required by the Round-33 scaling obstruction and Luo's separate upper critical-dissipation smallness. The bad occupation, defect measure, restricted dissipation and exact `delta^{-1}` owner scaling are already connected on the same samples.
3. **Com / A1-A2:** identify the literal odd P/Q matrix block with the existing Round-35 single Gram channel. Projection self-adjointness and physical transport skew-adjointness no longer need independent assumptions.

Then instantiate the remaining six lower-risk owners and run the joint threshold/primal/dual reserve test. A strict rational primal certificate `sum eta < 1` advances to the existing `CanonicalAnalyticPhysicalLeaves` route; an exact dual certificate forcing `sum eta >= 1` rejects the architecture before downstream continuation work.

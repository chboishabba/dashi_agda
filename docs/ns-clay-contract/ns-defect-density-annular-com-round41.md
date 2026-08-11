# NS Round 41 — defect density, annular master kernel, and one-channel Com

Round 41 continues the shortest post-Round-40 Navier–Stokes cut. It advances
hard finite/same-object mathematics and keeps genuinely physical PDE producers
fail-closed. No unconditional Navier–Stokes regularity theorem is claimed.

## HH-bad: exact inverse-shell source

Round 36 had only the signed scale valuation. Round 41 evaluates the exact
dyadic magnitude with `lambda_q=2^q`, `mu_q=2^-q`:

```text
(L lambda_q) (nu^-1 mu_q^2) R
  = (L nu^-1 R) mu_q,

(L lambda_q) (nu^-1 mu_q^2) (R lambda_q)
  = L nu^-1 R.
```

Exactly one derivative-bearing side of the parabolic inverse supplies the
required inverse shell power. Two derivative-bearing sides are scale-free.
This is now a literal falsification gate rather than a dimensional slogan.

If the physical restricted gain density is the same object as

```text
C_q = (L nu^-1 R) 2^-q
```

and the scale-free coefficient satisfies

```text
0 <= L nu^-1 R <= C_bad,
```

then Round 41 proves

```text
C_q <= C_bad 2^-q
```

and directly constructs Round 39's `InverseShellRestrictedGainDensity`
certificate. The remaining HH-bad work is therefore the physical same-object
factorization/coefficient bound plus Luo's separate localized critical-
dissipation smallness.

## Com: one cross channel controls the full commutator

Round 40 proved `V=-U*`. Round 41 proves on the exact P/Q carrier

```text
||[P,T](x,y)||^2 = b^2 (x^2+y^2),
```

where `b` is the single surviving cross-resolution coefficient. A one-channel
square envelope therefore controls the full commutator energy.

The repository already has the centered `(L6,L3)` six-three Gram cell and its
half-dyadic overlap. The remaining physical Com theorem is narrowed to

```text
literal odd P/Q pair product
  = pairProduct (sixThreeGramCell shellDistance).
```

That one equality constructs Round 40's single-channel Gram realization and
therefore both mature Round-35 Cotlar pair decays.

A Hilbert–Schmidt shortcut is also made falsifiable. Any compulsory per-channel
squared floors sum below `HS^2`, so cutoff-uniform HS control must really
control multiplicity; fixed-cutoff finite rank is not enough.

## One full directional-defect measure owns both HH strata

Round 41 uses a full classified physical carrier, not merely the bad
restriction. Each cell carries one vorticity pair, nonnegative energy, a
`goodRegion` or `badRegion` tag, and evidence for the corresponding threshold
inequality. Define

```text
D_dir      = sum_all  E_i Theta_i,
D_dir_good = sum_good E_i Theta_i,
D_dir_bad  = sum_bad  E_i Theta_i,
E_bad      = sum_bad  E_i.
```

Then exactly

```text
D_dir = D_dir_good + D_dir_bad,
delta E_bad <= D_dir_bad <= D_dir.
```

Consequently one physical estimate

```text
D_dir <= eta D + A + B X
```

controls bad occupation while the good stratum remains an exact component of
the same measure. A finite rational layer-cake theorem also reconstructs
`E Theta` from threshold-slice masses.

## Exact threshold scale diagnostics

For the Round-40 optimizer

```text
f_q(r)=A_q r + B_q r^-2,
A_q r_q^3 = 2 B_q,
```

Round 41 proves:

- if `A_q=w_q A_0` and `B_q=w_q B_0` with the same nonnegative shell factor,
  one balanced base scale works at every shell;
- if `A` is fixed and `B` is divided by eight, the balanced `r` is divided by
  two and `delta=r^2` is divided by four.

Thus scale independence of the physical threshold is a theorem to be derived
from the physical constants, not a standing assumption.

## HH-good annular master-kernel algebra

For the correct matrix-valued annular strain multiplier, Round 41 separates the
remaining same-object theorem into:

```text
literal annular multiplier = literal strain multiplier;
master kernel = its inverse Fourier transform;
K_q(x)=r^3 K(r x);
master kernel is L1;
canonical torus periodization.
```

The exact Jacobian ledger proves `r^3 mass r^-3 = mass`, and finite
periodization proves the torus mass is bounded by the lifted Euclidean mass.
Once the continuum same-object package is inhabited it constructs Round 40's
`PeriodizedAnnularStrainKernelL1Theorem` directly.

## Important falsification: raw `W <= X D` is too low-degree

The continuation proposal suggested testing whether Round 40's
`weightedLocalMass` might obey

```text
W <= C X D
```

with a fixed amplitude-independent constant. Inspecting the literal Round-38
weight shows

```text
W ~ a^2 b^4,
```

which is degree six under common amplitude scaling. The critical energy and
dissipation are quadratic, so `X D` is only degree four. Round 41 instantiates
the repository's exact cubic-versus-quadratic no-go and proves that no fixed
coefficient can make the raw degree-six quantity uniformly bounded by the
degree-four product for arbitrary amplitudes.

The raw shortcut is therefore **rejected**, not assumed.

The scale-compatible repair retains one further quadratic controlled resource,
for example the data-controlled L2 energy `E0`:

```text
W <= E0 X D.
```

This has the correct degree. Given that physical factorization and the already
proved shell estimate

```text
P^2 <= C_strain delta W,
```

Round 41 proves square-root-free Young absorption

```text
P <= epsilon D
     + [ C_strain delta E0 / (4 epsilon) ] X.
```

So HH-good is now narrowed honestly to:

```text
physical annular master-kernel same-object package;
physical strain-shell sample/mass identification;
physical data-weighted local-mass factorization W <= E0 X D
  (or another scale-compatible time/amplitude gain);
smooth torus correction.
```

## Dual pressure as a proof-search instrument

For any finite batch of Round-40 dual-pressure improvements, Round 41 proves

```text
newPressureTotal + savingTotal = oldPressureTotal,
savingTotal >= 0.
```

This gives exact rational sensitivity of the current Farkas obstruction once
provisional physical constants are available. It is not called a derivative
of the optimized reserve.

## Revised shortest physical cut

```text
HH-bad:
  literal bad gain -> one-derivative same-object factorization
  -> scale-free coefficient bound
  -> existing inverse-shell certificate
  + Luo localized critical-dissipation smallness
  -> HH-bad owner

Com:
  literal odd P/Q product
  -> equality to existing six-three Gram product
  -> existing single-channel/two-face Cotlar machinery
  -> Com owner

HH-good:
  literal annular strain master-kernel identification
  -> physical shell-kernel sample/mass identification
  -> scale-compatible W <= E0 X D (or equivalent physical gain)
  -> square-root-free Young owner
  + smooth torus remainder
  -> HH-good owner
```

Only after these three physical owners exist should the six lower-risk owners
be instantiated and the threshold-aware nine-owner primal/dual reserve test be
run. A certified `sum eta < 1` advances to the prepared canonical physical
leaves and maximal-time tail. An exact Farkas certificate forcing
`sum eta >= 1` is an architecture failure and should trigger redesign rather
than further tuning.

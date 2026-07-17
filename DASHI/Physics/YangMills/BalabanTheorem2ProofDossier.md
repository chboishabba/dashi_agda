# Balaban Theorem 2: finite-lattice beta trajectory dossier

## Status

This is a research dossier, not a theorem import and not an Agda producer.
It records the smallest missing analytic result behind the existing
fail-closed `BalabanRenormalisedCouplingConstruction` interface.  In
particular, it does **not** certify a Yang--Mills continuum limit or a Clay
solution.

The source scope is Balaban, *Renormalization Group Approach to Lattice Field
Theories I* (CMP 109, 1987), Theorem 2: four dimensions and `G = SU(2)`.

## Exact source target

Let `epsilon = L^-K`.  CMP 109 Theorem 2 (p. 259, equation (0.31)) states
that, for sufficiently small terminal coupling `g > 0`, there is a tuned bare
coupling `g₀(epsilon , g)` such that

```text
g_K = g,
0 < g_k ≤ gamma  for 0 ≤ k ≤ K,

1/g² + beta  log((L^k epsilon)^-1)
  ≤ 1/g_k²
  ≤ 1/g² + beta' log((L^k epsilon)^-1),
```

for positive source constants `beta ≤ beta'`.  The paper immediately says
that a proof is to be given separately and based on perturbative
calculations.  The proof is not supplied by CMP 109 or CMP 116.

With `u_k = 1/g_k²` and `epsilon = L^-K`, this is the linear tube

```text
u_R + beta  (K - k) log L ≤ u_k ≤ u_R + beta' (K - k) log L,
```

where `u_R = 1/g²` and `u_K = u_R`.

## What CMP 109 already supplies

CMP 109 defines the scale beta coefficient through the fluctuation effective
action and its vacuum-polarization tensor.  Equation (1.22), analysed again
in Section 5, gives for `mu != nu`:

```text
beta_j = - ∂_{p_mu} ∂_{p_nu} Pi^(j)_{mu nu}(0)
       =   sum_x Pi^(j)_{mu nu}(x) x_mu x_nu.                 (5.42)
```

The same section proves the transverse decomposition

```text
Pi_{mu nu}(p)
  = beta (delta_{mu nu} Delta(p) - dbar_mu(p) d_nu(p))
    + Pi'_{mu nu}(p),                                        (5.37)
```

and writes `Pi'` as third and higher lattice-derivative terms with analytic,
exponentially decaying kernels; see (5.38), (5.43), and (5.44).  This is a
coefficient identity and an irrelevant-remainder structure.  It is not a
uniform positive numerical bound for the coefficient.

CMP 109 also explicitly warns after (5.42) that the notation
`beta_j(g_{j-1})` suppresses dependence on all preceding couplings.  Any
proof must therefore control a history-dependent law

```text
B_{K,j}(u_0, ..., u_{j-1}),
```

not assume an autonomous scalar beta function.

## Normalization audit: the first calculation is now pinned

CMP 109 gives the required finite-lattice fluctuation normalization; it is
not safe to guess it from the continuum Wilson action.

* Before fluctuation rescaling, the transformed integral contains the
  gauge-fixing/action/quadratic terms with explicit `g_k^-2` factors; see
  (2.10), p. 267.
* Balaban then makes the explicit change of variables `B = g_k B'` on the
  same page.  The remaining variables carry a Gaussian measure with covariance
  `C^(k) = (C* A^(k) C)^-1` (p. 268), while the new effective interaction is
  defined by the Gaussian fluctuation integral (2.13).
* The coupling update is unambiguous:

  ```text
  1/g_k² = 1/g_{k+1}² + beta_{k+1}(g_k).                     (2.15)
  ```

  Equivalently, `u_{k+1} = u_k - beta_{k+1}`.  This is the
  convention used by the existing inverse-square Agda carrier.

Consequently, the candidate computation starts with the second variation of
the particular Gaussian integral (2.13), after this rescaling and its
constraint/gauge-fixing transformations.  It may not insert a continuum
one-loop coefficient or assume a residual `g_k^-2` Gaussian covariance.

The exact linear covariance and background-dependent operators invoked here
come from CMP 109 references [10], [13], [14], and [15] (Balaban's 1984--85
propagator, regular-configuration, and variational-background papers).  Those
papers are available in the local source packet.  Only the definitions used by
the constrained determinant should now be extracted; another broad source
ledger is not required.

## Source decomposition of the beta coefficient

Equations (1.3) and (1.6) make a distinction which is easy to lose in a
continuum perturbation slogan.  In (1.3), the contribution from RG step `j` is
written as the sum of

```text
log Z^(j)(U) - log Z^(j)(1)

and

E^(j+1)(g_j , U) - E^(j+1)(g_j , 1).
```

Equation (1.6) absorbs these two terms into a single bold-face effective
interaction.  Equations (1.20)--(1.22) define the polarization tensor and
`beta_(j+1)` from the second background variation of that **merged** term.
Consequently the exact coefficient has the source-native split

```text
beta_(j+1)(g-history)
  = betaZ_(j+1) + betaInt_(j+1)(g-history),
```

where `betaZ` is obtained from `log Z^(j)` and `betaInt` from the nonlinear
fluctuation interaction (2.13).

The Gaussian normalization is explicit in (1.4):

```text
Z^(j)(U) = integral dB delta(Q B)
             exp[-(1/2) <B , Delta^(j)(U) B>].
```

After the constrained variables are eliminated in Section 2, its covariance
is `(C* A^(k) C)^-1`.  This is the determinant to calculate.  A naive
flat-background lattice Laplacian is not an admissible replacement: the
constraint coordinates, the background-dependent quadratic form, and any
coordinate normalization retained by Balaban are part of `Z^(j)`.

The text following (2.13) states that the expression under that nonlinear
fluctuation integral vanishes at `g_k = 0`.  Subject to the uniform twice-
background-differentiable estimate needed to interchange this limit with
(1.20), this gives the precise perturbative candidate

```text
betaLead_(j+1) = betaZ_(j+1),
remainder_(j+1)(g-history) = betaInt_(j+1)(g-history),
remainder_(j+1)(0-history) = 0.
```

This is a smaller problem than expanding every term in (2.12) at leading
order.  The Jacobian `Tr log(I - h delta D-tilde/delta B)`, nonlinear measure
factor `log sigma`, gauge-fixing remainder `G_3`, nonlinear action `V`, and
the preceding-interaction difference all occur inside `P^(k)+{...}` in
(2.13).  They must be controlled for the remainder and its history
derivatives, but they are not to be silently added to the order-zero
coefficient if the stated vanishing and differentiation interchange are
proved.

This also explains why a generic statement that "`Tr log H` is not the whole
coefficient" is simultaneously true and too coarse:

* it is not the whole finite-`g` coefficient;
* the exact constrained Gaussian normalization is nevertheless the
  source-designated candidate for the complete `g = 0` leading term.

The first falsifiable analytic lemma is therefore

```text
betaInt_(j+1)(g-history) = O(g_j^rho)
```

for the source-derived positive power `rho`, uniformly in cutoff, scale,
volume, regular background, and admissible history.  The value of `rho` must
come from (2.12)--(2.13); it is not fixed here by perturbative folklore.

## Leading determinant calculation: exact work packet

The order-zero calculation now has four bounded stages.

1. **Constrained determinant reduction and interscale match.**  The finite
   Gaussian identity on CMP 109's exact constrained carrier is now closed
   directly from (1.4): it combines the local `S` determinant and
   `C_kerQ^* Delta C_kerQ` determinant into one Schur-complement expression.
   What remains is to identify the resulting augmented coarse operator with
   the next augmented `Delta`, up to a background-independent scale/basis
   conjugation.  Keep the explicit `S/C` derivative route only as a fallback
   audit.
2. **Endpoint background Hessian.**  Telescope the Gaussian normalizations
   over the requested prefix and differentiate the two endpoint trace-logs
   twice at the identity background.  In ordinary finite-dimensional notation
   the diagnostic shape is

   ```text
   D^2 log det DeltaHat [u,v]
     = Tr(DeltaHat^-1 D^2 DeltaHat[u,v])
       - Tr(DeltaHat^-1 DDeltaHat[u]
            DeltaHat^-1 DDeltaHat[v]),
   ```

   with the sign and factor inherited from the Gaussian integral.  This is a
   checksum after the interscale operator match has been fixed.
3. **Polarization projection.**  Fourier transform the endpoint bond kernel,
   prove the lattice Ward/transversality identity in the same convention, and
   apply the minus off-diagonal second derivative in (1.22)/(5.42).
4. **Cumulative enclosure.**  Evaluate or rigorously enclose the endpoint
   difference uniformly in cutoff, prefix endpoint, and torus.  Only after
   this step compare its slope with the universal continuum checksum,
   conventionally expected to be proportional to `2 b0 log L` per inverse-
   square RG step.

The shortest required output is the explicit prefix inequality

```text
betaZLower (m-k)
  <= sum_(j=k+1)^m betaZ_j
  <= betaZUpper (m-k)
```

for all finite prefixes, with `betaZLower > 0` and no appeal to universality
inside the proof.  A pointwise shell enclosure remains sufficient but is not
required.  Universality can detect a normalization error; it cannot provide
this finite-prefix bound.

CMP 109 itself points to reference [16], Balaban's CMP 102 (1985), 255--275
paper on three-dimensional lattice pure gauge theory, for an expansion of
`log Z^(j-1)(U_j)` compatible with the localized representation (1.7).  That
source shortcut is now available locally.  Its localization formula is
reusable, but its three-dimensional coefficient and power counting are not
evidence for the four-dimensional positive enclosure.

### What CMP 102 (1985), 255--275 actually contributes

The local copy `/home/c/Downloads/balaban1985a.pdf` contains the needed
structural reduction.  Around equations (61)--(63), the constrained delta
functions are eliminated with the same independent-coordinate map `C`.  Two
types of terms result:

```text
1. local constraint-coordinate terms
     - sum_c log det S(V^(k), b_0(c));

2. the constrained Gaussian determinant
     (1/2) log det(C* A_k C)^-1
       = -(1/2) Tr log(C* A_k C).
```

The paper then represents the trace logarithm by a contour/resolvent formula
and expands both the resolvent and `(C* A_k C)^-1` into generalized random
walks.  This proves that the determinant difference has a gauge-invariant,
localized expansion with exponential decay.

This materially sharpens the leading carrier.  `betaZ` is not just the trace
log of `C* A_k C`; it also includes the local `log det S` terms created when
the constrained variables are eliminated.  The calculation must project the
background Hessian of their sum through (1.22).  The reusable source identity
is therefore

```text
log Z^(j)(U) - log Z^(j)(1)
  = localConstraintJacobian_j(U)
    + constrainedTraceLog_j(U)
    + localized normalization constants which cancel at U = 1.
```

The three-dimensional paper supplies the algebraic and localization method,
not the four-dimensional sign.  The new four-dimensional work is now bounded
to evaluating the background Hessian of these two explicit pieces and proving
uniformity of their localized/resolvent tails.

The prerequisite formulas are now located, rather than merely bibliographic:

| Needed object | Literal source location | Role in the calculation |
| --- | --- | --- |
| linearized averaging coefficient `S(V,b_0(c))` | CMP 98, equation (124) and Proposition 3 | local constraint-Jacobian Hessian |
| background quadratic operator | CMP 99, equations (3.10), (3.118)--(3.120), and (3.156) | constrained Gaussian Hessian |
| constrained covariance | CMP 99, equations (3.183)--(3.187) | trace-log resolvent and decay |
| free multiscale Fourier symbols | CMP 95, equations (1.29)--(1.65), especially (1.60)--(1.63) | identity-background momentum evaluator |
| determinant localization | CMP 102 (1985), 255--275, equations (61)--(63) | local plus trace-log decomposition |

The next calculation should specialize these formulas at the identity
background, take two background variations, and only then implement a finite
momentum evaluator.  No additional source family is needed.

### Notation: two distinct `C` maps

Two different objects denoted `C` appear in the source packet and must not
be conflated.

* `C_nl(A')`: the **nonlinear remainder** in the constraint/averaging map.
  CMP 102 equation (15) writes `Q(A') = Q-bar A' + C_nl(A')`, where `C_nl`
  begins at second order in the fluctuation field `A'`.  Its derivatives
  generate interaction and Jacobian terms through the linearizing
  transformation.

* `C_kerQ(B)`: the **embedding of independent fluctuation coordinates**
  into `ker Q(B)`.  CMP 99, after (3.156), constructs this map by solving
  `(Q(B) x)(c) = 0` for the distinguished bond `b_0(c)`.  The constrained
  Gaussian determinant is `det(C_kerQ(B)^* A_j(B) C_kerQ(B))`.

The constrained trace-log Hessian in the following worksheet uses `C`
exclusively in the sense of `C_kerQ`.  The nonlinear `C_nl` enters only
through the interaction remainder `betaInt` and the linearization Jacobian.
The Schur-complement telescoping shortcut, if verified, eliminates
`C_kerQ` and its derivatives from the critical path entirely; `C_nl` remains
relevant only to the nonlinear remainder bound.

### Constrained-coordinate derivative worksheet

The source packet now fixes the first finite-dimensional reduction more
precisely.  CMP 98 equation (124) is the literal linear map

```text
(Q(V) A)(c) = sum_{b in B(c)} S_b(V,c) A(b).
```

Here `S_b(V,c)` denotes coefficient extraction from the right-hand side of
(124), and `S(V,b_0(c))` in CMP 102 is the distinguished coefficient
`S_0(V,c)`.  CMP 99, immediately after (3.156), says that `B(c) intersect c`
contains exactly one bond `b_0(c)` and that the constrained coordinate map
`C(V)` is obtained by solving `(Q(V)B)(c) = 0` for that bond.  Thus, for every
independent bond `b != b_0(c)`, the dependent coordinate is

```text
(C(V) B)(b_0(c))
  = sum_{b != b_0(c)} K_b(V,c) B(b),

K_b(V,c) = - S_0(V,c)^-1 S_b(V,c).
```

This makes the background dependence of `C` algebraic once the derivatives
of the coefficient maps in (124) are known.  Put `R_0 = S_0^-1`.  For two
background directions `u,v`, ordinary finite-dimensional differentiation
gives

```text
D R_0[u] = - R_0 (D S_0[u]) R_0,

D^2 R_0[u,v]
  = R_0 (D S_0[v]) R_0 (D S_0[u]) R_0
  + R_0 (D S_0[u]) R_0 (D S_0[v]) R_0
  - R_0 (D^2 S_0[u,v]) R_0,

D K_b[u]
  = R_0 (D S_0[u]) R_0 S_b - R_0 D S_b[u],

D^2 K_b[u,v]
  = - R_0 (D S_0[v]) R_0 (D S_0[u]) R_0 S_b
    - R_0 (D S_0[u]) R_0 (D S_0[v]) R_0 S_b
    + R_0 (D^2 S_0[u,v]) R_0 S_b
    + R_0 (D S_0[u]) R_0 D S_b[v]
    + R_0 (D S_0[v]) R_0 D S_b[u]
    - R_0 D^2 S_b[u,v].
```

These formulas determine `D C` and `D^2 C` componentwise.  No separate
background derivative theorem for `C` is needed.

At the identity background all path transports in CMP 98 (124) are the
identity, `y = y_x = 0`, and all correction brackets in (124) vanish.  Hence
`Q(1) = Q_0`, with `Q_0` given by (125).  In particular `S_0(1,c)` is a
nonzero scalar multiple of the identity Lie-algebra map, so the inverse used
above exists at the expansion point.  The exact scalar is to be read from the
coefficient of the unique distinguished bond in (125); it must not be guessed
from the overall `L^-(d+1)` factor before the path-incidence multiplicity is
checked.

The analytic functions in (124) are also normalized explicitly in CMP 98
(33)--(35):

```text
g(z)       = (exp(-z) - 1)/(-z)
           = 1 - z/2 + z^2/6 + ...,

g(z)^-1   = 1 + z/2 + z^2/12 + ...,

R(exp(iY)) = exp(i ad_Y).
```

Therefore the coefficient derivatives `D S_b` and `D^2 S_b` are a finite
calculation from (124), using

```text
D g(0)[X]             = - X/2,
D^2 g(0)[X,Y]         = (XY + YX)/6,
D g^-1(0)[X]          =   X/2,
D^2 g^-1(0)[X,Y]      = (XY + YX)/12,

D exp(i ad_Y)|_0[X]   = i ad_X,
D^2 exp(i ad_Y)|_0[X,Y]
  = -(ad_X ad_Y + ad_Y ad_X)/2.
```

The remaining source transcription on this branch is now exact and finite:
differentiate every coefficient of (124), retaining the derivatives of the
path transports `R_{0,c_-}`, `R_{0,c}`, and of `y,y_x`.  Until that expansion
is written out, `D S_b` and `D^2 S_b` are not available for numerical use.

### Constrained trace-log Hessian

Set

```text
M_j(B) = C(B)^* A_j(B) C(B),
G_j    = M_j(0)^-1.
```

For a background direction `u`, the complete first variation is

```text
D M_j[u]
  = D C[u]^* A_j C
    + C^* D A_j[u] C
    + C^* A_j D C[u].
```

For two directions `u,v`, the complete mixed variation is

```text
D^2 M_j[u,v]
  = D^2 C[u,v]^* A_j C
    + D C[u]^* D A_j[v] C
    + D C[u]^* A_j D C[v]
    + D C[v]^* D A_j[u] C
    + C^* D^2 A_j[u,v] C
    + C^* D A_j[u] D C[v]
    + D C[v]^* A_j D C[u]
    + C^* D A_j[v] D C[u]
    + C^* A_j D^2 C[u,v].
```

All unlabelled factors on the right are evaluated at the identity background.
Consequently the trace-log contribution to the background Hessian is exactly

```text
-1/2 Tr(
    G_j D^2 M_j[u,v]
  - G_j D M_j[u] G_j D M_j[v]).
```

The local constraint determinant has the parallel formula

```text
- tr(
    S_0^-1 D^2 S_0[u,v]
  - S_0^-1 D S_0[u] S_0^-1 D S_0[v]).
```

These two formulas must be summed before applying the Ward projection; neither
summand is required to be transverse or positive separately.

### Identity-background quadratic operator and Fourier seed

CMP 99 (3.10) gives the exact background quadratic operator

```text
A_j(U) = D_U^* D_U + A'_j(U),
```

where the quadratic form of `A'_j(U)` is the sum of a term proportional to
`Re U(partial p) - 1` and a commutator term proportional to
`Im U(partial p)`.  Hence

```text
A_j(1) = d^* d,
```

while `D A_j` and `D^2 A_j` are obtained by differentiating both the covariant
derivatives and the two plaquette-holonomy coefficients in (3.10).  CMP 99
(3.1)--(3.7) gives the required finite plaquette expansion, so no continuum
vertex may be substituted here.

These derivatives can already be written without graph notation.  Parameterize
the background links by `U_B(b) = exp(i B(b))`.  For a site field `f`, CMP 99
(3.3) gives

```text
(D_B f)(b)
  = eta^-1 (R(U_B(b)) f(b_+) - f(b_-)).
```

At `B = 0`, writing `deltaD[u] = D(D_B)|_0[u]` and similarly for the mixed
second variation,

```text
(deltaD[u] f)(b)
  = eta^-1 i ad_(u(b)) f(b_+),

(delta2D[u,v] f)(b)
  = - eta^-1/2
      (ad_(u(b)) ad_(v(b)) + ad_(v(b)) ad_(u(b))) f(b_+).
```

Consequently the covariant-Laplacian part of (3.10) has the exact variations

```text
D(D_B^* D_B)|_0[u]
  = deltaD[u]^* d + d^* deltaD[u],

D^2(D_B^* D_B)|_0[u,v]
  = delta2D[u,v]^* d + d^* delta2D[u,v]
    + deltaD[u]^* deltaD[v]
    + deltaD[v]^* deltaD[u].
```

For an oriented plaquette `p` with ordered boundary bonds `b_1,...,b_4`, put
`sigma_r = +/-1` according to orientation and

```text
P_p(B) = product_(r=1)^4 exp(i sigma_r B(b_r)).
```

Then its first and mixed second variations are the finite expressions

```text
D P_p(0)[u]
  = i sum_r sigma_r u(b_r),

D^2 P_p(0)[u,v]
  = -1/2 sum_r
      (u(b_r)v(b_r) + v(b_r)u(b_r))
    - sum_(r<s) sigma_r sigma_s
      (u(b_r)v(b_s) + v(b_r)u(b_s)).
```

Reversing a bond is understood to replace its field by its negative, as in
CMP 99 (3.5).  Taking the source definitions
`Re P = (P + P^-1)/2` and `Im P = (P - P^-1)/(2i)` now gives finite formulas
for

```text
D Im P_p(0),
D^2 Re P_p(0),
D^2 Im P_p(0).
```

In particular `D Re P_p(0) = 0`.  Therefore the first variation of the
`A'_j` quadratic form in (3.10) comes only from the commutator term multiplied
by `D Im P_p(0)`.  Its second variation has exactly three source-visible
classes:

```text
1. D^2 Re P_p(0) times the identity-background (d A)(p)^2 term;
2. D Im P_p(0) times one variation of a transported A'(b_r);
3. D^2 Im P_p(0) times the identity-background commutator term.
```

The variation of each transported `A'(b_r)` is again finite: at the identity,
a transport by a prefix path `gamma` has first variation

```text
i ad_(sum_(b in gamma) sigma_b u(b)) A(b_r),
```

and its mixed second variation follows from the same ordered-product formula
above.  Combining these terms with the covariant-Laplacian formulas gives the
literal `D A_j` and `D^2 A_j` kernels.  What remains is index expansion and
Fourier transformation, not an unspecified functional derivative.

CMP 95 fixes the free Fourier convention and the elementary symbols:

```text
d_mu(p) = (exp(i eta p_mu) - 1)/eta,
Delta(p) = sum_mu |d_mu(p)|^2,

u_k(p) = product_mu
  ((exp(i p_mu) - 1) / (exp(i eta p_mu) - 1))
       = product_mu d_mu^(1)(p) / d_mu(p).              (1.31)
```

Equations (1.60)--(1.63) then give the complete identity-background symbol of
the constrained minimizer `H_k`; equation (1.62) defines

```text
phi_mu(p') = sum_l
  |u_k(p' + l)|^2 |d_mu(p' + l)|^2 / Delta(p' + l).
```

Those formulas are the seed for a finite momentum evaluator.  They do not yet
give the desired determinant Hessian: the evaluator still needs the explicit
Fourier kernels of `D S`, `D^2 S`, `D A_j`, and `D^2 A_j` from the preceding
finite path/plaquette differentiations.

This closes the abstract operator calculus.  The first remaining paper
calculation is now the literal expansion of CMP 98 (124) and CMP 99 (3.10) at
the identity background into those four finite Fourier kernels.

### Coordinate-free determinant reduction

There is a shorter representation which should be used if the finite
gauge-fixed ambient quadratic operator is invertible.  Let `A` be a positive
invertible operator on the finite real fluctuation carrier and let
`Q : X -> Y` be a surjective linear constraint.  Direct finite-dimensional
Gaussian integration gives

```text
integral_X dx delta(Qx) exp[-1/2 <x,A x>]
  = (2 pi)^((dim X - dim Y)/2)
      det(A)^-1/2 det(Q A^-1 Q^*)^-1/2.                 (* )
```

If one instead solves the constraint for the distinguished coordinates using
`S_0` and writes `x = C x_bar`, the same integral is

```text
|det S_0|^-1 det(C^* A C)^-1/2
```

times the same background-independent Gaussian constant.  Hence

```text
det(S_0)^2 det(C^* A C)
  = det(A) det(Q A^-1 Q^*)
```

with the determinant conventions induced by the chosen oriented real bases.
This identity explains why CMP 102 obtains the local `log det S` and
constrained trace-log together: they are the coordinate-elimination form of a
single constrained Gaussian determinant.

The literal CMP 109 definition (1.4) makes this reduction exact for the
Gaussian normalization appearing in the inductive action:

```text
Z^(j)(U_k)
  = integral dB delta(Q-bar_j(U_k) B)
      exp[-1/2 <B, Delta^(j)(U_k) B>].
```

This displayed `Z^(j)` is already a constrained Lebesgue Gaussian.  The
Haar-density ratio, the Jacobian of the nonlinear linearization, and the
higher terms generated by `C_nl(B)` occur in the interaction integrated in
(2.10)--(2.13); they are not hidden factors in (1.4).  CMP 102 equations
(61)--(63) give the coordinate-elimination version of this same Gaussian
identity: the local `det S` factors and the
`det(C_kerQ^* Delta C_kerQ)` factor are two coordinate pieces of the one
constrained determinant.

Applied to the literal background-dependent operators in (1.4), put

```text
G_j(B) = Delta_j(B)^-1,
N_j(B) = Q-bar_j(B) G_j(B) Q-bar_j(B)^*,
S_j(B) = N_j(B)^-1.
```

Here `Delta_j` is the complete positive quadratic operator on the finite
gauge-fixed carrier used by (1.4).  It must not be silently replaced by the
Wilson-action Hessian or by the unit-lattice covariance inverse `A^(k)`.
Direct Gaussian integration proves, modulo a background-independent
dimensional constant,

```text
GammaZ_j(B)
  = -1/2 Tr log Delta_j(B) - 1/2 tr log N_j(B)
  = -1/2 Tr log Delta_j(B) + 1/2 tr log S_j(B).          (**)
```

When positivity is obtained by adding an auxiliary penalty
`a Q-bar_j^* Q-bar_j`, write the resulting ambient operator as
`DeltaHat_j`.  The penalty vanishes on the support of `delta(Q-bar_j B)`, so
it does not change `Z^(j)`, but the determinant formula may be evaluated with
`DeltaHat_j`.  CMP 95 (1.68)--(1.71) and CMP 99 (3.122) use exactly this
device.  In that convention

```text
S_j = (Q-bar_j DeltaHat_j^-1 Q-bar_j^*)^-1
```

is the **augmented** coarse operator; the physical minimized Hessian is
`S_j - a I`.  Any interscale telescope must therefore match augmented
operators with the same penalty convention, rather than identify the raw
physical Hessian with `S_j`.

This representation eliminates `S`, `C`, and all their derivatives from the
combined Gaussian calculation.  It does **not** eliminate the background
dependence of the complete linearized averaging map `Q-bar_j`, whose first
and second variations still come from CMP 98 (124).

The derivatives needed by (**) are finite algebra.  At the identity
background, with `G = Delta^-1`,

```text
D G[u] = - G D Delta[u] G,

D^2 G[u,v]
  = G D Delta[v] G D Delta[u] G
    + G D Delta[u] G D Delta[v] G
    - G D^2 Delta[u,v] G.
```

For `N = Q-bar G Q-bar^*`,

```text
D N[u]
  = D Q[u] G Q^*
    + Q D G[u] Q^*
    + Q G D Q[u]^*,

D^2 N[u,v]
  = D^2 Q[u,v] G Q^*
    + D Q[u] D G[v] Q^*
    + D Q[u] G D Q[v]^*
    + D Q[v] D G[u] Q^*
    + Q D^2 G[u,v] Q^*
    + Q D G[u] D Q[v]^*
    + D Q[v] G D Q[u]^*
    + Q D G[v] D Q[u]^*
    + Q G D^2 Q[u,v]^*.
```

Writing `R = N^-1`, the complete constrained-Gaussian background Hessian is

```text
-1/2 Tr(G D^2 Delta[u,v] - G D Delta[u] G D Delta[v])
-1/2 tr(R D^2 N[u,v] - R D N[u] R D N[v]).              (***)
```

The local determinant and `C^* Delta C` Hessians written above are a useful
check on (***), but need not be evaluated separately if (*) is established on
the exact source carrier.

The gauge-carrier qualification is part of the literal meaning of (1.4): the
inverse and determinants above are taken only on the finite carrier on which
`Delta^(j)` defines the Gaussian after Bałaban's gauge fixing.  No unrestricted
inverse of `D^*D` may be introduced.  The one-scale constrained-determinant
reduction is therefore closed.  Subject to a separate cross-scale
identification, the explicit kernels needed by the leading calculation reduce
to

```text
D Q-bar_j,  D^2 Q-bar_j,  D Delta_j,  D^2 Delta_j.
```

### Rejected adjacent Schur-complement telescope

The coordinate-free formula has a further exact simplification **if** the
next source quadratic operator is the constrained minimum of the current one,
as in the free calculation of CMP 95.  Define the Schur complement of a
positive augmented representative of the literal (1.4) data by

```text
S_j(B)
  = (Q-bar_j(B) DeltaHat_j(B)^-1 Q-bar_j(B)^*)^-1.
```

For a general positive operator `A` and constraint `Q`, the corresponding
minimum has, for

```text
H_j = A_j^-1 Q_j^* (Q_j A_j^-1 Q_j^*)^-1,
```

one has `Q_j H_j = I`, and the minimized coarse quadratic form is

```text
A_(j+1) = H_j^* A_j H_j
        = (Q_j A_j^-1 Q_j^*)^-1.
```

This is the finite-dimensional Schur-complement identity behind CMP 95
(1.60), (1.64), and (1.65).  CMP 99 (3.122) displays the auxiliary-penalty
correction explicitly:

```text
physicalCoarseHessian_j = S_j - a I.
```

Thus `S_j` is the augmented coarse quadratic form induced by `DeltaHat_j`.
This is also a normalization warning.  At the next integration the positive
ambient representative is naturally obtained by adding the *next constraint*
penalty,

```text
DeltaHat_(j+1) = physicalCoarseHessian_j + a Q_(j+1)* Q_(j+1),
```

not by adding `a I`.  Consequently `S_j` is not automatically the same
operator as the next augmented Gaussian operator.  It does **not by itself**
prove the source identification

```text
S_j(U_j) = DeltaHat_(j+1)(U_(j+1))
```

with the background lift, gauge carrier, and modified quadratic terms of CMP
109.  The source augmentation convention below shows that this identification
is not the next-Gaussian identity, so the following endpoint formula is a
rejected candidate rather than a usable consequence:

```text
log Z_j(B)
  = -1/2 Tr log DeltaHat_j(B)
    + 1/2 Tr log DeltaHat_(j+1)(B_coarse)
    + background-independent constant.                         (****)
```

Thus the combined local `log det S` and constrained
`C_kerQ^* Delta_j C_kerQ` terms **do** form the one-scale constrained
determinant (**).  The attempted adjacent telescope, however, has an
additional penalty-normalization seam: it must compare `S_j` with the
correct next constrained determinant, not simply rename `S_j` as
`DeltaHat_(j+1)`.  The preferred critical path is therefore a cumulative
block-determinant factorization of the nested constraints; it must retain the
penalty factors explicitly.  Neither `D S` nor `D C_kerQ` needs to be
evaluated separately only after that cumulative identity has been derived.
Accordingly the following adjacent-shell polarization formula is **not**
available from the one-step determinant identity:

```text
D^2 log Z_j
  = 1/2 D^2 Tr log DeltaHat_(j+1)
    - 1/2 D^2 Tr log DeltaHat_j,
```

where the two background variations are related by Bałaban's exact
fine/coarse background map.

Nor do the displayed determinants telescope across several Gaussian steps
without a separate cumulative block-determinant factorization:

```text
sum_(j=0)^(K-1) log Z_j
  = 1/2 Tr log DeltaHat_K - 1/2 Tr log DeltaHat_0
    + sum_j background-independent constants.
```

After the vacuum subtraction, the constants disappear.  This makes the
leading beta coefficient a shell difference of the standard background-field
one-loop determinant.  Dashen--Gross is therefore potentially useful at the
level of this **combined** determinant, rather than as a replacement for one
of Bałaban's coordinate terms.

The rejected shortcut would have required the following false identification:

1. the augmented `DeltaHat_(j+1)` occurring in the next normalization must be
   exactly the Schur complement `S_j` of `DeltaHat_j` and `Q-bar_j` used in
   (1.4), including the background map, rescaling, gauge carrier, auxiliary
   penalty, and the modified quadratic terms in (1.5).

Telescoping controls the sum of shell coefficients rather than each shell
separately.  This is not a defect for the shortest proof: the existing
`BalabanBetaPrefixBound` consumer and the bilateral logarithmic inequalities
in Theorem 2 are both cumulative statements.  A pointwise positive shell
bound is stronger than the canonical route requires.

The free/minimization analogue of this check is present in the source.  CMP 99
(3.122)--(3.126) introduces the positive gauge-fixed operator `G^-1`, solves
the constrained minimum, and proves

```text
H = G Q^* (Q G Q^*)^-1.
```

The modified quadratic form actually used after linearizing the nonlinear
average has the same representation in (3.127)--(3.129), with `G_1` in place
of `G`.  After subtracting the auxiliary coarse penalty displayed in (3.122),

```text
physicalCoarseHessian = H^* G^-1 H - a I
                      = (Q G Q^*)^-1 - a I
```

is the induced physical quadratic form.  What remains is to match the
augmented form `(Q G Q^*)^-1` to the literal augmented representative of
`Delta^(j+1)` used by CMP 109.  No cancellation of
Faddeev--Popov or nonlinear-linearization Jacobians inside `Z^(j)` is required:
CMP 109 (1.4) shows that those terms are outside the displayed Gaussian
normalization and belong to the interaction lane.

The appearance of the modified form in CMP 99 (3.127)--(3.129) is not an
accident.  It is the finite-dimensional constrained-envelope Hessian.  Let
`S(x)` be the fine action, `q(x) = y` the nonlinear coarse constraint,
`h(y)` its minimizing background, and `lambda(y)` the Lagrange multiplier:

```text
D S(h(y)) - D q(h(y))^* lambda(y) = 0,
q(h(y)) = y.
```

Put `Q = D q(h(y))` and let `L` be the Hessian of the constrained
Lagrangian,

```text
L = D^2 S(h(y)) - <lambda(y), D^2 q(h(y))>.
```

Differentiating stationarity and the constraint gives

```text
L D h = Q^* D lambda,
Q D h = I.
```

Hence

```text
D h = L^-1 Q^* (Q L^-1 Q^*)^-1,
D lambda = (Q L^-1 Q^*)^-1,
D^2 (S o h) = (Q L^-1 Q^*)^-1.
```

The `C^(2)`/`J` term in CMP 99 (3.127)--(3.128) is precisely the
constraint-curvature contribution to `L`; omitting it would give the wrong
coarse Hessian.  The `DRD^*` gauge extension and `a Q^*Q` penalty are devices
used to invert the ambient operator.  Equations (3.124)--(3.126) remove the
gauge-extension contribution from the constrained minimizer, while (3.122)
records the remaining `-a I` correction.  Thus the **operator algebra** of the
interscale identification is closed.  The unresolved source match is now only
whether the scaled/background-pulled operator denoted `Delta^(j+1)` in CMP 109
is definitionally this constrained-envelope Hessian with the same augmentation
and determinant convention.

CMP 95 (1.16)--(1.17) identifies a composition of Gaussian RG transformations
with the single iterated constraint `Q_k`, while (1.64)--(1.65) identifies the
resulting coarse quadratic action with the constrained minimum.  CMP 98
(127), (134) gives the corresponding composition of the nonlinear averaging
maps and their linear parts.  These facts support a **cumulative**
block-determinant calculation.  They do not make it enough to prove

```text
S_j(U_j)
  = R_j^* DeltaHat_(j+1)(U_(j+1)) R_j
```

for a background-independent scale/basis isomorphism `R_j`: the `a I` versus
`a Q_(j+1)^*Q_(j+1)` mismatch remains even when `R_j = I`.

The shortest leading-coefficient route is therefore:

```text
simultaneous nested-constraint determinant
  -> sequential block-determinant factorization with explicit penalties
  -> endpoint background determinant difference plus explicit correction
  -> Ward/transverse projection
  -> cumulative linear upper/lower enclosure.
```

Only after this factorization and a bound on its explicit correction can
linearity of the polarization projection give

```text
sum_(j=k+1)^K betaZ_j
  = betaProjection(
      1/2 Tr log endpointHat_K - 1/2 Tr log endpointHat_k)
    + betaProjection(J_(k:K)),
```

where `J_(k:K)` is the exact cumulative penalty/block-factor correction.  The
desired target is therefore a linear enclosure of the endpoint term **plus**
that explicit correction:

```text
betaZLower (K-k)
  <= sum_(j=k+1)^K betaZ_j
  <= betaZUpper (K-k),
```

not `betaZLower <= betaZ_j` for every `j`.  Dashen--Gross's universal
logarithmic residue is naturally an endpoint determinant statement and is
therefore better aligned with this cumulative target.  The owned work remains
to identify Bałaban's endpoint determinants with the same regulated
background-field quantity and to bound the finite endpoint errors uniformly.

The explicit `S/C/Q` derivative worksheet remains a fallback and an audit of
the coordinate cancellation, not the preferred critical path.

### Cumulative block-determinant theorem to instantiate

The finite-dimensional algebra needed next is exact.  Let `A` be the positive
gauge-fixed Hessian on a fine carrier and let `mathcalQ` collect all
linearized nested constraints whose values are retained during a multi-step
elimination.  The simultaneous constrained Gaussian has determinant factor

```text
det(A)^(-1/2) det(mathcalQ A^-1 mathcalQ*)^(-1/2).
```

Order the retained constraint coordinates by scale.  Block Gaussian
elimination (equivalently a block-Cholesky factorization) gives

```text
det(mathcalQ A^-1 mathcalQ*)
  = product_r det(Gamma_(r | < r)),
```

where `Gamma_(r | < r)` is the conditional covariance of the `r`-th
constraint coordinate after the preceding ones have been eliminated.  This
identity is the correct algebraic replacement for an adjacent equality of
operators.  To use it here, construct `mathcalQ` from the derivatives of the
composed Bałaban averages, then identify every conditional covariance with
the actual sequential shell calculation, including its `a`-penalty and
gauge-coordinate determinant.  The difference between this literal product
and the desired endpoint determinant is, by definition, `J_(k:m)` above.

This target is smaller than a new perturbative coefficient calculation: it is
a finite-dimensional determinant comparison with source-defined operators.
It either restores an exact endpoint factorization or isolates a concrete
Gaussian correction that must be estimated alongside the interaction
remainder.

### Interscale identification: the immediate next calculation

The one-scale constrained-Gaussian identity is confirmed by CMP 109 (1.4).
The immediate next calculation is narrower: prove the operator/background
identification.  A source check sharpens its literal meaning.  CMP 109
(2.10)--(2.11) identifies the shell quadratic form with the operator
`A^(k)` of CMP 99 (3.156), namely the coarse quadratic form containing both
the augmented Schur complement and the constraint-curvature contribution:

```text
A^(k) = (Q G_1 Q*)^-1 - a I - 2 <H_1 D~^(2)(B), J> .
```

Thus the relevant object is not a bare Hessian of the Wilson action.  It is
the Hessian of the **constrained Lagrangian** for the preceding minimization.
This is exactly the Hessian which occurs in the second-derivative formula for
a nested constrained minimum.

Write `F_j` for the classical action after the first `j` background
minimizations, and write `q_j` for the next nonlinear averaging map.  CMP 98
(127), (134) gives the composition of these maps, while the variational
construction used in CMP 109 (2.2)--(2.8) gives, on the regular tube,

```text
F_(j+1)(c) = min { F_j(b) : q_j(b) = c }.
```

At its minimizing pair let

```text
L_j = D^2 F_j - <lambda_j, D^2 q_j>
```

be the constrained-Lagrangian Hessian.  Finite-dimensional differentiation
of the stationarity and constraint equations gives the exact algebraic lemma

```text
D^2 F_(j+1) = (D q_j L_j^-1 D q_j*)^-1.                 (nested-minimum)
```

For auditability, this is not an appeal to a formal Schur-complement slogan.
With the multiplier convention

```text
D F_j(b) - D q_j(b)* lambda = 0,       q_j(b) = c,
```

differentiate at the minimizing pair.  The two linearized equations are

```text
L_j db = D q_j* dlambda,                D q_j db = dc.
```

They give

```text
db = L_j^-1 D q_j* (D q_j L_j^-1 D q_j*)^-1 dc,
dlambda = (D q_j L_j^-1 D q_j*)^-1 dc.
```

The envelope identity `D F_(j+1) = lambda` then gives
`(nested-minimum)`.  Thus the sole analytic/source work in this algebraic
step is identifying the literal operator `L_j`; no determinant manipulation
can repair a missing constraint-curvature term.

The `D^2 q_j` term is essential: it is the source role played by the
`D~^(2)`/constraint-curvature term in CMP 99 (3.127)--(3.129) and (3.156).
If `DeltaHat_j` is the positive augmented representative of `L_j`, the
literal consequence is

```text
D^2 F_(j+1) = (Q-bar_j DeltaHat_j^-1 Q-bar_j*)^-1 - a I.
```

The remaining source identifications are:

1. `DeltaHat_j` is the positive augmented representative of `L_j` on the
   exact gauge-fixed carrier used by the Gaussian;
2. the physical part of `D^2 F_(j+1)` is the next source operator, with the
   `- a I` convention restored exactly once;
3. the positive representative used in the next Gaussian is formed by the
   next-constraint penalty `a Q_(j+1)* Q_(j+1)`.

The third item rules out the unqualified adjacent telescope.  In the natural
source convention,

```text
DeltaHat_(j+1)
  = (Q-bar_j DeltaHat_j^-1 Q-bar_j*)^-1 - a I
    + a Q_(j+1)* Q_(j+1),
```

so `(Q-bar_j DeltaHat_j^-1 Q-bar_j*)^-1` is generally not the next augmented
Gaussian operator.  No background-independent conjugation can remove this
`a I` versus `a Q_(j+1)*Q_(j+1)` mismatch.  The originally proposed pairwise
identity is therefore not the current theorem target.

The minimization composition itself is not an extra conjecture.  Let `M_j`
denote the `j`-scale averaging constraint on a fine configuration, and let
`q_j` be its next one-step factor.  CMP 98 proves the nonlinear composition
of the averaging operations in (90)--(92), and CMP 102 defines `U_j` as the
unique minimum of the Wilson action with the combined constraints.  Hence
`M_(j+1) = q_j o M_j` gives directly

```text
min { A(U) : M_(j+1)(U) = c }
  = min { min { A(U) : M_j(U) = b } : q_j(b) = c }.
```

This is just equality of the two constrained sets, followed by the source
uniqueness of the regular minimum.  It supplies the `F_(j+1) = min F_j`
premise above.  CMP 102 §G additionally supplies the analyticity of the
minimal background needed to differentiate the identity on the regular tube.

Accordingly, the remaining literal audit is this four-line carrier
table:

```text
source object                    role in nested-minimum formula
--------------------------------------------------------------------------
CMP 109 A^(j), CMP 99 (3.156)    physical D^2 F_j, including curvature
A^(j) + a Q_j* Q_j               positive representative for current integral
(Q_j Lhat_j^-1 Q_j*)^-1 - a I    physical D^2 F_(j+1)
D^2 F_(j+1)+a Q_(j+1)*Q_(j+1)    positive representative for next integral
```

The comparison must be made on the gauge-fixed tangent carriers used in
CMP 109 (1.4).  There is a useful normalization correction here.  CMP 109
explicitly says of this construction that there are *no scaling
transformations*; the displayed `B = g_k B'` change in (2.10)--(2.12) is a
coupling normalization, not a lattice rescaling.  Moreover `Q_j` maps the
fine fluctuation variables at `T^(j)` directly to variables on `T^(j+1)`.
Consequently its Schur complement already acts on the same coarse tangent
carrier as the next step, but the penalty mismatch above remains on that
carrier.  Start with `R_j = I`; a nontrivial `R_j` is warranted only if the
source's gauge-coordinate convention introduces a separately defined
background-independent identification.

The correct immediate target is consequently a **cumulative block
determinant identity**.  Form the finite Gaussian with all nested linearized
constraints imposed at once, calculate its determinant once, and then
calculate it by sequential constraint elimination.  Equality by finite
dimensional Fubini/change of variables forces an exact factorization of the
shell determinants and every `a`-penalty factor.  This produces either a
genuine endpoint formula or an explicit cumulative correction; it does not
assume a false adjacent identification.

The desired shell identity is therefore conditional on that factorization:

```text
GammaZ_j(B) - GammaZ_j(0)
  = 1/2 Delta_B Tr log DeltaHat_(j+1)
    - 1/2 Delta_B Tr log DeltaHat_j
```

or identify the exact correction:

```text
GammaZ_j
  = 1/2 Tr log DeltaHat_(j+1)
    - 1/2 Tr log DeltaHat_j
    + J_j,
```

where `J_j` now includes the exact penalty/block-factor correction from the
cumulative determinant calculation, not an omitted factor in the constrained
Gaussian (1.4).  The nonlinear
constraint Jacobian, Haar-density ratio, and higher interaction terms remain in
`betaInt` and must be bounded cumulatively there.  The Gaussian telescope is
valid if `J_j = 0`, or if the residual satisfies

```text
betaProjection(J_j) = 0
```

or has its cumulative contribution placed under control.  Only after this
verification does the cumulative Gaussian coefficient become

```text
sum_(j=k+1)^m betaZ_j
  = betaProjection(
      1/2 Tr log DeltaHat_m - 1/2 Tr log DeltaHat_k).
```

### Revised route status

```text
one-scale constrained determinant identity:       closed from CMP 109 (1.4)
adjacent augmented Schur-complement telescope:    falsified by a-penalty mismatch
cumulative block-determinant factorization:        open (immediate target)
endpoint determinant / correction linear enclosure: downstream
cumulative interaction remainder:                  downstream
trajectory tuning and CMP 122 composition:         already architected
```

### What Dashen--Gross contributes

The local copy `/home/c/Downloads/dashen1981.pdf` is the correct paper,
DOI `10.1103/PhysRevD.23.2340`.  It performs a background-field calculation
for the Wilson lattice action and compares the lattice and continuum coupling
definitions.  Its one-loop answer is assembled from four contributions,
including lattice-artifact vertices, background-field quadratic terms, and
the gauge/ghost determinant.  The universal logarithmic coefficient emerges
only after these pieces are combined.

For the present proof this has two uses only:

* it is a normalization and sign checksum for the four-dimensional momentum
  calculation;
* it gives a tested decomposition against which the background expansion of
  Balaban's `localConstraintJacobian + constrainedTraceLog` can be compared.

It does not prove equality with Balaban's finite RG-step coefficient.  That
requires a source-specific equivalence between the constrained block
covariance and the background-field shell integrated by Dashen--Gross.
Character expansion is not required by either calculation; the shortest
route is finite-dimensional Gaussian differentiation, Wick contraction where
needed for `betaInt`, and lattice Fourier/resolvent evaluation.

## Nonlinear remainder and history work packet

Write the exponent in (2.13) exactly as

```text
Phi_k(g_k , U_(k+1) , B) = P^(k)(g_k , U_(k+1) , B) + {...}.
```

For a background path `U(t)`, finite-dimensional log-moment differentiation
has the structural form

```text
D log <exp Phi> = <D Phi>_Phi,

D^2 log <exp Phi>
  = <D^2 Phi>_Phi + Cov_Phi(D Phi , D Phi).
```

This identity identifies the actual nonlinear contributions without guessing
"determinant", "3--3", or "quartic" diagram labels.  Expanding the two
expectations by the explicit terms of (2.12), with Balaban's constrained
Gaussian measure, determines which Wick contractions occur and their powers
of `g_k`.

The required estimates are then:

```text
abs(betaInt_(j+1)(history)) <= CRem * smallPower(g_j),

abs(betaInt_(j+1)(g-history) - betaInt_(j+1)(h-history))
  <= sum_(i<=j) L_(j,i) abs(g_i - h_i).
```

The first may be replaced by a direct cumulative interaction-prefix estimate;
that cumulative remainder must be small relative to the Gaussian prefix
lower slope `betaZLower`.  The second must have enough scale separation to
contract the backward trajectory map.  CMP 109's
statement that the beta functions are smooth/analytic and uniformly bounded
does not supply either quantitative inequality.

## Promotion gate for an Agda coefficient module

Do not create `BalabanPerturbativeBetaCoefficient.agda` until the paper
calculation has produced all of the following literal data:

* the finite constrained operator whose determinant defines `betaZ`;
* the finite trace or momentum-sum formula for its polarization projection;
* a proved positive-slope interval for every finite Gaussian prefix (a
  pointwise shell interval is optional stronger data);
* the source-derived cumulative bound for the nonlinear remainder;
* the history-derivative kernel and a weighted contraction margin.

At that point the Agda module should encode those finite expressions and prove
the interval/remainder composition.  Before then, a field named
`leadingCoefficientPositive : Set` would only rename the missing theorem.

## Correct finite-cutoff fixed-point experiment

Fix a terminal inverse coupling `u_R`.  For a whole trajectory
`u = (u_0, ..., u_K)`, define the backward map

```text
(T_K u)_k = u_R + sum_{j=k+1}^K B_{K,j}(u_0, ..., u_{j-1}),
```

on a tube whose candidate members satisfy the Theorem-2 linear bounds.  A
uniform weighted sequence norm is required; fixed-cutoff numerical checks by
themselves are not sufficient.

The desired sufficient certificate is:

1. **Positive prefix interval.**  On the tube, for every `k < m <= K`,

   ```text
   betaLower (m-k)
     <= sum_(j=k+1)^m B_{K,j}(u)
     <= betaUpper (m-k),
   ```

   uniformly in cutoff, scale, finite volume, admitted background fields,
   and allowed histories, with `betaLower > 0`.

2. **History-sensitivity bound.**  For weights chosen so the backward sum is
   bounded,

   ```text
   ||T_K u - T_K v||_w ≤ q ||u - v||_w,  q < 1,
   ```

   uniformly in `K`.

3. **Finite-volume/localization error.**  The difference between the actual
   finite-volume coefficient and its controlled local/infinite-volume
   representation is absorbed in the same two inequalities.

Banach's theorem then gives a unique tuned trajectory with `u_K = u_R`.
The positive prefix interval immediately yields the required two-sided linear tube,
and hence the logarithmic bounds in Theorem 2.  The existing Agda
`BalabanBetaTubeEstimate` can consume this proof without an interface change:
its `TubePoint` may be the entire trajectory.

Contraction is only a sufficient route.  A direct perturbative shooting,
monotone-continuation, or degree argument is equally acceptable if it proves
the same tuned trajectory and bounds.

## Normalization and sign checks before any calculation

The first calculation must reproduce (5.42) in Balaban's conventions.  Do
not insert the continuum beta coefficient by hand.

In the inverse-square coordinate, conventional asymptotic freedom suggests
that an infrared coarse-graining correction has the form

```text
u_{k+1} = u_k - (positive constant + controlled correction),
```

up to Balaban's orientation and normalization.  Thus the leading source
coefficient to certify is order one in `u`-coordinates, not an asserted
`g_k^4` correction.  The sign, the factor of `log L`, and the relation to
the conventional one-loop coefficient are all outputs of the source-normalized
finite-lattice calculation.

Likewise, do not infer an `exp(-c/g²)` large-field penalty merely from
positivity of a quadratic fluctuation form.  After the usual fluctuation
rescaling, the coupling factors may cancel in the quadratic action.  Large
field suppression, block-averaging covariance mass, and the beta estimate are
separate source-level mechanisms.  CMP 122's conditional small/large-field
induction must not be used as a substitute for the missing beta estimate.

## First falsifiable computation

The smallest useful computer-assisted or analytic experiment is not a full
cluster expansion.  It is a certified evaluation of the second variation of
the finite-lattice fluctuation effective action sufficient to enclose the
coefficient in (5.42):

```text
fluctuation integral
  -> Pi^(j)_{mu nu}(x)
  -> sum_x Pi^(j)_{mu nu}(x) x_mu x_nu
  -> interval [betaLower, betaUpper].
```

It must then add an analytic tail argument which is uniform in `K`, `j`,
volume, and all histories in the tube.  Ward identities and the decomposition
(5.37)--(5.44) are the natural tools for eliminating forbidden lower-order
terms; locality/random-walk estimates are the natural candidates for the
finite-volume tail.

The falsification criteria are explicit:

* if the certified coefficient interval crosses zero, this contraction route
  fails in the proposed tube;
* if the history-sensitivity bound cannot be made `< 1` in any source-valid
  weighted norm, scalar shooting and this particular contraction mechanism
  are not justified;
* if only fixed-`K` intervals are available, the result is evidence, not a
  Theorem-2 proof.

## Completion criterion

The RG centre is complete only when this dossier is replaced by a paper proof
that constructs an inhabitant of
`BalabanRenormalisedCouplingConstruction` from the finite-lattice beta law.
The already checked arithmetic then yields finite-cutoff
`UniformBalabanRGClosureAt K`.  Continuum Schwinger functions, OS axioms,
O(4) restoration, observable-complete decay, and nontriviality remain
separate Clay-facing proof obligations.

## Source anchors

* CMP 109, pp. 259--260: Theorems 1--2 and (0.31); Theorem 2 is explicitly
  deferred to perturbative calculations.
* CMP 109, p. 264: (1.20)--(1.22), definition of the vacuum-polarization
  tensor and beta coefficient.
* CMP 109, pp. 260--261: (1.3)--(1.6), separation and subsequent merger of
  the Gaussian normalization `log Z^(j)` and nonlinear interaction
  `E^(j+1)`.
* CMP 109, pp. 267--268: (2.10)--(2.15), constrained fluctuation rescaling,
  covariance `(C* A^(k) C)^-1`, the explicit nonlinear exponent, and the
  inverse-square coupling update.
* CMP 109, pp. 297--298: (5.37)--(5.44), especially the exact identity
  (5.42), exponential kernel decay, and the statement that beta depends on
  preceding couplings.
* Balaban, CMP 95 (1984), pp. 28--29: (1.60)--(1.67), constrained minimizer,
  exact Gaussian RG factorization, and the free coarse quadratic symbol.
* Balaban, CMP 99 (1985), pp. 417--421: (3.109)--(3.129), positive
  gauge-fixed constrained minimization and
  `H = G Q^* (Q G Q^*)^-1` for both the basic and linearized nonlinear
  quadratic forms.
* Balaban, CMP 102 (1985), 255--275, DOI `10.1007/BF01229380`: source [16]
  cited by CMP 109 for the localized expansion of `log Z`; potentially
  reusable structure, but a three-dimensional result.
* Balaban--Imbrie--Jaffe, *Exact Renormalization Group for Gauge Theories*
  (1984): historical motivation only; it does not prove the four-dimensional
  finite-lattice coefficient estimate required here.

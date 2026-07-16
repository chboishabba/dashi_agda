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

1. **Constrained determinant reduction.**  Prove the finite Gaussian
   Schur-complement identity on the exact gauge-fixed source carrier.  This
   combines the local `S` Jacobian and `C^* A C` determinant into the
   fine-minus-coarse trace-log recorded below.  Keep the explicit `S/C`
   derivative route only as a fallback audit.
2. **Endpoint background Hessian.**  Telescope the Gaussian normalizations
   over the requested prefix and differentiate the two endpoint trace-logs
   twice at the identity background.  In ordinary finite-dimensional notation
   the diagnostic shape is

   ```text
   D^2 log det A [u,v]
     = Tr(A^-1 D^2 A[u,v])
       - Tr(A^-1 DA[u] A^-1 DA[v]),
   ```

   with the sign and factor inherited from the Gaussian integral.  This is a
   checksum only until the source's constrained measure has been reduced to
   that determinant formula.
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

### Coordinate-free determinant shortcut

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

Applied to the background-dependent source operators, put

```text
G_j(B) = A_j(B)^-1,
N_j(B) = Q_j(B) G_j(B) Q_j(B)^*.
```

Then, modulo background-independent normalization constants,

```text
GammaZ_j(B)
  = -1/2 Tr log A_j(B) - 1/2 tr log N_j(B).              (**)
```

This representation eliminates `S`, `C`, and all their derivatives from the
combined Gaussian calculation.  It does **not** eliminate the background
dependence of the complete averaging map `Q_j`, whose first and second
variations still come from CMP 98 (124).

The derivatives needed by (**) are finite algebra.  At the identity
background, with `G = A^-1`,

```text
D G[u] = - G D A[u] G,

D^2 G[u,v]
  = G D A[v] G D A[u] G
    + G D A[u] G D A[v] G
    - G D^2 A[u,v] G.
```

For `N = Q G Q^*`,

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
-1/2 Tr(G D^2 A[u,v] - G D A[u] G D A[v])
-1/2 tr(R D^2 N[u,v] - R D N[u] R D N[v]).              (***)
```

The local determinant and `C^*AC` Hessians written above are a useful check on
(***), but need not be evaluated separately if (*) is established on the
exact source carrier.

There is one mandatory source check before adopting this shortcut: `A_j` in
(*) must mean the complete positive operator on Bałaban's already gauge-fixed
finite ambient space.  If the operator still has gauge zero modes, (*) must be
applied after restricting to the Faddeev--Popov slice (or written with the
corresponding reduced determinant).  No unrestricted inverse of `D^*D` may be
introduced.  Subject to that check, the first explicit kernels needed by the
leading calculation reduce from four families to

```text
D Q_j,  D^2 Q_j,  D A_j,  D^2 A_j.
```

### Schur-complement telescoping shortcut

The coordinate-free formula has a further exact simplification when the
coarse quadratic form is defined by constrained minimization, as in CMP 95.
For

```text
H_j = A_j^-1 Q_j^* (Q_j A_j^-1 Q_j^*)^-1,
```

one has `Q_j H_j = I`, and the minimized coarse quadratic form is

```text
A_(j+1) = H_j^* A_j H_j
        = (Q_j A_j^-1 Q_j^*)^-1.
```

This is the finite-dimensional Schur-complement identity behind CMP 95
(1.60), (1.64), and (1.65).  Substituting it into (*) yields

```text
log Z_j(B)
  = -1/2 Tr log A_j(B)
    + 1/2 Tr log A_(j+1)(B_coarse)
    + background-independent constant.                         (****)
```

Thus the combined local `log det S`, constrained `C^*A_jC`, and averaging-map
terms are exactly a **fine-minus-coarse determinant shell**.  If (****) is
verified for the precise background-dependent gauge-fixed carriers used in
CMP 109, neither `D S`, `D C`, nor `D Q` needs to be evaluated separately.
The Gaussian polarization is simply

```text
D^2 log Z_j
  = 1/2 D^2 Tr log A_(j+1)
    - 1/2 D^2 Tr log A_j,
```

where the two background variations are related by Bałaban's exact
fine/coarse background map.

Across several Gaussian RG steps these determinants telescope:

```text
sum_(j=0)^(K-1) log Z_j
  = 1/2 Tr log A_K - 1/2 Tr log A_0
    + sum_j background-independent constants.
```

After the vacuum subtraction, the constants disappear.  This makes the
leading beta coefficient a shell difference of the standard background-field
one-loop determinant.  Dashen--Gross is therefore potentially useful at the
level of this **combined** determinant, rather than as a replacement for one
of Bałaban's coordinate terms.

This shortcut has two load-bearing checks:

1. the `A_(j+1)` occurring in CMP 109's next-scale quadratic action must be
   exactly the Schur complement of the gauge-fixed `A_j` and `Q_j` used in its
   Gaussian normalization, including the background map and measure
   convention;
2. telescoping controls the sum of shell coefficients rather than each shell
   separately.  This is not a defect for the shortest proof: the existing
   `BalabanBetaPrefixBound` consumer and the bilateral logarithmic inequalities
   in Theorem 2 are both cumulative statements.  A pointwise positive shell
   bound is stronger than the canonical route requires.

The operator part of check 1 is already present in the source.  CMP 99
(3.122)--(3.126) introduces the positive gauge-fixed operator `G^-1`, solves
the constrained minimum, and proves

```text
H = G Q^* (Q G Q^*)^-1.
```

The modified quadratic form actually used after linearizing the nonlinear
average has the same representation in (3.127)--(3.129), with `G_1` in place
of `G`.  Since the gauge-fixing terms vanish on the constrained minimizer,

```text
H^* G^-1 H = (Q G Q^*)^-1
```

is the next-scale minimized quadratic form.  What remains to check is the
measure-level determinant identity for the exact CMP 109 normalization,
including the Faddeev--Popov and linearization Jacobians; the finite Gaussian
identity (*) predicts their combined cancellation.

If check 1 holds, the shortest leading-coefficient proof is no longer the
termwise differentiation of CMP 98 (124).  It is:

```text
Schur-complement identity
  -> telescoped endpoint background determinant difference
  -> Ward/transverse projection
  -> cumulative linear upper/lower enclosure.
```

More explicitly, linearity of the polarization projection gives

```text
sum_(j=k+1)^K betaZ_j
  = betaProjection(
      1/2 Tr log A_K - 1/2 Tr log A_k),
```

with the endpoint backgrounds compared in the source scaling convention.
The desired target is therefore directly

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

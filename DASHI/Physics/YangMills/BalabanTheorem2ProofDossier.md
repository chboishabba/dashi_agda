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
definitions are the next source packet required before a numerical or symbolic
coefficient evaluator can be honest.

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

1. **Positive coefficient interval.**  On the tube,

   ```text
   0 < betaLower ≤ B_{K,j}(u) ≤ betaUpper,
   ```

   uniformly in cutoff, scale, finite volume, admitted background fields,
   and allowed histories.

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
The positive interval immediately yields the required two-sided linear tube,
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
* CMP 109, pp. 297--298: (5.37)--(5.44), especially the exact identity
  (5.42), exponential kernel decay, and the statement that beta depends on
  preceding couplings.
* Balaban--Imbrie--Jaffe, *Exact Renormalization Group for Gauge Theories*
  (1984): historical motivation only; it does not prove the four-dimensional
  finite-lattice coefficient estimate required here.

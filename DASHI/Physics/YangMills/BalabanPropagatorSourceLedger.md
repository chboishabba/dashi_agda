# Balaban propagator packet: coefficient-extraction ledger

Status: all six prerequisite papers are locally available; literal operator
extraction is in progress. This is a research ledger, not a theorem import and
not evidence that the deferred CMP 109 Theorem 2 has been proved.

## Local primary sources verified

| Source | Local copy | Role in the beta calculation |
| --- | --- | --- |
| CMP 109 (1987), *Renormalization group approach … I* | `Downloads/pdf's/1104116842.pdf` | Defines the fluctuation effective action, vacuum polarization and the beta coefficient. Equation (2.15) is the inverse-square recurrence. Equation (5.42) identifies beta with an off-diagonal polarization moment. |
| CMP 116 (1988), *… II. Cluster expansions* | `Downloads/renormalization-group-approach-to-lattice-gauge-field-4penm4k7hc.pdf` | Localizes/exponentiates the small-field fluctuation correction; it does not prove the tuned coupling theorem. |
| CMP 99 (1985), *Propagators … in a background field* | `Downloads/pdf's/1103942769.pdf` | Supplies regularity, decay, localization and analyticity estimates for the background-dependent propagators. |

The following prerequisite files are now also present under `Downloads/`:

| Source | Local copy | First extraction anchor |
| --- | --- | --- |
| CMP 95 (1984), *Propagators I* | `balaban1984.pdf` | Sect. A defines the Abelian constrained transform; Sect. E gives minimizers; Proposition 1.2 starts the regularity/decay package. |
| CMP 96 (1984), *Propagators II* | `10.1007@BF01240221.pdf` | Sect. 2 handles restrictions at several scales; Proposition 2.2 gives convergent generalized random-walk control; Proposition 2.3 handles the averaged covariance inverse. |
| CMP 98 (1985), *Averaging operations* | `10.1007@BF01211042.pdf` | Sect. B defines compositions of one-step averages and their regular/analytic behavior. |
| CMP 99 (1985), *Regular configurations and gauge fixing* | `10.1007@BF01466594.pdf` | Sect. A defines regularity conditions; Sect. C / Theorem 2 controls the axial-to-Landau gauge transformation on the regular chart. |
| CMP 102 (1985), *Variational problem and background fields* | `220_2005_Article_BF01229381.pdf` | Theorem 1 gives a minimal orbit and regularity; Proposition 9 gives the axial-gauge analytic/minimizer representation used later for `U_k(V)`. |

## Required six-paper operator chain

| CMP reference in CMP 109 | Required object | Exact role | Local status |
| --- | --- | --- | --- |
| 95 (1984), 17–40: *Propagators and renormalization transformations I* | free/constrained propagators | Base renormalization-transform and decay machinery | local: `balaban1984.pdf` |
| 96 (1984), 223–250: *… II* | continuation of propagator construction | constraint/localization machinery | local: `10.1007@BF01240221.pdf` |
| 98 (1985), 17–51: *Averaging operations …* | gauge-covariant averages `Q`, `Q_k` | Defines the block maps consumed by the fluctuation action | local: `10.1007@BF01211042.pdf` |
| 99 (1985), 75–102: *Spaces of regular gauge field configurations …* | regular chart and gauge fixing | Admissible background-field tube | local: `10.1007@BF01466594.pdf` |
| 99 (1985), 389–434: *Propagators … in a background field* | `G'(U)`, `G(U)`, `R(U)` and local expansions | Theorems 3.1–3.4 give regularity, decay and analyticity; Theorem 3.7 / Corollary 3.8 give a generalized random-walk localization | verified locally |
| 102 (1985), 277–309: *Variational problem and background fields …* | minimizer `U_k(V)` and linearized maps | Background/minimizer construction used by CMP 109 | local: `220_2005_Article_BF01229381.pdf` |

## Literal source seam

CMP 109 uses the prerequisite results in its fluctuation analysis:

```text
regular gauge configuration + minimizer/background maps
  -> fluctuation Hessian and constrained Gaussian covariance
  -> E^(k+1) fluctuation effective action (2.13)
  -> second variation / vacuum polarization Pi^(j)
  -> beta_j = sum_x Pi^(j)_{mu nu}(x) x_mu x_nu, mu != nu  (5.42)
```

Literal anchors checked in the local text extraction:

- CMP 109 (2.13) defines the next fluctuation effective action as the logarithm
  of the constrained fluctuation integral; (2.15) performs inverse-square
  coupling renormalization.
- CMP 109 (5.37)--(5.38) decomposes the polarization tensor into the transverse
  Wilson-term coefficient plus a third-lattice-derivative remainder.  The
  following (5.42) identifies that coefficient with both the off-diagonal
  second momentum derivative and the coordinate-space moment used by the beta
  recurrence.  The text immediately after (5.42) explicitly warns that
  `beta_j`, while displayed as a function of `g_{j-1}`, depends on the prior
  coupling history as well.
- CMP 99 background-propagator Theorem 3.14 states the domain-sequence
  difference estimate, with the additional distance-decay factor (3.154).
  Its proof cancels random-walk terms localized in the common domain.
- CMP 102 Theorem 1 establishes the regular minimal orbit; Proposition 9 gives
  the analytic extension of `U_k(V)` and records derivative decay estimates
  for the regular background chart.

The normalization audit is mandatory: CMP 109 first displays `g_k^-2` terms
in the raw fluctuation integral, then rescales the fluctuation field before
introducing its Gaussian covariance. Background-propagator positivity must not
be misread as an automatic `exp(-c/g_k^2)` large-field estimate.

## Exact verified propagator input

In the locally available CMP 99 paper:

- Theorems 3.1–3.3 establish background-dependent propagator bounds and state
  constants independent of the domain sequence when the stated regularity
  hypotheses hold.
- Theorem 3.4 establishes analytic dependence on a complexified regular
  background-field neighborhood while preserving those estimates.
- Theorem 3.7 gives a convergent generalized random-walk representation;
  Corollary 3.8 localizes individual walk terms and retains exponential decay.

More specifically, its domain-sequence difference discussion culminates in
(3.154): random-walk contributions whose localizations remain in the common
domain cancel, while the remaining terms acquire an exponential factor in the
distance to the discrepancy.  This is the source input for the finite-volume
tail; the owned bridge is to propagate it through the polarization diagrams,
including the weighted `x_mu x_nu` moment and history/background sensitivity.

## Modern auxiliary method source (not a Yang--Mills substitute)

`Downloads/2403.09800.pdf`, Dybalski--Stottmeister--Tanimoto, *The Bałaban
variational problem in the non-linear sigma model* (2024), is useful as a
transparent proof template for the minimizer layer.  Its Sections 4.1--4.7
derive a constrained critical-point equation and solve it by Banach contraction;
Sections 4.2--4.6 and Appendix A obtain positivity and exponential kernel bounds
via random-walk expansions.

It is **not** an authority for the four-dimensional gauge covariance,
vacuum-polarization coefficient, history-dependent beta law, or CMP 109
Theorem 2.  Its value is methodological: once the six primary papers pin the
Yang--Mills operators, its contraction/Green-kernel proof layout is a candidate
for formalizing the background-minimizer sublemma without inventing an operator
normalization.

## Next source extraction deliverable

The prerequisite packet is complete. Fill the following table with literal
definitions/equation numbers before implementing a numerical coefficient
evaluator.

| Symbol | Definition source | Domain/codomain | Required uniform estimate |
| --- | --- | --- | --- |
| `Q`, `Q_k` | CMP 98 | fine links to blocked links | norm/derivative and gauge covariance |
| `C`, `C*` | CMP 95/96 | constrained fluctuation coordinates | projection/constraint identities |
| `A^(k)` | CMP 109 plus packet | constrained Hessian | positivity and background stability |
| `C^(k)` | CMP 109 plus CMP 95/96/99 | covariance kernel | decay, derivatives, finite-volume comparison |
| `U_k(V)` | CMP 102 | coarse background to fine minimizer | existence, regularity, locality |
| `H_k` | CMP 99/102 | background variation map | decay and history sensitivity |
| `Pi^(j)` | CMP 109 §5 | bond/polarization kernel | Ward/transversality and local majorant |
| `beta_j` | CMP 109 (5.42) | coupling history to real | positive interval and sensitivity |

### Extracted operator anchors

- **Gauge-covariant block average.** CMP 98 (121)--(122) writes the nonlinear
  one-step average as `Q(V_0,A,c) = i log(...)` and proves its analytic split
  `Q(V_0,A,c) = L(Q(V_0)A)_c + C(V_0,A,c)`.  Proposition 3 then gives the
  analytic small-field control.  Equations (90)--(91) define the iterated
  averages.  This is the source-level `Q`, `Q_k` input; it is not an ordinary
  scalar block average.
- **Constrained covariance.** CMP 96 (2.156) gives the covariance in the
  form `C^(k) = C (C* A_k C)^(-1) C*` (with the paper's constrained-coordinate
  normalization).  The surrounding text states that the inverse inherits the
  required short-range properties.  Proposition 2.2 gives the generalized
  random-walk control, and Proposition 2.3 treats the corresponding averaged
  inverse.
- **Regular-background propagators.** CMP 99 background-field (3.25)--(3.26)
  defines the projected operator `R(U)` and the regularized Hessian
  `A'(U) = A''(U) + D*R(U)D + Q*(U)aQ(U)`.  Theorems 3.1--3.3 give the kernel
  estimates for `G'`, the averaged inverse, `R`, and `G`; Theorem 3.4 extends
  them analytically to the complex regular-background tube.  Theorem 3.7 is
  the localized random-walk expansion.
- **Minimizing background.** CMP 102 Theorem 1 provides the regular minimal
  orbit.  Proposition 9 identifies the analytic extension of the axial-gauge
  `U_k(V)` and gives its regular-background derivative bounds (via (190)).

The associated Agda surfaces are
[`BalabanCutoffBetaLaw.agda`](BalabanCutoffBetaLaw.agda),
[`BalabanVacuumPolarisationCoefficient.agda`](BalabanVacuumPolarisationCoefficient.agda),
and
[`BalabanVacuumPolarisationDomainTail.agda`](BalabanVacuumPolarisationDomainTail.agda).
The coupling law admits either direct finite-volume uniform beta bounds or a
reference-coefficient tail.  The domain-tail target is the source-faithful
inequality obtained by carrying CMP 99 (3.154) through CMP 109's weighted
polarization moment; it remains an unavailable owned theorem.

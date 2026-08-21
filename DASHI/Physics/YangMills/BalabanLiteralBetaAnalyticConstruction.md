# Literal Wilson/FP/Haar beta: minimal constructive target

## Sources

- Kenneth G. Wilson, *Confinement of Quarks*, Physical Review D **10**
  (1974), 2445–2459. DOI:
  [10.1103/PhysRevD.10.2445](https://doi.org/10.1103/PhysRevD.10.2445).
- Ludwig D. Faddeev and Victor N. Popov, *Feynman Diagrams for the Yang–Mills
  Field*, Physics Letters B **25** (1967), 29–30. DOI:
  [10.1016/0370-2693(67)90067-6](https://doi.org/10.1016/0370-2693(67)90067-6).
- Tadeusz Bałaban, *Renormalization Group Approach to Lattice Gauge Field
  Theories. I. Generation of Effective Actions in a Small Field Approximation
  and a Coupling Constant Renormalization in Four Dimensions*, Communications
  in Mathematical Physics **109** (1987), 249–301. DOI:
  [10.1007/BF01215223](https://doi.org/10.1007/BF01215223).

## The positivity margin

For \(G=\mathrm{SU}(2)\), the fixed universal inverse-coupling coefficient is

\[
 C_A\frac{11}{24}=\frac{11}{12}.
\]

Consequently the literal regular/history contribution \(r_j\) need only obey

\[
 |r_j|<\frac{11}{12}
\]

to prove positive beta.  A deliberately wide sufficient target is

\[
 |r_j|\le\frac12
 \quad\Longrightarrow\quad
 \frac5{12}\le\beta_j\le\frac{17}{12}.
\]

The four-orbit calculation controls this finite regular term; it must not be
used to rediscover the universal \(11/12\) logarithmic coefficient.

## What the four-orbit reduction actually leaves

Hypercubic symmetry reduces the 240 regular Brillouin cells to four values,
with exact multiplicities

\[
 64I_1+96I_2+64I_3+16I_4. \tag{1}
\]

This is useful only after a single scalar integrand has been constructed from
the same Wilson action, reduced Faddeev--Popov determinant, Haar measure, and
the transverse Ward projection.  The four values are then rigorous interval
quadratures of that one expression, with the infrared singular term subtracted
before regular-cell evaluation.

## Audit result: the live missing calculation

`BalabanClayT4LiteralOneLoopBoxEvaluatorExact.agda` defines a recursive
interval language, but its record `LiteralDiagramExpressions` takes
`wilsonQuadraticVertex`, `wilsonCubicVertex`, `wilsonQuarticVertex`,
`faddeevPopovOperator`, `ghostBackgroundVertex`, and `haarQuadraticVertex` as
unconstrained caller fields.  Its Ward record likewise accepts the Ward facts
as fields.  Therefore it is a sound *verification target*, not an instantiated
Wilson/FP/Haar calculation.

The minimal physical implementation is exactly:

1. Derive the momentum-space quadratic, cubic, quartic, ghost, and Haar
   vertices from the already-defined literal link/plaquette jets, including all
   orientation and normalization factors.
2. Contract them into the transverse vacuum-polarization scalar and prove the
   lattice Ward identity for that same expression.
3. Substitute those expressions into the four representative cells in (1),
   using outward-rounded trigonometric and quadrature error bounds, and prove
   the resulting regular/history contribution lies in a radius strictly below
   \(11/12\) (the wide \(1/2\) target is enough for SU(2)).
4. Prove the colour contraction is \(C_A\) times this same scalar and give a
   group-uniform remainder radius below \(11C_A/24\) for compact-simple \(G\).

No orbit, denominator, or interval refactor is needed before Step 1.  Until
the vertices and Ward scalar are materialized, no numerical interval bound can
be a bound on the literal RG beta coefficient, so
`LiteralCompactSimplePositiveBeta` remains conditional.

## Literal finite-coordinate work already available

The gap is not the Taylor algebra. The side-four action surface
`BalabanP33LiteralWilsonFPHaarFourthJetExact.agda` already defines raw finite
contractions from one rational coordinate carrier:

\[
 \sum_{a,b}V_{AAqq}(e_\mu,e_\nu,e_a,e_b)G_{ab},
 \qquad
 \sum_{a,b,c,d}V_{Aqq}(e_\mu,e_a,e_b)G_{ac}
                  V_{Aqq}(e_\nu,e_c,e_d)G_{bd},
\]

alongside a reduced-FP two-jet and the Haar
\(\tfrac13\operatorname{Tr}G\) insertion. These are literal finite sums, but
they intentionally precede effective-action symmetry factors and external
momentum extraction.

The shortest next theorem is a **same-object Fourier contraction identity**:
insert normalized external lattice plane waves into precisely those four sums,
prove their contraction is the Wilson/FP/Haar transverse momentum kernel, and
establish its arbitrary-side normalization. Only then may the trigonometric
four-orbit evaluator be populated. Treating a side-four Green sum as one
Brillouin-box value would be a category error: the side-four momentum carrier
and the continuum-oriented box partition are not identified.

There is one prerequisite below that theorem. `BalabanPeriodicTorus4Fourier`
is an authority interface: its character, character orthogonality, inversion,
and Parseval data are caller inputs. The checkout **does** already contain an
explicit Gaussian-rational \(\mathbb Q[i]\) table `character1` and its tensor
product `character4` in `BalabanSide4ScalarGreenKernelComputed.agda`; the
earlier constant-character regression is not the only character data.

The live foundational seam is narrower: promote that exact table to the
literal Fourier authority by proving its C4 multiplication and conjugation
laws, finite \(\mathbb Z_4^4\) orthogonality/inversion, and its normalization
against the rational coordinate carrier. Only that promotion makes the
proposed plane-wave contraction an evaluable theorem rather than another
Fourier interface.

The one-dimensional multiplication and conjugation laws are now exhausted
directly over the 64 and 16 C4 cases, respectively, in
`BalabanSide4GaussianCharacterCoreExact.agda`. The remaining Fourier premise
is specifically the fourfold tensor/orthogonality/inversion calculation, not
another choice of phase convention. The tensor character laws themselves are
now proved in `BalabanSide4GaussianFourTorusCharacterExact.agda`; only finite
orthogonality, inversion, Parseval, and normalization remain at this Fourier
layer.

The one-dimensional orthogonality factor has now also been evaluated exactly
in `BalabanSide4GaussianCharacterOrthogonalityExact.agda`:
\(\sum_{x\in\mathbb Z_4}\chi(k,x)\overline{\chi(\ell,x)}=4\delta_{k\ell}\).
The remaining task is its fourfold tensor/Fubini promotion, followed by
inversion and Parseval at the literal \(1/256\) normalization.

The three new character files contain explicit draft proof terms but are
marked conditional because the requested workflow forbids running Agda; no
machine-check status is claimed pending an allowed focused check.

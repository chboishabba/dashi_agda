# Riemann reflection-orbit defect — 2026 frontier

## Primary source

Levent Alpöge and Ralph Furman, **“More than two thirds of the zeta zeros are simple and on the critical line”**, arXiv:2608.13637 (2026). DOI: `10.48550/arXiv.2608.13637`.

Machine-checked companion consulted for the exact zero-side block decomposition: Anthropic, `zeta-23-lean`, especially `Zeta23/ZeroSide.lean` (2026, Apache-2.0).

This tranche is source-calibrated to the 2026 rank/trace + Sylvester-inertia argument, but it does not claim to reprove the paper's analytic Weil-form estimates or the Riemann hypothesis.

## 1. Centre the functional-equation reflection

Write a hypothetical nontrivial zero as

\[
\rho = \frac12 + \alpha + i\gamma.
\]

The functional-equation partner at the same ordinate is

\[
1-\overline\rho = \frac12-\alpha+i\gamma.
\]

Thus the transverse coordinate carries the involution

\[
\alpha\longleftrightarrow-\alpha.
\]

`RiemannReflectionOrbitDefectExact.agda` isolates exactly this geometry in a finite/discrete carrier:

```text
criticalCentre
left magnitude  <->  right magnitude
```

with a unique fixed centre.  The quotient forgets left/right orientation while retaining magnitude, and its first nontrivial residual is the squared defect

\[
\delta = \alpha^2
\]

in the analytic interpretation.  The Agda carrier uses natural-number magnitudes deliberately; it is a theorem-bearing orbit model, not a model of the actual real parts of zeta zeros.

The module proves:

```text
reflection is involutive
reflection-fixed => critical centre
orbit magnitude is reflection invariant
squared defect is reflection invariant
zero squared defect => critical centre
left count = right count for every paired finite population
nonfixed count = left count + right count = 2 * pair count
```

The small `4 fixed + 1 inverse pair = 6 total` checksum records the exact `2/3` finite geometry only.  The asymptotic theorem remains analytic authority from Alpöge--Furman.

## 2. Inverse pairing kills orientation, not every residual

`RiemannReflectionPairBlockExact.agda` provides a deliberately elementary swap-symmetric diagnostic block

\[
B(m)=\begin{pmatrix}0&m\\m&0\end{pmatrix}.
\]

Its trace-like observable is zero for every inverse pair, while the squared off-diagonal observable is `m^2`.  The exact finite falsifier is:

```text
near pair: trace = 0, defect = 1
far pair:  trace = 0, defect = 9
```

Hence a symmetric quotient can legitimately erase orientation while retaining a consumer-relevant defect.  This is a generic algebraic diagnostic only; `B(m)` is **not** asserted to be the paper's Weil block.

## 3. What the actual 2026 inertia argument sees

The source-native off-line contribution is sharper and also exposes an obstruction.

For one representative of an off-line pair, write its complex evaluation vector as

\[
u=x+iy.
\]

The verified zero-side source records the paired bilinear contribution as

\[
m\bigl(uu^T+\overline u\,\overline u^T\bigr)
  = 2m\bigl(xx^T-yy^T\bigr).
\]

Thus the pair is a difference of two positive rank-one forms: a pullback of a two-dimensional hyperbolic form of signature \((1,1)\).  In the formal companion this appears as the `rePart - imPart` decomposition, followed by the theorem

```text
n_+(Q) <= p
```

for `p` unordered off-line reflection pairs.  Sylvester inertia therefore implies that the pulled-back contribution costs **at most one positive direction per off-line pair**.

`RiemannWeilOffLineHyperbolicBlockExact.agda` formalizes the finite signature ledger:

```text
one off-line pair -> source signature (1 positive, 1 negative)
#off = 2 * pairCount
source positive-index budget = pairCount
source negative-index budget = pairCount
```

### Crucial result: the current inertia budget is displacement-blind

The same module proves a genuine no-factor theorem.

Two inverse-pair states may have different squared defects, for example `1` and `9`, while the bare source signature observer sends both to the same non-fixed-pair code.  Therefore there is no function

```text
source signature -> squared defect
```

that reconstructs the defect on all reflection states.

This means the current Alpöge--Furman inertia count does **not** give an \(\sum \alpha^2\) or higher transverse-moment bound for free.  It controls **how many positive directions an unresolved pair can cost**, not how far the pair sits from the critical line.

That distinction is the main mathematical advance of this implementation pass: it turns a tempting analogy into an explicit theorem-level obstruction.

## 4. Monster C3 cross-pollination: orbit shape only

`RiemannReflectionC3OrbitShapeBridgeExact.agda` reuses the existing exact Monster/C3 cyclotomic carrier:

\[
1+\zeta+\zeta^2=0,
\qquad
\zeta^{-1}=\zeta^2.
\]

The common orbit shape is

```text
C3:   identity fixed + {zeta, zeta^-1}
zeta: critical centre + {left magnitude, right magnitude}
```

or abstractly

```text
one fixed sector + one inverse-oriented pair role.
```

The bridge proves only this action/orbit-role correspondence.  It explicitly blocks:

```text
Monster carrier = zeta-zero carrier
cyclotomic cancellation = Weil inertia
Monster phase data => Riemann-zero location
```

There is also a structural difference worth retaining: C3 has only one nontrivial inverse orbit, whereas the zeta reflection quotient can retain a continuum of magnitudes in the analytic setting.  Therefore the C3 analogy motivates the fixed-plus-inverse-pair organization but does not supply the missing displacement observable.

Existing C3 sources remain those already attached to `MonsterC3CyclotomicEvaluationExact.agda`: I. M. Isaacs, *Character Theory of Finite Groups* (no DOI assigned), and Audrey Terras, *Fourier Analysis on Finite Groups and Applications*, DOI `10.1017/CBO9780511626265`.

## 5. Exact next frontier

The current implementation narrows the next high-alpha question to one source-facing producer:

> Find an analytic observable of the actual off-line Weil pair that is reflection invariant **and** quantitatively sensitive to \(|\beta-1/2|\), then prove that the rank/trace or Hilbert--Schmidt machinery controls its aggregate.

The typed `DistanceSensitiveOffLineAdapter` records the minimum bridge data needed before such a promotion is legitimate.

A successful strengthening would need more than the bare hyperbolic signature.  Candidate directions include:

1. inspect whether the norms, Gram determinants, singular values, or Hilbert--Schmidt contributions of the **actual** evaluation vectors retain transverse displacement after the reflection pair is assembled;
2. connect any such invariant to the explicit-formula kernel strongly enough to sum it over zeros;
3. determine whether the bandwidth/support restrictions of the present pair-correlation input prevent a weighted improvement just as they constrain the counting route;
4. only then formulate a weighted even-moment target such as a controlled version of
   \[
   \sum_{|\gamma|\le T}(\beta-1/2)^2.
   \]

Until that analytic producer exists, the repository keeps

```text
weighted transverse moment bound = false
RH proved here = false
```

while retaining the exact orbit, quotient, no-factor, and source-signature mathematics already closed.

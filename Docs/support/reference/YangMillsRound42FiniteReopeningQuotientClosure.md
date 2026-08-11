# Yang–Mills Round 42 — finite reopening, split quotient, and covariance closure

This note supersedes the earlier Round-42 statement that the selected-background Green still required a Neumann-limit/completeness bridge. The current branch closes the finite reopening algebraically, replaces the singular raw combined multiplier presentation by an explicit split presentation, proves a strict same-object floor on that presentation, and extends finite RG reopening from moments to connected two-point functions.

## 1. Finite reopening replaces a Neumann limit over Q

On the literal 768-row selected gauge multiplier carrier the already-proved residual is

\[
R_A = G_0 E_A,
\qquad
\|R_A\|_1 < \frac1{10},
\]

and its rational Combes–Thomas conjugate satisfies

\[
\|D R_A D^{-1}\|_1 < \frac16.
\]

`BalabanFiniteStrictContractionReopeningExact` proves directly from

\[
x + R x = y
\]

that

\[
(1-q)\|x\|_1 \le \|y\|_1.
\]

Thus the unweighted reopening has norm bound `10/9`, the weighted reopening has norm bound `6/5`, and the homogeneous equation has zero norm. A complete finite selector upgrades zero norm to pointwise zero, so `I+R_A` and its weighted conjugate are pointwise injective.

`BalabanFiniteRationalInjectiveInverseExact` isolates only the standard finite-dimensional field theorem

```text
finite square injective rational matrix => rational inverse
```

as imported linear algebra. No Yang–Mills estimate is hidden in that authority.

## 2. The literal perturbation and residual are same-object identities

`BalabanSelectedBackgroundGaugePerturbationActionExact` proves that the literal finite matrix

\[
K_A-K_0
\]

used by the absolute-mass estimates acts exactly as

\[
E_A=L_0D_A^*+D_AL_0^*+D_AD_A^*.
\]

`BalabanSelectedBackgroundResidualActionExact` then proves that the literal residual kernel used in the `<1/10` and `<1/6` estimates acts exactly as

\[
R_A=G_0E_A.
\]

This closes the previous same-object seam between coefficient estimates and the operator decomposition.

## 3. Exact selected-background regularized gauge Green

Let

\[
M_A=I+R_A.
\]

The finite inverse certificate for `M_A` defines

\[
G_A=M_A^{-1}G_0.
\]

`BalabanSelectedBackgroundGaugeGreenFiniteExact` proves pointwise

\[
G_AK_A^{\rm reg}=I,
\qquad
K_A^{\rm reg}G_A=I.
\]

The second direction uses injectivity of the already exact flat Green rather than an infinite series.

`BalabanSelectedBackgroundGaugeGreenDecayExact` applies the rational weight

\[
w=\prod_{\mu=1}^{4}(64/65)^{d_{C_4}(x_\mu,y_\mu)}
\]

and obtains

\[
\boxed{|G_A(x,y)|\le 3\,w(x,y).}
\]

This is a fixed-side-four Gate-I exponential-decay theorem. It is not the later scale-uniform physical decay theorem required for a continuum mass gap.

## 4. The raw 780-row Gram no-go remains decisive

The literal combined constraint has 12 block-average rows and all 768 gauge rows. At the identity background, take a multiplier which is zero on every average row and nonzero constant on every gauge row. The actual flat gauge adjoint is the negative periodic gradient, hence

\[
L_0^*\lambda=0,
\qquad \lambda\ne0,
\]

and therefore

\[
(L_0L_0^*)\lambda=0.
\]

`BalabanSelectedCombinedConstraintRawGramNoGoExact` formalizes this witness and proves that the raw flat 780-row Gram has no two-sided rational inverse.

Consequently the formula

\[
I-L_A^*(L_AL_A^*)^{-1}L_A
\]

cannot be used on the unreduced raw multiplier carrier.

## 5. Split exact combined multiplier presentation

`BalabanSelectedCombinedMultiplierSplitExact` implements the quotient/reopening discipline directly.

A raw multiplier is split as

\[
\lambda=(\alpha,\gamma),
\]

with twelve average coordinates and 768 gauge coordinates. The gauge part is projected to its componentwise-mean-zero representative. The reduced object retains

```text
average multiplier alpha
mean-zero gauge multiplier gamma
proof that gamma is componentwise mean zero.
```

There are explicit maps

```text
reduceSelectedMultiplier : raw -> reduced
reopenReducedMultiplier : reduced -> raw
```

and the raw representative projector

\[
P=sq
\]

is `selectedCombinedReducedProjection`.

The module proves pointwise:

```text
q(s(reduced)) = reduced,
P(P(raw)) = P(raw),
```

and identifies the exact kernel of `P` as

```text
zero average part + zero centered gauge part,
```

i.e. the flat presentation redundancy. It also proves that a gauge multiplier with zero centered part is pointwise equal to its componentwise constant projection.

This is deliberately a **computational flat-reference presentation**, not a theorem that the nonlinear physical stabilizer is globally the same three-dimensional constant sector. The previously proved holonomy/stabilizer stratification remains in force.

## 6. Same-object reduced adjoint and exact flat orthogonality

`BalabanSelectedReducedCombinedConstraintFloorExact` defines the reduced adjoint by reopening into the literal raw operator:

\[
L_{A,\mathrm{red}}^* := L_A^*\circ s.
\]

`selectedReducedCombinedAdjointSameObject` proves that this is exactly the sum of the literal average adjoint and background gauge adjoint; no second comparison operator is introduced.

The important new simplification is stronger than a generic cross-angle estimate. At the flat reference the average and gauge normal directions are **exactly orthogonal**.

The proof is finite and literal:

1. the flat gauge adjoint is the negative periodic forward gradient;
2. the sum of every periodic forward difference is exactly zero;
3. therefore every block-average row applied to the flat gauge adjoint is zero;
4. rectangular finite adjointness gives

\[
\boxed{
\langle L_{\rm avg}^*\alpha,L_{g,0}^*\gamma\rangle=0.
}
\]

The average normal operator was already exactly `256 I`, while the reduced flat gauge adjoint has floor `1/16`. Hence the flat reduced **combined** adjoint has the common floor

\[
\frac1{16}
\bigl(\|\alpha\|^2+\|\gamma\|^2\bigr)
\le
\|L_{0,\mathrm{red}}^*(\alpha,\gamma)\|^2.
\]

The selected background changes only the gauge-adjoint part. Its already-proved defect obeys

\[
\|D_A^*\gamma\|^2
\le
\frac{3}{1024}\|\gamma\|^2
\le
\frac{3}{1024}
(\|\alpha\|^2+\|\gamma\|^2).
\]

Applying the square-root-free perturbation theorem therefore gives the actual reopened selected adjoint floor

\[
\boxed{
\frac{29}{1024}
\bigl(\|\alpha\|^2+\|\gamma\|^2\bigr)
\le
\|L_A^*s(\alpha,\gamma)\|^2.
}
\]

This avoids diagonalizing a 777-by-777 Gram and avoids an artificial cross-angle budget.

## 7. Restricted reduced-adjoint injectivity

`BalabanFiniteSelectorL2DefinitenessExact` proves, for any proof-bearing finite rational selector, that zero finite squared norm forces every represented coordinate to be zero.

`BalabanSelectedReducedCombinedAdjointInjectiveExact` combines that theorem with the `29/1024` floor. Under the selected radius hypothesis,

\[
L_A^*s(\alpha,\gamma)=0
\]

pointwise implies

\[
\alpha=0,
\qquad
\gamma=0
\]

pointwise on their finite row selectors.

This is the correct result after the raw-Gram no-go:

\[
\boxed{
L_A^*|_{\operatorname{im}s}\text{ is injective.}
}
\]

It does **not** assert

\[
\ker L_A^*=\mathcal C
\]

on the raw carrier at every background.

There is still one physical-identification theorem between this computational section and the actual selected tangent/constraint problem. The fixed mean-zero presentation must not be mistaken for a global description of the nonlinear stabilizer.

## 8. Configuration section versus multiplier section

The branch now has two distinct section constructions which must remain conceptually separate.

`BalabanBasedPathGaugeSectionExact` gives a **configuration-space** section: a rooted path system constructs a gauge arrow and a rooted representative, and uniqueness holds inside the based rooted slice.

`BalabanSelectedCombinedMultiplierSplitExact` gives a **constraint-multiplier** section: a raw row multiplier is reduced and reopened through the componentwise-mean-zero presentation.

The first removes gauge-orbit ambiguity of fields. The second removes redundant constraint coordinates. They are not interchangeable.

## 9. Exact block-average compatibility criterion

The existing generic transported-log averaging package `CompactLieBlockAverage` already proves Bałaban-style gauge covariance

\[
Q(U^g)=Q(U)^{g_{\rm coarse}}.
\]

`BalabanBlockAnchoredGaugeAverageCompatibilityExact` now consumes that theorem in the direction needed by Gate I. If the fine gauge arrow restricts to the identity coarse gauge, then

\[
\boxed{Q(U^g)=Q(U)}
\]

exactly.

This is an important correction to the earlier wording. A gauge which is merely identity at **one** root is not automatically proved to preserve every nonlinear block average. The sufficient structural condition is a **coarse/block-anchored** gauge whose restriction is the coarse identity.

The next configuration-space theorem is therefore not another generic quotient record; it is the construction of the actual selected coarse-anchored section and the proof that it presents the same Bałaban variational fibre.

## 10. Finite RG connected observable reopening

`BalabanFiniteRGObservableReopeningExact` proves exact finite disintegration/reopening:

\[
\mathbb E_{\mu_j}[O]
=
\mathbb E_{\mu_{j+1}}[\mathcal T_jO].
\]

It also handles composite observables without factorization.

`BalabanFiniteRGTotalCovarianceExact` now proves the exact law of total covariance:

\[
\boxed{
\operatorname{Cov}_{\mu_j}(X,Y)
=
\operatorname{Cov}_{\mu_{j+1}}
  (\mathbb E[X\mid C],\mathbb E[Y\mid C])
+
\mathbb E_{\mu_{j+1}}
  [\operatorname{Cov}(X,Y\mid C)].
}
\]

The diagonal specialization gives total variance:

\[
\operatorname{Var}(X)
=
\operatorname{Var}(\mathbb E[X\mid C])
+
\mathbb E[\operatorname{Var}(X\mid C)].
\]

This is a real algebraic bridge to the later mass-gap route: an RG step decomposes connected correlation into a coarse correlation plus a residual fibre correlation. The all-scale statement still has to prove that the residual covariance contracts with constants uniform in cutoff and volume.

## 11. Revised immediate Gate-I frontier

The finite Green and reduced multiplier algebra are no longer the blockers. The shortest local path is now:

```text
construct selected coarse/block-anchored configuration gauge section
  -> prove selected nonlinear block-average fibre preservation
  -> prove physical variational-orbit equivalence
  -> prove tangent of selected constraint manifold = kernel of L_A
  -> prove actual constrained minimizer / first variation annihilates tangent
  -> obtain KKT / projected Euler-Lagrange on the physical tangent space
  -> produce literal signed W-local / owner bounds for the same minimizer
  -> consume existing selectedBackgroundLiteralHessianOneThirtySecond
  -> freeze Gate I.
```

A concrete normal projector may be useful, but the physical invariant is `ker L_A`; equality of a particular projector matrix is not itself the target. The raw 780 Gram remains singular, while the fixed mean-zero reduced presentation has a strict normal floor but still needs the physical tangent-equivalence theorem before being treated as the final nonlinear constraint quotient.

## 12. Frontier after Gate I

After local closure, essentially all research weight should move to a proof-bearing

```text
YM4ScaleUniformRG
```

which must simultaneously establish small-field induction, fluctuation covariance control, large-field suppression, polymer-norm contraction, asymptotically-free running with controlled remainder, local observable transport, gauge-Jacobian/orbit-volume control, and constants uniform in cutoff and volume.

The preferred downstream route is then

```text
YM4ScaleUniformRG
  -> continuum gauge-invariant Schwinger functions
  -> OS hypotheses on those same functions
  -> physical-unit exponential clustering with m_G > 0
  -> OS reconstruction / spectral theorem
  -> Hamiltonian spectrum has no spectrum in (0,m_G)
  -> compact-simple-group scope.
```

The finite covariance identity above is one algebraic component of this route. It does not prove the scale-uniform contraction needed to close it.

## 13. Source provenance

The load-bearing Agda headers in this continuation cite, as appropriate:

- Tadeusz Bałaban, *Averaging Operations for Lattice Gauge Theories*, DOI `10.1007/BF01211042`;
- Tadeusz Bałaban, *Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing Conditions*, DOI `10.1007/BF01466594`;
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`;
- Tadeusz Bałaban, *The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories*, DOI `10.1007/BF01229381`;
- Tadeusz Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories. I*, DOI `10.1007/BF01215223`;
- J. M. Combes and L. Thomas, *Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger Operators*, DOI `10.1007/BF01646473`;
- Roger A. Horn and Charles R. Johnson, *Matrix Analysis*, DOI `10.1017/CBO9781139020411`;
- Tosio Kato, *Perturbation Theory for Linear Operators*, DOI `10.1007/978-3-642-66282-9`;
- Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, DOI `10.1007/978-3-319-13467-3`;
- Franco Brezzi, *On the Existence, Uniqueness and Approximation of Saddle-Point Problems Arising from Lagrangian Multipliers* (1974; no DOI assigned to the cited article);
- P. K. Mitter, *The Exact Renormalization Group*, arXiv `math-ph/0505008`.

## Validation boundary

The cumulative Round-42 root imports the split multiplier, reduced floor/injectivity, block-average compatibility and total-covariance modules. The extension checker cascades the prior checker, scans the transitive in-repository Agda dependency graph for holes/postulates/unsafe/trust/function-extensionality escapes, checks theorem/provenance markers, and invokes the pinned Agda 2.9 checker.

Both self-hosted Round-42 workflows are restricted to trusted branch pushes; pull-request checkout content is not executed on the shared self-hosted runner, and checkout credentials are not persisted.

Source-level `ProofLevel = machineChecked` markers are metadata, not evidence of an observed compiler run. `vacuumOrthogonalMoscoRecoveryLevel` is intentionally kept `conditional` until a pinned cumulative kernel run is actually observed. No successful Agda-kernel claim should be made without such an observable run, and none of the genuinely open four-dimensional RG/continuum/Clay theorems is promoted by this finite tranche.

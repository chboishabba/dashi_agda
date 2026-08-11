# Yang–Mills Round 42 — finite reopening and quotient closure

This note supersedes the earlier Round-42 statement that the selected-background Green still required a Neumann-limit/completeness bridge.  The current branch instead closes the finite reopening algebraically and records the remaining quotient boundary precisely.

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

Thus the unweighted reopening has norm bound `10/9`, the weighted reopening has norm bound `6/5`, and the homogeneous equation has zero norm.  A complete finite selector upgrades zero norm to pointwise zero, so `I+R_A` and its weighted conjugate are pointwise injective.

`BalabanFiniteRationalInjectiveInverseExact` isolates only the standard finite-dimensional field theorem

```text
finite square injective rational matrix => rational inverse
```

as imported linear algebra.  No Yang–Mills estimate is hidden in that authority.

## 2. The literal perturbation and residual are now same-object identities

`BalabanSelectedBackgroundGaugePerturbationActionExact` proves that the literal finite matrix

\[
K_A-K_0
\]

used by the absolute-mass estimates acts exactly as the three-term operator perturbation

\[
E_A=L_0D_A^*+D_AL_0^*+D_AD_A^*
\]

used in

\[
K_A^{\rm reg}=K_0^{\rm reg}+E_A.
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

and obtains the fixed-side-four kernel bound

\[
\boxed{
|G_A(x,y)|\le 3\,w(x,y).
}
\]

This is the local Gate-I exponential-decay theorem.  It is not a substitute for the later scale-uniform physical decay required in the continuum RG construction.

## 4. A concrete provenance-bearing based path gauge section

`BalabanBasedPathGaugeSectionExact` chooses a rooted path to every site and defines the gauge function by path transport from the base.  The resulting transformed field has unit transport on every selected rooted path.  The construction returns the actual gauge arrow together with the representative.

A second theorem proves uniqueness inside this rooted slice: a based gauge arrow between two rooted representatives is the identity at every site, hence the representatives agree bondwise.

This closes finite based-slice existence and uniqueness for the ordinary gauge action.  It deliberately does **not** yet prove preservation of the selected nonlinear Bałaban block-average constraint.  That compatibility is still the load-bearing theorem needed to identify this computational section with the selected variational orbit.

## 5. The raw 780-row combined Gram is not universally invertible

A useful no-go emerged while constructing the tangent projector.  The literal combined constraint has 12 block-average rows and all 768 gauge rows.  At the identity background, take a multiplier that is zero on every block-average row and constant nonzero on every gauge row.  The actual flat gauge adjoint is the negative periodic gradient, so it kills that constant multiplier.  Therefore the full combined transpose kills this nonzero multiplier, and hence

\[
(L_0L_0^*)\lambda=0,
\qquad
\lambda\ne0.
\]

`BalabanSelectedCombinedConstraintRawGramNoGoExact` formalizes this witness and proves that the raw flat 780-row Gram has no two-sided rational inverse.

This rules out a dangerous shortcut.  The universal physical tangent projector cannot be constructed by blindly writing

\[
I-L_A^*(L_AL_A^*)^{-1}L_A
\]

on the unreduced 780-row carrier.  `BalabanSelectedCombinedConstraintTangentProjectorExact` proves the formula only conditional on an actually invertible carrier, and `BalabanSelectedCombinedConstraintTangentProjectorBoundaryExact` records that this condition fails on the raw flat carrier.

The live route is now explicit: remove the gauge redundancy on a based/reduced carrier, or construct an equivalent quotient-aware normal projector, before inversion.

## 6. Finite RG reopening / observable transport

`BalabanFiniteRGObservableReopeningExact` implements the finite algebra suggested by the wider quotient/reopening discussion.  An RG step carries a coarse projection together with a conditional reopening kernel `kappa`.  Exact disintegration implies

\[
\mathbb E_{\mu_j}[O]
=
\mathbb E_{\mu_{j+1}}[\mathcal T_jO],
\qquad
(\mathcal T_jO)(y)
=
\sum_x\kappa_j(y,x)O(x).
\]

The same statement is proved for composite observables without assuming factorization.  This is the finite provenance theorem needed so that later RG steps can transport the same gauge-invariant observable family instead of preserving only the partition function.

It does **not** prove the genuine open four-dimensional all-scale estimates: small-field closure, large-field suppression, polymer-norm contraction, asymptotically-free running, locality of transported observables, or cutoff/volume-uniform constants.

## 7. Immediate local frontier

The shortest remaining Gate-I path is now:

```text
selected block-average compatibility of a based/reduced gauge section
  -> selected based/reduced normal carrier
  -> physical tangent = kernel theorem on that carrier
  -> constrained stationarity / projected Euler–Lagrange
  -> literal coupled Wilson/gauge lower producer
  -> consume the existing H_A >= 1/32 endpoint
  -> freeze Gate I.
```

The raw-full-Gram route is formally ruled out, so effort should not be spent trying to repair it by assuming away the flat constant gauge modes.

After this local closure, the dominant mathematical target remains one proof-bearing `YM4ScaleUniformRG` producer, followed by continuum Schwinger functions/OS axioms, physical-unit clustering and Hamiltonian gap transfer, nontriviality/asymptotic freedom on the same observable family, and compact-simple-group scope.  None of those frontier theorems is asserted by this Round-42 finite tranche.

## 8. Source provenance

The load-bearing Agda headers in this continuation cite, as appropriate:

- Tadeusz Bałaban, *Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing Conditions*, DOI `10.1007/BF01466594`;
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`;
- Tadeusz Bałaban, *The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories*, DOI `10.1007/BF01229381`;
- J. M. Combes and L. Thomas, *Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger Operators*, DOI `10.1007/BF01646473`;
- Roger A. Horn and Charles R. Johnson, *Matrix Analysis*, DOI `10.1017/CBO9781139020411`;
- Tosio Kato, *Perturbation Theory for Linear Operators*, DOI `10.1007/978-3-642-66282-9`;
- Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, DOI `10.1007/978-3-319-13467-3`;
- P. K. Mitter, *The Exact Renormalization Group*, arXiv `math-ph/0505008`.

## Validation boundary

The cumulative Round-42 root and extension checker import/guard this tranche and reject holes, local postulates, unsafe/trust escapes, and function-extensionality shortcuts.  Source-level `ProofLevel = machineChecked` markers are metadata, not evidence of an observed compiler run.  A successful Agda-kernel claim is to be made only after an actual pinned Agda 2.9 workflow/typecheck completes.
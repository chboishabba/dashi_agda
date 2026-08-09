# Round 40 — selected multiplier locality and correlated singleton closure

Round 40 continues the redundancy-safe KKT algebra of Round 39.  It does not add another projector abstraction.  It makes the remaining Gate-I object explicit:

\[
\delta_{p,h}=L_Aw_{p,h},\qquad
\lambda_0=K_A^+L_Ag_A,\qquad K_A=L_AL_A^*.
\]

The spillover is the collar-local Green contraction

\[
\langle\lambda_0,\delta_{p,h}\rangle
 =\langle L_Ag_A,K_A^+L_Aw_{p,h}\rangle.
\]

## Sign audit

The repository's literal projector algebra is

\[
dS(Pw)=dS(w)-dS((I-P)w),
\]

and the raw extractor convention is

\[
dS(w)=\operatorname{Singleton}+\operatorname{RawLocalization}.
\]

Round 39 proves

\[
dS((I-P)w)=\langle\lambda,Lw\rangle.
\]

Therefore the unique generated projected residual is

\[
\boxed{\operatorname{RawLocalization}-\langle\lambda,Lw\rangle}.
\]

At stationarity,

\[
\boxed{\operatorname{Singleton}
 =-\operatorname{RawLocalization}+\langle\lambda,Lw\rangle}.
\]

The previously displayed expression
`-RawLocalization - <lambda,Lw>` does not follow from the selected-variation decomposition.  `BalabanSelectedVariationSignConventionExact.agda` makes the sign chain public and proves that equality with the double-negative expression would force twice the multiplier pairing to vanish.

## Redundancy and collar support

`BalabanSelectedMultiplierPairingRedundancyInvariantExact.agda` proves

\[
r\in\ker L^*\Longrightarrow \langle r,Lw\rangle=0.
\]

Hence all KKT multiplier representatives give exactly the canonical Moore–Penrose defect pairing.

`BalabanSelectedConstraintCollarPairingExact.agda` proves that any row whose literal stencil misses the plaquette boundary contributes zero, and therefore

\[
\langle\lambda,\delta_{p,h}\rangle
 =\langle\chi_{\mathcal C(p)}\lambda,\delta_{p,h}\rangle.
\]

A multiplier supported outside the collar annihilates the defect exactly.

## Constraint-Gram Combes–Thomas route

The first decay target is the smaller local operator

\[
K_A=L_AL_A^*.
\]

`BalabanSelectedConstraintGramCombesThomasExact.agda` exposes the literal finite-range certificate, diagonal tilt, row-mass budget and kernel untwisting theorem.  `BalabanSelectedKKTMultiplierLocalityExact.agda` then converts a weighted Green-row estimate and a localized source bound into

\[
|\lambda_0(x)|\le M_sR_Kw(x)
\]

and an exact collar `L1` bound.

The full saddle block remains represented locally as

\[
\mathcal K_A=\begin{pmatrix}H_A&L_A^*\\L_A&0\end{pmatrix}.
\]

`BalabanP33FiniteKKTBlockCombesThomasConstantsExact.agda` names the complete quantitative inputs

- `selectedKKTInverseNormUpper`,
- the separate weighted row masses of `H`, `L*` and `L`,
- `selectedKKTInteractionRange`,
- `selectedKKTAdmissibleTilt`,
- and the half-contraction inequality
  \(C_K(S_H+S_{L^*}+S_L)\le 1/2\).

It yields the explicit tilted-inverse majorant `2 C_K` and the standard untwisted off-diagonal estimate once the physical constants are supplied.

## Genuine finite KKT inverse

Round 39 constructed a right inverse.  `BalabanP33FiniteKKTBlockInverseExact.agda` proves the missing implication:

1. homogeneous constraint equation gives `Lv=0`;
2. adjoint pairing cancellation gives \(\langle v,Hv\rangle=0\);
3. coercivity on `ker L` gives `v=0`;
4. reduced adjoint injectivity gives `mu=0`;
5. the block is injective, so the right inverse is also a left inverse.

The resulting authority is `finiteKKTBlockInverseExact`.

## Common Boolean basis and delayed majorisation

`BalabanSelectedRawExtractorConstraintDefectAtomsExact.agda` reconstructs both

\[
s_A=L_Ag_A,\qquad \delta_{p,h}=L_Aw_{p,h}
\]

from the same fifteen nonempty subsets of the four Wilson factors.

`BalabanSelectedCorrelatedResidualOwnershipExact.agda` uses the pair carrier

\[
(S,T,\text{orbit tag},\text{orientation},\text{collar displacement},\text{owner})
\]

for the Green term.  It aggregates

\[
\sum_S r_S-\sum_{S,T}\langle s_S,K_A^+\delta_T\rangle
\]

by owner, removes the exact-cancellation owner, and only then applies positive upper bounds to the four surviving owner totals.

## Generated coefficient optimization

`BalabanP33PhysicalSingletonBudgetOptimizationExact.agda` replaces the old feasibility-only `27+28=55` witness by a generated optimization certificate containing

- `physicalParameterAssignment`,
- `rawLocalizationCostExact`,
- `multiplierDefectCostExact`,
- `singletonTotalCostExact`,
- global minimality in the declared candidate family,
- `singletonTotalBelowBudget`.

It also defines a dual no-fit certificate.  The exact rational producer is `scripts/ym_round40_singleton_budget_optimize.py`; decimal inputs are rejected and a no-fit result exits nonzero.

The committed JSON fixture is a checker regression only and is explicitly marked synthetic.  It is not a physical coefficient claim.

## D4 and coefficient-field audits

`BalabanP33ConstraintGramD4CovarianceExact.agda` requires covariance of `L`, `L*`, `K` and `K+`, together with invariance of the multiplier dot product, before a Green-pairing orbit reduction is accepted.

`BalabanSelectedBackgroundCoefficientFieldExact.agda` separates the literal selected-background coefficient field from its rational specialization.  A rational frame is authoritative only after every selected constraint and frame entry is exhibited as the image of a rational.

## Terminal reducer

`BalabanSelectedCorrelatedSingletonClosureExact.agda` builds the existing physical `SingletonExtractionWitness` from the corrected-sign correlated residual.  It proves the exact singleton budget and reuses the already closed pair/deep channel to produce the correlated Wilson lower bound.

## Exact remaining physical producers

The algebraic lane is closed only conditionally on these selected-background data:

1. literal Boolean atoms for `L_Ag_A` and `L_Aw_{p,h}`;
2. exact owner cancellation and the four surviving owner estimates;
3. the generated physical optimization certificate below `55/18874368`;
4. the selected constraint-Gram finite-range stencil and reduced spectral floor;
5. the Gram and full-KKT tilt row masses and inverse norm;
6. reduced Hessian coercivity and reduced multiplier-adjoint injectivity;
7. D4 covariance of the selected pseudoinverse;
8. literal coefficient-field/rationality authority for the selected background.

No finite Hessian or KKT decay theorem is promoted to an Osterwalder–Schrader Hamiltonian mass gap without the separate uniform RG, clustering, continuum-limit, OS-reconstruction and spectral-transfer bridges.

## Sources

- Tadeusz Bałaban, *Averaging Operations for Lattice Gauge Theories*, Communications in Mathematical Physics 98 (1985), 17–51. DOI: `10.1007/BF01211042`.
- Tadeusz Bałaban, *The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories*, Communications in Mathematical Physics 102 (1985), 277–309. DOI: `10.1007/BF01229381`.
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, Communications in Mathematical Physics 99 (1985), 389–434. DOI: `10.1007/BF01240355`.
- J. M. Combes and L. Thomas, *Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger Operators*, Communications in Mathematical Physics 34 (1973), 251–270. DOI: `10.1007/BF01646473`.
- Roger Penrose, *A Generalized Inverse for Matrices*, Proceedings of the Cambridge Philosophical Society 51 (1955), 406–413. DOI: `10.1017/S0305004100030401`.
- Franco Brezzi, *On the Existence, Uniqueness and Approximation of Saddle-Point Problems Arising from Lagrangian Multipliers*, RAIRO Analyse Numérique 8 (1974), 129–151. No DOI assigned.
- Gian-Carlo Rota, *On the Foundations of Combinatorial Theory I. Theory of Möbius Functions*, Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte Gebiete 2 (1964), 340–368. DOI: `10.1007/BF00531932`.

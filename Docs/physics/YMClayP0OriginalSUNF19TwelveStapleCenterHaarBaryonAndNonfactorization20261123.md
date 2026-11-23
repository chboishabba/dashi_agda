# YM P0 — original 12-staple F19 SU(N) continuous-Haar centre-charge series, exact SU(3) signed baryon and nonfactorizing pair history

23 November 2026. **Original four-dimensional SU(N) Wilson source, mass gap P0.** This extends (and does **not** rederive) the actual twelve-staple matrix external-field reduction in `YMClayP0OriginalF19ContinuousHaarPairTSource20261123.md`, the original full F19 64 ordered-pair / 896 interacting-spectator conditional Haar theorem, and the original two unique globally inserted 1/F/G/FG Wilson marks. This is a genuine analytic **continuous SU(N) Haar-integral** theorem for one original F19 pair, plus an original-action counterexample to replacing the next pair by an independent copy. It is NOT the fully localized/gauge-constrained Bałaban CMP119/122 T and does not discharge any physical CMP116 individual absolute connected-shell charge, E1/OS or same-H gap.

## 1. The exact original one-pair source, already owned

At original L=4 with 1024 positive fine SU(N) links and 1536 actual positive plaquettes, choose one of the original 64 consecutive axial F19 pairs, set `V=U1` and the true coarse holonomy `W=U0 U1`, reconstruct `U0=W V^{-1}`. At fixed W, fixed other 63 pairs and all 896 interacting spectator links, exactly 12 original plaquettes touch this pair, no original plaquette contains both pair links. In the already-constructed source owner, the full actual original Wilson deficit action has the identity

\[
S_{\rm Wilson}(V)=C-\frac1N\operatorname{ReTr}(H V),\qquad
C=\sum_{p\text{ among 1524 untouched}}d_p+12,\quad
H=\sum_{p\text{ among 12 touched}} H_p,\quad
\|H\|_{\rm op}\le12,
\]

with all `H_p ∈ SU(N)` determined by the **original** W and surrounding Wilson links; `d_p=1-ReTr(U_p)/N`. The exact positive continuous compact Haar one-fibre integral is

\[
\boxed{T_0=e^{-\beta C}\mathcal Z_N(H;\beta),\qquad
\mathcal Z_N(H;\beta)=\int_{SU(N)}\exp\!\left[\frac\beta N\operatorname{ReTr}(HV)\right]dV.}
\]

There is no arbitrary independent twelve-staple model: every H_p comes from one **original** native face word, all 1524 remaining Wilson action terms remain in C. The one-pair conditional is genuinely continuous SU(N) Haar. This step alone does not integrate the other 959 source variables, identify Bałaban's constrained physical T, or remove their interactions.

## 2. NEW all-rank source-exact centre-charge decomposition and positive analytic convergence

Define original compact-group moments

\[
I_{k,l}^{(N)}(H)=\int_{SU(N)}(\operatorname{Tr}HV)^k
  (\operatorname{Tr}V^\dagger H^\dagger)^l\,dV.
\]

Taylor-expand the same **original** positive one-fibre Wilson integral, absolutely and uniformly in V for fixed finite beta. Because `zeta I∈Z(SU(N))` acts by `V→zeta V` and Haar is invariant,

\[
\boxed{I_{k,l}^{(N)}(H)=0\quad\text{whenever }k-l\not\equiv0\pmod N.}
\]

This is the exact **all-N baryon/antibaryon centre-charge selection rule**. It yields the ORIGINAL F19 conditional T, with no new gauge field or coupling:

\[
\boxed{\mathcal Z_N(H;\beta)
 =\!\sum_{\substack{k,l\ge0\\k-l\equiv0\ (\mathrm{mod}\ N)}}
 \frac{(\beta/2N)^{k+l}}{k!l!}\,I_{k,l}^{(N)}(H).}
\]

Absolute convergence is immediate from `|Tr(HV)|≤12N`; at order M (total k+l≤M) the **true** compact-Haar remainder is bounded, for all beta≥0, by

\[
\boxed{\bigl|\mathcal Z_N-\mathcal Z_N^{[M]}\bigr|
 \le e^{12\beta}\frac{(12\beta)^{M+1}}{(M+1)!}.}
\]

For each original marked **deficit** column (bounded 0≤F,G≤2), its Taylor remainder is bounded by 2 times this amount, and for FG by 4 times; multiply by the actual `e^{-βC}` if including the complete fixed-background original Wilson density. These are honest finite-beta convergent source T approximations, *not a weak-coupling activity bound*: the `e^{12β}` envelope degenerates along beta(a)→∞ and gives no cutoff-uniform W3 contraction.

The standard SU(N) epsilon invariant gives `I_{N,0}(H)=det H` and `I_{0,N}(H)=conj(det H)`; hence the first rank-dependent **unbalanced baryon+antibaryon** source term at degree N is

\[
\boxed{\frac{2}{N!}\left(\frac\beta{2N}\right)^N\operatorname{Re}\det H.}
\]

The complete degree N coefficient also includes balanced meson terms when N is even, so **never call the full order-N coefficient just baryonic**. The first universal balanced moments are

\[
I_{1,1}(H)=\frac{\operatorname{Tr}(HH^\dagger)}N,
\quad
I_{2,2}(H)=\frac2{N^2-1}\left[(\operatorname{Tr}HH^\dagger)^2
  -\frac1N\operatorname{Tr}((HH^\dagger)^2)\right].
\]

These follow from the classical unitary Haar/Schur–Weyl–Weingarten two-pair contraction, which applies unchanged to equal holomorphic/antiholomorphic degrees on SU(N). Classical source provenance: Weyl integration and epsilon tensors; Collins–Śniady, *Integration with Respect to the Haar Measure on Unitary, Orthogonal and Symplectic Group* (arXiv:math-ph/0402073), rather than a novel all-group Haar formula attributed to DASHI.

## 3. NEW original F19 SU(3) spectator configuration: first baryon changes sign

Choose the **actual** original R445 y-pair with positive links `U0=(0,0,0,0; y)` and `U1=(0,1,0,0; y)` and **actual** coarse W=I. The original face enumeration identifies twelve distinct positive y-parallel *spectator* links, one opposite to the selected variable in each of the twelve touched faces (each is transverse-odd and remains one of the original 896 spectators). All other 884 spectators and the other 63 original F19 pairs may be fixed to identity for this conditional slice without changing the original source measure definition. The twelve spectator controls can be set independently to SU3 central matrices so that the six original faces incident on U0 produce coefficients `I`, and the six faces incident on U1 produce coefficients `ωI`, `ω=e^{2πi/3}`; the orientation-dependent inverse is correctly handled by using `ω²` on the opposite U1 spectator links. This is a **literal original native 1536-face configuration**, not twelve free fitted staple matrices. The actual untouched-face Wilson action stays in C.

Consequently the actual positive SU3 conditional Wilson one-pair source has `H=6(1+ω)I`, `|6(1+ω)|=6`, `det H=-216`. Compare the original all-identity coherent exterior `H=12I`, `det H=1728`.

Independent **exact continuous SU(3) Haar** integration (not centre-subgroup Haar): using the standard SU3 Weyl torus with `z1,z2,z3=(z1 z2)^-1` and normalized Laurent Vandermonde

\[
\int_{SU(3)}f(V)dV
=\frac1{3!}\operatorname{CT}_{z_1,z_2}
\bigg[f(\operatorname{diag}z)\prod_{i<j}(1-z_i/z_j)(1-z_j/z_i)\bigg]
\]

for class functions (the present central H gives one), the genuine two conditional source factors have:

\[
\begin{aligned}
\boxed{\mathcal Z_3(12I;\beta)}
  &=1+4\beta^2+\tfrac83\beta^3+8\beta^4+O(\beta^5),\\
\boxed{\mathcal Z_3(6(1+\omega)I;\beta)}
  &=1+\beta^2-\tfrac13\beta^3+\tfrac12\beta^4+O(\beta^5).
\end{aligned}
\]

**The cubic baryonic coefficient flips sign `+8/3 ↔ -1/3` on two legitimate original Wilson exterior configurations, while the FULL original conditional Boltzmann integrand remains positive at every real beta.** Thus a source proof cannot assign nonnegative **individual baryonic signed coefficients** simply because the Wilson measure is positive. This is an all-continuous-Haar, actual-original-plaquette stronger negative control than earlier SU2 Q8 centre-only checks. It is *not* a claim that a selected Bałaban CMP116 **absolute** baryonic cluster activity is negative; that activity has not yet been source-identified.

## 4. The globally unique original F/G mark: source directional derivative is also explicit

The chosen original y/z plaquette mark F at time zero touches the U0 of this pair. In the original central exterior it is **the actual native deficit** `F(V)=1-ReTr(V)/3`, not a new observable. By differentiating the SAME one Wilson source in the coefficient direction `I`, for beta>0,

\[
\boxed{T_F=e^{-\beta C}\left[\mathcal Z_3(H;\beta)
 -\frac1\beta\,D_I\mathcal Z_3(H;\beta)\right].}
\]

The limit beta→0 exists. For the original reduced marked factor (dividing out the unchanged `e^{-βC}`), the **exact continuous Haar** coefficients are

\[
\begin{aligned}
T_F(12I)e^{\beta C}&=1-\tfrac23\beta+\tfrac{10}3\beta^2+0\beta^3+O(\beta^4),\\
T_F(6(1+\omega)I)e^{\beta C}&=1-\tfrac16\beta+\tfrac{13}{12}\beta^2-\tfrac12\beta^3+O(\beta^4).
\end{aligned}
\]

Both calculations keep F in the actual original action AND insert it once as the differentiated source column. Original remote G is constant at this fixed one-pair step, so `T_G=G_const T0`, `T_FG=G_const T_F`. This **local** factorization does NOT survive unchanged through the 896 interacting spectators and 63 other pair fibres; the original global F/G covariance need not vanish. No artificial independent F/G marks or direct identification with Bałaban T are introduced.

## 5. NEW exact full 4D nonfactorization theorem: the next F19 pair DOES NOT remain an independent twelve-staple T

Take two true R445 native even-origin pairs in **different y and z axes from the same original x=(0,0,0,0)**, both coarse W_y=W_z=I, freeze the other **1020** original positive links to I and vary one true compact-SU(N) Cartan matrix for each pair,

\[
V_y=\operatorname{diag}(e^{i\theta},e^{-i\theta},1,\ldots),\quad
V_z=\operatorname{diag}(e^{i\phi},e^{-i\phi},1,\ldots),
\]

with the first fine link in each native pair `U0=V^{-1}` and second `U1=V`. Direct original 1536-face Wilson enumeration finds **1513 untouched plaquettes, 11 touched only by the y pair, 11 only by the z pair and precisely ONE shared original y–z plaquette** at x. The actual full original Wilson deficit action is *exactly*

\[
\boxed{S_N(\theta,\phi)=\frac2N\left[11(1-\cos\theta)+11(1-\cos\phi)
   +(1-\cos(\phi-\theta))\right].}
\]

Hence

\[
\boxed{\left.\frac{\partial^2S_N}{\partial\theta\partial\phi}\right|_{0,0}
  =-\frac2N\ne0.}
\]

The source integrand CANNOT be a product of two functions, one of `V_y` and one of `V_z`, because its mixed log/action Hessian is nonzero. **One original twelve-staple Haar integral may be taken exactly, but the resulting effective action for the second pair contains its induced connected interaction.** Multiplying independent single-pair Bessel/Haar factors or classifying the 64 original pairs as independent CMP119 disjoint components is mathematically false on the genuine original Wilson source. The original CMP119 factorized (2.18–2.22) domain/residual and ordered constrained T history may still represent the correct interaction; its source-dependent residual and boundary variables must be identified instead of set to unity.

This holds for **all N>=2**, all six orientation pairs by the same source enumeration, and all positive bare beta; the above Cartan family is a deterministic **witness of nonseparability**, not an interacting continuum YM mass and not a replacement for spatial source cluster estimates.

## 6. Executed strict independent acceptance and next endpoint

[Full exact checker](../../scripts/check_ym_p0_sun_original_12staple_haar_center_baryon_20261123.py): **1,838/1,838 PASS**. It exhaustively creates original L4 1024-link/1536-plaquette words; verifies twelve distinct authentic spectator controls and their source phases, all three central V original-word trace reductions, continuous SU2/SU3/SU4 **Weyl–Haar** Laurent constant-term moments (k+l≤6), all-rank group centre filter, normalized `I11=1`, `IN0=1`, `I22=2` for H=I, original SU3 two real source expansions, exact original-F deficit marked directional derivatives, SU2 Bessel sixth-order reference, and **six native original two-pair overlapping orientations** with mixed Cartan Hessian `-2/N` for N=2,3,4,5,8. Weyl constant-term integration is exact for these class-function fixtures, not numerical Monte Carlo and not a finite discrete subgroup substitution. Full analytic all-H theorem uses the standard SU(N) Haar invariant tensor identities; local executable tests special source H central fixtures.

**Source trust:** this file proves source mathematics with classical compact-group Haar integration and existing full-original Wilson geometry. No Agda kernel/CI, no true full 960-variable Haar integration, no selected CMP98/109 nonlinear averaging or CMP119 Omega/Lambda/S (S INSIDE T), no CMP122 Eq1.71 constrained/gauge-fixed FP/Jacobian R/E/R/B/V interpretation, no cutoff-uniform rooted **termwise absolute** CMP116 two-mark spatial activity, and no noncollapsed interacting E1/D2/N1/G1 same-H mass gap. Avoid confusing positive Wilson Gibbs density with positivity of each centre-charged coefficient or original 64-pair Haar Fubini with 64 independent marked T factors.

**P0 MAX-CUT AFTER THIS RESULT:** use the exact all-N centre-resolved *one-pair* external-field source as the nontrivial physical boundary test of any proposed CMP119/122 **genuinely localized constrained** T. It must reproduce the original meson+baryon source coefficients and their marked directional jets for the actual original one-fibre exterior, and maintain the y–z nonfactorizing shared plaquette through selected histories and residuals. Then derive *true* original renormalized **individual absolute mixed-marked connecting cluster activities**, preserving SU(N) centre/baryon signs, and a cutoff-/volume-uniform positive physical shell rate. Only then invoke already-existing CMP116, E1/OS and same-H D2 consumers. Existing Biskup/FILS RP, original signed Wilson/Haar and Bałaban/KP sources retain proper provenance.
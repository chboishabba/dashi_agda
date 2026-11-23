# YM P0 / W3 — exact first restoration shell of the original SU(N) two-mark tube

23 November 2026. Original periodic four-dimensional Wilson link/plaquette source; `master`-based extension. This is a mathematical finite-source step, **not** the full 4D homogeneous Wilson W3 estimate, CMP119/122 physical `T` identification, Agda kernel receipt, or a mass-gap theorem.

## Original physical indices and signed source

For `L >= 3`, choose a native periodic `L^4` SU(N) lattice with `4L^4` positively oriented links and `6L^4` positive plaquettes. Fix an oriented spatial plane `a<b`, a native time separation `1<=d<L`, and original Wilson marks `H_0=F=t(P_{(0,0,0,0);a,b})`, `H_d=G=t(P_{(d,0,0,0);a,b})`, where `t(U)=ReTr(U)/N`. Let `T_d` consist of the `4d` original (time,spatial)-plane walls of the `1 x 1 x d` prism. Introduce every genuine original intermediate spatial plaquette `H_k=t(P_{(k,0,0,0);a,b})` for `0<=k<=d`.

All original links and plaquettes remain on their original four-dimensional carrier. The reference measure `mu_0` couples only the native wall faces, with arbitrary finite wall couplings `beta_q`. The interpolation to homogeneous Wilson at common coupling `beta` adds the remaining `6L^4-4d` faces at weight `tau*beta`, including both caps and intermediate spatial sections. This time index is native Euclidean time, NOT RG scale or a hyperfabric index.

Write
\[
z_N(b)=\int_{SU(N)}e^{b t(U)}dH(U),\qquad
m_N(b)=z_N'(b)/z_N(b),\qquad
v_N=\int t^2dH,\qquad h_N=\int t^3dH.
\]
As in the established original all-beta wall-only surface contraction, set `M_T=prod_{q in T_d} m_N(beta_q)`. The wall-only two-mark covariance is `v_N M_T`.

## A. Exact original 4D incidence/leaf census

The union of the `4d+2` faces `T_d ∪ {H_0,H_d}` uses precisely `8d+4` native links, each incident to two selected faces. Every *other* native plaquette `p` satisfies exactly one of the following:

1. `p=H_k` for some `1<=k<d`. Its four boundary links are already in the tube edge support.
2. `p` is not a spatial cross-section. At least one of its four native boundary links is **absent** from the entire tube edge support.

Thus among restored source plaquettes `p notin T_d`, precisely the `d+1` cross-sectional plaquettes lack an external link-Haar leaf. This includes **the interior section**, not merely the two marked caps.

The native-exhaustive Python checker enumerates *all* `6L^4` original source plaquettes, not just a heuristic tube candidate set. It passes `L=3,4,5,6`, all `1<=d<L`, and all three spatial planes: **42/42 distinct source geometries**. In the original `L=4,d=2` source, `3` of the `1528` restored faces are cross-sections; the remaining `1525` have a link absent from the selected tube.

For such an off-section `p`, the Haar integral of every moment containing `t_p` and any combination of `F,G` is zero under `mu_0`: that external link occurs in `t_p` but no existing wall exponential or mark. This is exact *for arbitrary finite wall couplings*; it does **not** hold when the other spectator interactions are switched on at `tau>0`.

## B. Exact continuous-SU(N) original tube transfer and triple source

Using the standard axial/tree gauge elimination on the **embedded original** 2D tube face complex (not substituting a physical 2D YM theory), the original class-function slice holonomies `H_k` admit an open-chain transfer representation. The slice at one end is Haar-distributed; four actual wall plaquettes per time step act as central-convolution increments. Conjugation invariance gives
\[
\int_{SU(N)} U\,z_N(b)^{-1}e^{bt(U)}dH(U)=m_N(b)I_N.
\]
Consequently the normalized class-function transfer on `t` has eigenvalue `r_j=prod_{q in four walls at time j}m_N(beta_q)`; it is time-reversal symmetric because `t(U^{-1})=t(U)`. Therefore each slice has Haar marginal, `E_{\mu_0}H_k=0`, and for `0<=k<=d` (also valid at `k=0,d`)
\[
E_{\mu_0}[F G H_k]
= h_N \prod_{j=0}^{d-1} r_j
=h_N M_T.
\]
For `k` strictly between the caps this follows from conditional independence of the two chain segments given the middle slice; for the endpoint, integrate `F^2G` or `FG^2` using the same transfer eigenvalue. Because all first moments are zero, the triple expectation is already the connected third cumulant.

This is an analytic compact-group/transfer proof at finite lattice size, **not** an Agda kernel-verified proof of its non-Abelian gauge-fixing isomorphism. The checker separately verifies the three-section conditional-cumulant algebra and differentiated normalization on exact rational `Z_3`, and **also** independently evaluates the actual continuous SU(2)/SU(3) Haar moments through Weyl–Vandermonde Laurent constant-term extraction. The finite `Z_3` transfer is not a substitute for continuous SU(3) Haar; the SU(3) moment is checked directly by the Weyl integral.

## C. Exact SU(N) center/epsilon trilinear selection

For `N>=2`,
\[
v_N=\begin{cases}1/4&N=2\\1/(2N^2)&N>=3,\end{cases}
\qquad
h_N=\begin{cases}1/108&N=3\\0&N=2\text{ or }N>=4.\end{cases}
\]
For `N≠3`, center-charge selection annihilates all terms in `(TrU+TrU^\dagger)^3` (the only possible charges are `±1,±3`; for SU(2) the nontrivial center also kills the odd moment). For SU(3), the unique determinant/epsilon invariant gives `∫(TrU)^3dH=1` and its conjugate is 1; mixed charge terms vanish. Thus `h_3=2/(8*3^3)=1/108`. This is a known fundamental invariant-tensor identity, not inferred from the finite `Z_3` regression.

## D. Source W3 first-jet theorem and exact rooted sum **at tau=0 only**

Combining A–C gives the **pointwise native source third cumulant**
\[
\boxed{
\kappa_{\mu_0}(F,G,t_p)=
\begin{cases}
h_N M_T,&p\in\{H_0,H_1,\ldots,H_d\},\\
0,&p\notin T_d\cup\{H_0,\ldots,H_d\}.
\end{cases}}
\]
In particular
\[
\boxed{\sum_{p\notin T_d}|\kappa_{\mu_0}(F,G,t_p)|
=(d+1)|h_N|\prod_{q\in T_d}|m_N(\beta_q)|.}
\]
This is finite-volume-independent for the restricted-source starting measure; it does **not** imply the CMP116 two-mark absolutely summable *restored* activities or any `tau>0` rooted-shell estimate.

For common coupling `beta` on the walls and interpolation `tau*beta` on every other original plaquette, exact source Duhamel differentiation yields
\[
\boxed{
\left.\frac{d}{d\tau}\operatorname{Cov}_{\mu_\tau}(F,G)\right|_{\tau=0}
=\beta(d+1)h_N\,m_N(\beta)^{4d}.
}
\]
For the original `L=4,d=2`: **SU(3)** has slope `beta*m_3(beta)^8/36`, which is `beta/2` times the initial covariance `m_3(beta)^8/18`; **SU(2) and N>=4** have zero first slope, not a zero full remainder. All fixed-lattice finite-beta expectations are analytic in `tau`, hence their remainder starts at quadratic order in `tau` for those groups, without a uniform coefficient claim.

## E. Reverse-solve boundary: why this is not the full physical W3

The initial absolute activity is exact and exceptionally sparse, but restoring remote Wilson interactions removes the external leaf immediately. The order-`tau^2` and higher source moments can bridge spectators to the tube and contribute across arbitrary connected lattice polymers. Neither finite Taylor order nor the signed Duhamel equation bounds the full `0<=tau<=1` **absolute** connecting-cluster sum.

Even at `tau=0`, `m_N(beta)->1` as `beta->infty`, so the SU(3) first-shell absolute charge approaches `(d+1)/108`; the bare wall-only starting point supplies no weak-coupling continuum decay estimate. The physically required bound is on the same original full Wilson measure with scale `beta(a)`, full CMP119/122 `Omega/Lambda/S` constrained operation, original Jacobian/FP/background and E/R/B/V contributions, all large-field sectors, a cutoff/volume-uniform rooted-shell entropy budget and fixed physical time. Existing F19/W0 eight coefficients may transport source moments but **do not identify** that physical constrained `T`.

**Next honest P0 weld:** extract from the existing CMP119/122 source a marked *absolute* `tau`-dependent connected-activity decomposition that can be checked against this exact `tau=0` three-section boundary; prove its original Wilson/fine-F19 source identification and a uniform small+large-field bound. Then consume existing CMP116 → R556/R551/R552 on one reconstructed interacting OS Hamiltonian. E1/D1/D2/N1/G1 remain open.

## Evidence / trust

- Executed locally (Python/SymPy exact arithmetic): [original 4D shell census, independent finite transfer and continuous SU(2)/SU(3) Haar Weyl moments](../../scripts/check_ym_original_w3_first_restoration_shell_20261123.py), 42/42 lattice cases; exact rational derivative control passes; direct Weyl–Vandermonde constant-term integrals give SU(2) moments (1,0,1/4,0) and SU(3) moments (1,0,1/18,1/108). The committed compact checker retains the same algorithms, but its exact uploaded bytes were not separately executed.
- Original eight-wall baseline and full source restoration are on [YM #1536](https://github.com/chboishabba/dashi_agda/pull/1536); original CMP119/122/116 donor is [#1444](https://github.com/chboishabba/dashi_agda/pull/1444).
- The current branch was cut from the updated `master` rather than force-merging #1536's diverged history. The compact script in this branch is source-equivalent to the locally executed regression; it has not been byte-for-byte executed after GitHub upload.
- No Agda/Lean/CI, global Wilson W3, same-H spectral gap, or Clay theorem is claimed.


## F. Larger BIDI cut — exact SECOND restoration jet, original SU(2) L=4,d=2

The exterior-leaf mechanism persists through **two** restoration insertions, not merely one. The native 4D complete-link census shows every non-section plaquette has at least two boundary links outside the original tube support, for every tested L=3,4,5,6, every 1<=d<L and every spatial plane. On these periodic original lattices any two distinct positive-oriented plaquettes share at most one original link (checked exhaustively via link-to-face incidence, not assumed). Hence adding a *distinct* second restored plaquette cannot eliminate every exterior Haar leaf. If it is the **same** exterior plaquette repeated, its holonomy is already Haar-independent of the entire (F,G) pair under mu_0, so the *connected* fourth cumulant still vanishes.

Therefore, for the 1,528 restored original source faces of L4/d2, in the exact genuine full-source second variation
\[
\left.\partial_\tau^2\operatorname{Cov}_{\mu_\tau}(F,G)\right|_{\tau=0}
=\beta^2\sum_{p,q\notin T_2}\kappa_{\mu_0}(F,G,t_p,t_q),
\]
**all 1,528^2 = 2,334,784 ordered terms reduce to just 3^2 = 9 ordered section pairs**, and all 2,334,775 other terms are identically zero. This is a source-geometric statement at tau=0, not a bound on any later interpolation value.

For continuous SU(2), the original tube stationary class-function chain has exact four-wall transfer eigenvalues
\[
a=\left[\frac{I_2(\beta)}{I_1(\beta)}\right]^4
\quad(\text{fundamental spin }1/2),\qquad
b=\left[\frac{I_3(\beta)}{I_1(\beta)}\right]^4
\quad(\text{adjoint spin }1).
\]
Using the original SU(2) multiplication law `t\,\chi_j=(\chi_{j+1/2}+\chi_{j-1/2})/2`, the nine connected fourth cumulants are:
\[
\begin{aligned}
\kappa_4(F,G,H_i,H_i)&=-a^2/16&&(i=0,1,2),\\
\kappa_4(F,G,H_0,H_1)&=\kappa_4(F,G,H_1,H_2)=(ab-2a^3)/16,\\
\kappa_4(F,G,H_0,H_2)&=(b^2-2a^4)/16,
\end{aligned}
\]
and symmetry supplies each reversed pair. Thus:
\[
\boxed{\left.\partial_\tau^2\operatorname{Cov}_{\mu_\tau}(F,G)\right|_{\tau=0}
=\frac{\beta^2}{16}\left(-3a^2+4ab-8a^3+2b^2-4a^4\right).}
\]
Together with the proven zero SU(2) first derivative and original wall-only covariance `a^2/4`, this yields at **fixed finite L4 and beta** the exact Taylor jet
\[
\operatorname{Cov}_{\mu_\tau}(F,G)
=\frac{a^2}{4}
+\frac{\tau^2\beta^2}{32}
(-3a^2+4ab-8a^3+2b^2-4a^4)
+O_\beta(\tau^3).
\]

**Independent local source validation:** The script computes each SU(2) four-mark moment using exact spin-character multiplication and native four-wall transfer, sums all 9 connected fourth cumulants, and independently differentiates the **normalized** three-section source with the correct repeated-insertion factorials through order `u^2`. Both yield the same exact symbolic expression. The original-geometry second-order exterior Haar criterion is checked for all L3–L6. These are symbolic exact tests of the established compact-group character calculus; a complete corresponding Agda non-Abelian source/transfer kernel proof has not been produced.

**Boundary:** this proves only the first two restoration derivatives at tau=0. At higher order, combinations of distinct exterior plaquettes can remove one another's free links and yield genuinely interacting rooted cluster activities. The physical CMP119/122 constrained T/large-field absolute W3 bound on the interval [0,1] remains wholly open. No continuum, physical mass gap or global full-Gibbs exponential clustering follows.

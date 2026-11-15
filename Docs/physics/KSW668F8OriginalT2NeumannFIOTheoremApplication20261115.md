# KSW668 F8 original a=t Neumann-to-Weyl paper-theorem application

**Status:** mathematically formulated external theorem application for the **prescribed smooth compact conserved TT boundary source** and **linear tensor** on the ORIGINAL moving AdS5 brane. Source-level mathematical proof candidate; **not kernel-accepted**, numerically converged, a dynamical matter action, or a physical observation.

## 1. Exactly applicable external FIO theorem

Stefanov & Yang, *The inverse problem for the Dirichlet-to-Neumann map on Lorentzian manifolds*, Analysis & PDE 11 (2018), 1381–1414, DOI 10.2140/apde.2018.11.1381, **Theorems 3.1 and 4.2**, §§3–4. They state explicitly that dimension is **1+n, n>=2**, including 1+4; local outgoing DN is an **elliptic order-1 ΨDO** in the timelike boundary cotangent cone, and the transversely first-return semiglobal DN lens map is an **elliptic order-1 FIO** (canonical graph) modulo smoothing. Their construction is microlocal even without a separately proved global PDE. The original KSW smooth retarded Neumann IBVP existence follows via the separately cited Ginoux–Murro 2022 theorem with the compact boundary lift, subject to its normal hyperbolic smooth-data hypotheses. A theorem application is not a fresh kernel proof.

## 2. The ORIGINAL geometric and differential hypotheses

Metric \`g5=z^-2(-dT²+dz²+dx1²+dx2²+dx3²)\`, domain \`z>=b(T)=1/t\`, \`dT/dt=sqrt(1+t²)/t²\`, \`v=b'=-1/sqrt(1+t²)\`. Original tensor \`Box_g5 H=0\` and original Israel \`n·dH=-6 pi_TT\`. Fix source interior point \`t_e=1.000141436357416\`, \`x_e=0.00014471324980684235\` and original receiver \`t_r=2, r_r=0.697797781099381\`; choose a real compact spacetime source with spatial support in \`|x|<.001\`, and temporal support near \`T_e-T(1)=.0002\`, zero near the initial slice. Entire source photon-dark receiver margin \`r_r-.001-log2=0.003650600539435688>0\`.

The unique straight conformal-null chord lies **strictly in z>b(T)** between endpoints by \`b''>0\`; it is a first-return, transverse, non-glancing chord. Outward normal symbols at source and receiver are respectively \`+0.17622301193802767\` and \`-0.07558371447219975\`. Since bulk-null projections onto the timelike boundary are timelike precisely when the normal symbol is nonzero, both local DN symbols are elliptic. Outward null second fundamental form \`kappa=t³/(1+t²)^(3/2)>0\`. Constant AdS curvature gives no null *screen* conjugate focusing along the direct chord, so the lens map is a local canonical graph. A broken null line from the same source and receiver has strictly greater optical length than the straight chord unless it coincides; choose small microlocal cutoffs selecting the direct branch only. Stefanov–Yang's local finite-chord FIO construction is insensitive to the far Poincare horizon because of finite propagation and compact ray neighborhood.

## 3. Reuse DASHI's actual finite Neumann telescope: exact causal block inverse

On causally ordered small emitter E and receiving R boundary patches, the **Dirichlet-to-Neumann** map's microlocal two-patch matrix is, modulo smoothing and branches excluded by cutoffs,

\[
 \Lambda_{DN}=\begin{pmatrix}D_e&0\\F_{re}&D_r\end{pmatrix},
\]

with \`D_e,D_r\` elliptic local ΨDOs order 1 and \`F_re\` an elliptic first-return FIO order 1. Zero upper-right follows from **retarded causality**. Let \`E_e=D_e^{-1}, E_r=D_r^{-1}\` denote elliptic local order -1 parametrices and \`G0=diag(E_e,E_r)\`. Then **in noncommutative operator algebra**

\[
R=I-\Lambda_{DN}G_0=
\begin{pmatrix}0&0\\-F_{re}E_e&0\end{pmatrix},\quad
R^2=0,\quad
G=G_0(I+R)=
\begin{pmatrix}E_e&0\\-E_rF_{re}E_e&E_r\end{pmatrix}.
\]

The identities \`Lambda_DN G=G Lambda_DN=I\` hold **modulo the correctly controlled elliptic parametrix/smoothing errors**. This is *exactly the n=2 nilpotent case* of existing \`BalabanFiniteNeumannParametrix.finiteRightNeumannExactAtDepth\`; no spectral contraction hypothesis is hidden. The noncommutative inverse identity and \`R²=0\` are tested with a free noncommutative word algebra and independent noncommuting rational matrix blocks. The **Neumann source to receiving Dirichlet trace** is

\[
\boxed{\Lambda_{ND,re}=-E_rF_{re}E_e}
\]

with an **elliptic FIO principal symbol of order -1** because all three factors are elliptic and the canonical composition is locally a graph. The moving oblique Neumann junction law is independently checked, including exact rational \`t=4/3\` reflection \`beta=1/4\`. This causal two-patch R is NOT the stationary Hankel-frozen wall R, whose strict contraction only holds for positive-real Laplace \`s>=16\` and fails at low \`s\`.

## 4. Prescribed smooth compact TT source and nonzero early Weyl

Use the existing local fourth-order TT operator \`S_TT=(P_i^kP_j^l-1/2 P_ij P^kl)Q_kl\`, \`P=-delta Delta+∂∂\`, \`Q=diag(0,1,-1)\`. It preserves spatial compact support, has zero divergence and trace, has a nonzero yy principal symbol for k along x, and its mixed-index background FRW stress is conserved. Set for every finite large \`lambda\`
\[
\pi^{TT}_\lambda=\lambda^{-4}S_{TT}[\chi(T,x)\cos(\lambda(-T+s b(T)+k_x x)+\theta)]
\]
with a fixed smooth compact cutoff \`chi\` supported near the actual interior emitter. It is a **real smooth compact** stress, not a delta distribution, and the factor \`lambda^-4\` keeps its leading TT amplitude O(1). Include the original smooth nonzero Israel source normalization \`-6\` and time-dependent unit-normal factor.

At the source-free receiver, **intrinsic 4D electric Weyl** and **SMS projected 5D electric Weyl** have two distinct nonzero order-2 principal multipliers, previously checked at the same original ray: \`0.0840263224215478\` and \`0.002856448946707509\`. The SMS sign follows \`delta E5=[6-3(rho+3p)]pi_TT - delta G4\`, not a mistaken identification with the intrinsic 4D Weyl.

Therefore the composed source→Neumann→first-return lens→receiver Weyl map has **nonzero elliptic FIO principal symbol** (order \`4-4-1+2=+1\` for this normalized family), for *both* Weyl readouts. Applied to a smooth high-frequency packet, each leading contribution is \`lambda c_j cos(lambda psi+theta+phase_j)+O(1)\` with \`c_j != 0\`. The published microlocal parametrix controls lower symbols and smoothing errors; select real phase \`theta\` outside the finite union of zero-phase sets, then a sufficiently large **finite** \`lambda\` makes both receiving values nonzero. Any nonzero overall small source scaling preserves nonvanishing. Actual retarded finite energy follows from Ginoux–Murro wellposedness and the separately derived original moving-boundary energy bound:
\[
E_U(T)\le \tfrac12\int_{T_0}^T e^{\gamma(T-S)}
\|-\mathcal L_y W(S)\|^2_{L^2(z^{-3})}\,dS,
\quad \gamma=18.8994949366,
\]
for \`H=U+W\` and smooth compact Neumann lift \`W=y chi(y)G/(1-v²)\`.

**Mathematical conclusion (subject to referee checking of theorem transfer):** a real compact background-conserved **prescribed** TT source exists, on the **original** linearly perturbed 5D AdS \`a=t\` model, whose smooth finite-energy retarded tensor field has nonzero intrinsic-4D and projected-5D Weyl response at the same \`t=2\` receiver before all source photons confined to the brane. This imports a published external FIO theorem; it does **not** compute an actual physical emitter/receiver apparatus, observational limit, all-mode stability, full Einstein-matter source action, or experimental result. No new general 5D superluminal causal law follows.

The previous coefficients \`24.0805/lambda,2.0234 lambda,0.06878 lambda\` are **plane-phase local symbolic checks without all FIO Jacobians and cutoff weights**; they are NOT a quantitative complete physical receiving waveform.

## 5. Acceptance boundary and remaining gates

At the **paper/theorem-application level** the causal block inversion is algebraically exact and the source-to-Weyl existential argument is supplied using Stefanov–Yang's 1+n FIO theorem. The **Agda kernel acceptance** of all continuum steps is *not* present, so F11 remains open. The numerical **compact 3D** F8.3 still fails mesh convergence (48.4% field /83.0% curvature drift) and does not acquire a numerical receipt from this analytic argument.

Still OPEN: F8.3 quantitatively converged 3D numerical propagator; F9.1 generating matter action with complete constraints; F9.2 coupled tensor/scalar/vector and backreaction stability; F9.3 the distinct doubled-disc-cylinder gravitational perturbations; F10 physical scale, timing, frequency, attenuation and detector calibration; F11.1 pinned Agda continuum kernel; F11.2 source-to-observation semantic weld; D1 independent calibrated physical graviton observation. Review the external-theorem application before any formal promotion. No claim of a freely usable communications device or free energy.


**Original-ray phase matching (essential F8.1 correction).** A microlocal source launched from the moving boundary must have the tangential phase obtained by restricting the five-dimensional direct-null phase `Phi(T,z,x)=-T+s z+k_x x` to `z=b(T)`: `Phi_src(T,x)=-T+s b(T)+k_x x`, with `s=Delta z/Delta T` for the exact original chord and `s²+k_x²=1`. In particular the induced boundary temporal frequency is `-1+s v(T)`, not `-1`; omitting `s b(T)` launches a different bicharacteristic and invalidates the chosen-source-to-original-receiver symbol match. Source phase is compactly cut off and TT-projected by the local spatial differential operator. This correction does not itself prove the full Neumann-FIO transfer/cutoff/error theorem, which remains subject to independent audit.


**Exact 5D source-phase and normal-orientation crosscheck (2026-11-15).** New `scripts/ksw668_f8_boundary_ray_phase.py` and five local regression tests show that `Phi=-T+s*z+k*x` restricts on the ORIGINAL moving wall to `Phi_source=-T+s*b(T)+k*x`; the tangential boundary time covector is `-1+s*v(T)`. Its induced boundary inverse-metric norm is `-b²(s-v)²/(1-v²)<0`, so the source/reception covectors lie in the elliptic *timelike* domain of the local DN theory. **Sign convention:** the previously quoted `+0.1762230` emitter and `-0.0755837` receiver normal symbols use the **inward Israel normal** into the physical `z>=b(T)` bulk. The **outward geometric convexity normal** has the opposite symbols. Strict null convexity `kappa_out>0` and ellipticity (nonzero normal) are unchanged; any FIO source and reflection formula must carry this normal-orientation sign explicitly. The 68-case source-equivalent math suite includes these controls. This repairs the tangential source-phase matching but does not constitute a global numerical/Agda/referee receipt.
# YM P0 W0 — actual original 4D Wilson/F19 single-fibre continuous Haar source (23 Nov 2026)

**23-Nov source continuation (mass-gap P0):** the [actual original continuous SU(N) twelve-staple Haar centre-charge series, original SU(3) signed baryonic F-mark and native two-pair nonfactorization](YMClayP0OriginalSUNF19TwelveStapleCenterHaarBaryonAndNonfactorization20261123.md) now extends this already-owned original one-fibre reduction. [The exact source checker](../../scripts/check_ym_p0_sun_original_12staple_haar_center_baryon_20261123.py) passed **1,838/1,838** and its committed blob **b6d937c44fb8f2d24f2e3849f8eb230281faac9a** matches the locally executed Python script byte-for-byte. Standard SU(N) centre selection gives I_{kl}(H)=0 unless k-l≡0 mod N, and first unbalanced baryon coefficient 2*(beta/(2N))^N/N!*Re det H. On the authentic original y-pair with all twelve spectator controls native, continuous SU3 Weyl–Haar gives reduced local T coefficients 1+4beta²+8beta³/3+8beta⁴ vs 1+beta²-beta³/3+beta⁴/2 for two genuine coherent/frustrated exterior conditions. For two original y,z F19 pairs sharing exactly one original y-z plaquette, full original Wilson action has a nonzero mixed Cartan Hessian -2/N: the next pair CANNOT be treated as independent T. **These results do not supply the physically selected CMP119/122 constrained/gauge-fixed R/FP T, original absolute W3 or a Clay mass gap.** Classical SU(N) Weyl and Weingarten integration retain primary attribution.


## Source authority, scope and proof owner precedence

One original finite four-dimensional periodic L=4 Wilson action: 1024 positive links, 1536 unit plaquettes, and the existing native original R445 F19 disintegration into 64 ordered two-link pairs (128 original links) and **all 896 interacting original spectator links**. The two unique original gauge-invariant fine plaquette deficits remain F and G at y–z faces rooted at (0,0,0,0) and (0,0,0,2), with 0<=F,G<=2. Exact original F19 normalized Haar/four-column ancestry: \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\`, \`YMClayOriginalWilsonPhysicalF19PartitionExact\` and the pre-existing full-1536-plaquette local source regression \`scripts/check_ym_p0_original_wilson_marked_ordered_t_20261123.py\`. All original CMP119/122 ordered T, E/R/B/V, FP/gauge, P3/Step-V and CMP116/W3 receivers remain attributed to their existing owners. No new generic T record or presumed Eq.(1.71) source equality is introduced.

This result pays a previously absent **explicit nontrivial continuous SU(2) Haar integration for one selected actual original Wilson/R445 fine fibre**, for arbitrary noncommuting original link background and arbitrary beta>=0. It is not the full continuous 960-variable Haar integration nor a source-identified Bałaban CMP119/122 physical T.

## Exact original source geometry, no toy action

For every original pair (U0,U1) with its literal native coarse holonomy W=U0 U1, let V=U1, so U0=W V^{-1}. Holding W and the other 959 F19 coordinates fixed, changing V affects **exactly 12 distinct original plaquettes**. Every original positive link occurs in exactly 6 plaquettes; no unit plaquette contains both members of a consecutive collinear pair. At least **two of the four original positive links in every plaquette are spectators**, so the original Haar/fibre disintegration has no missing plaquette variables. Of 64 pairs, exactly two touch F, exactly two touch G, and the remaining sixty touch neither; none touch both. All counts are exhaustive on the original 1536 face words and their native source indices.

For compact SU(N), the normalized trace-deficit \`J(P)=1-ReTr(P)/N\` obeys \`|J(P)-J(P')|<=||P-P'||_op\`. With \`||V-V'||_op<=delta\`, the two altered source links each change by at most delta (left multiplication and inverse preserve this distance). Therefore, for *the actual full original Wilson action* \`S=sum_p J(P_p)\`, **at every fixed background**:

\`\`\`text
|S(V)-S(V')| <= 12 delta
exp(-12 beta delta) <= exp(-beta S(V'))/exp(-beta S(V))
                    <= exp(12 beta delta), all beta>=0.
\`\`\`

This local modulus is independent of the 896 spectator count/volume *at one fibre step*. It does not give cutoff-uniform RG rate; beta(a) may grow, so mesh resolution must scale accordingly.

## Continuous SU(2) quaternion elimination at every fixed original background

Identify SU(2) with unit quaternions \`q=(q0,q1,q2,q3) in S^3\`. The actual source plaquette holonomies contain either \`V\` or \`W V^-1\` once on each of the twelve touched faces. Their normalized real trace is therefore affine-linear in the four real coordinates of q (in fact homogeneous linear for each touched face), with rational coefficients when the frozen original SU2 links are rational quaternions. For arbitrary noncommuting W and the remaining original link values, *the complete original action* has the exact form

\`\`\`text
S(q)=C-h.q,  |h|<=12,
F(q)=aF+bF.q,   G(q)=aG+bG.q.
\`\`\`

C includes the other **1524 source plaquette costs** plus the constant 12. The coefficients C,h,aF,bF,aG,bG are determined by the actual source, not independent fitted terms. For any original pair, bF=0 or bG=0 (the two selected global marks are not incident to one pair).

Normalized continuous SU2 Haar is uniform measure on S^3. Its exact moments are \`E[q0^(2k)]=Catalan(k)/4^k\`, odd moments zero; the moment-generating function is **at all orders**

\`\`\`text
I(t)=int_{SU2} exp(t u.q) dH(q) = 2 BesselI_1(t)/t,    |u|=1,
I'(t)=2 BesselI_2(t)/t,    t=beta*|h|.
\`\`\`

Define \`I(0)=1\`, \`I'(0)=0\`; when h=0 the source integrals use those continuous limits. Then the original **conditional one-fibre** source masses are exactly

\`\`\`text
T0 = exp(-beta*C)*I(t)
TF = exp(-beta*C)*(aF*I(t)+(bF.h)/|h|*I'(t))
TG = exp(-beta*C)*(aG*I(t)+(bG.h)/|h|*I'(t))
TFG= exp(-beta*C)*(aF*aG*I(t)
                   +(aF*bG.h+aG*bF.h)/|h|*I'(t))
\`\`\`

for the **actual separated original mark pair** (at most one b vector nonzero for a given fibre). These are all four same-measure source columns, not a product of independently averaged F and G with different reference weights. The formula holds for arbitrary other original SU2 configurations and every beta>=0; no numerical Haar quadrature assumption is required.

Special exact source sanity check: if W=I and all other original links are fixed to I for the native pair touching F, then C=12, h=(12,0,0,0), F(q)=1-q0, G(q)=0. Thus

\`\`\`text
T0 = e^(-12 beta)*2 I_1(12 beta)/(12 beta)
TF = e^(-12 beta)*2 (I_1(12 beta)-I_2(12 beta))/(12 beta)
TG = TFG = 0.
\`\`\`

At fixed other coordinates a single fibre cannot produce the time-separated connected covariance; after genuine integration over interacting spectators it need not vanish. Never promote this zero conditional response to a full Wilson clustering theorem.

## SOURCE-RELATIVE four-column continuous-Haar tagged-cell errors

Partition the genuine compact SU(N) Haar pair fibre into measurable cells of operator-norm diameter <=delta, select one representative per cell and weight it by the **true Haar mass of that cell**, not a fictitious equal-mass finite subgroup. With x=12 beta delta and E=e^x, the exact positive Wilson source K0 of this fixed-background fibre controls all four *approximate source* errors:

\`\`\`text
|K0'-K0|   <= eps0*K0,     eps0=E-1
|KF'-KF|   <= epsF*K0,     epsF=2(E-1)+f E delta
|KG'-KG|   <= epsG*K0,     epsG=2(E-1)+g E delta
|KFG'-KFG| <= epsFG*K0,    epsFG=4(E-1)+2(f+g) E delta.
\`\`\`

Here f,g in {0,1} are original incidence indicators of whether the pair touches F/G; f*g=0. The Wilson weight ratio plus |F|,|G|<=2 and |dF|<=f delta, |dG|<=g delta prove this **before integration**, so the estimates work at every arbitrary frozen background and every beta>=0. They are precisely four distinct, *same-source-normalized* marked-error inputs (including FG). At x<1 one may certify rationally using E<=1/(1-x).

Explicit SU(2) finite net: round each unit quaternion coordinate to the nearest 1/M grid and normalize. Each point is within 2/M of its representative; cell diameter <=4/M. True Haar cell masses exist; this assertion does NOT assign them equal weights. For M=1024, delta=1/256 and beta=1/144, x=1/3072 and E<=3072/3071. A pair touching F but not G has verified conservative errors

\`\`\`text
eps0  <=  1/3071
epsF  <= 14/3071
epsG  <=  2/3071
epsFG <= 28/3071.
\`\`\`

Feeding these four inputs into the *already existing* W0→W1 mixed-log stability estimate gives a rigorous error bound <=0.064388 for that one-fibre marked polynomial on |s|,|t|<=9/100. This is conservative and often vacuous for conditional connected response; it is not W3 decay.

For the **complete original F19 Haar integral** at fixed W, quantize all 64 pair variables AND 896 original spectator variables with mesh diameter delta. All 1024 original links then change by <=delta, so |dS|<=6144 delta, |dF|,|dG|<=4delta. Hence the same integral yields explicit four-column relative errors with X=6144 beta delta:

\`\`\`text
eps0=exp(X)-1,
epsF=epsG=2(exp(X)-1)+4 exp(X)delta,
epsFG=4(exp(X)-1)+16 exp(X)delta.
\`\`\`

This is a direct constructive original continuous-Haar **to original tagged-Haar cubature** certificate retaining all physical interacting spectators, global marks and normalization. At beta=1/144 and delta=1/65536, X=1/1536, and rational E<=1536/1535 gives a mixed-log error upper bound <0.037880 on the same complex marked bidisk. **It is not a quantitative comparison with CMP119's Eq.(1.71) T** until a source-specific equality or discrepancy linking that genuine gauge-fixed operator to this Wilson quadrature is proved; finite huge cubature nets are not efficient physical RG bounds.

## Independent original-source regressions (local SymPy 1.14.0, no CI)

Two exact local Python/Fraction/SymPy acceptance scripts have been executed independently of Agda/Lean:

1. \`check_ym_p0_original_su2_arbitrary_background_f19_bessel_t_20261123.py\`: **2936/2936 assertion groups PASS**. Uses the actual full 1536 native plaquette words and 24 arbitrary noncommuting rational SU2 W/spectator backgrounds, checks exact \`S(q)=C-h.q\` against both 12+1524 and all-1536 Wilson evaluations, all original F/G geometry and 672 independent source four-column continuous-Haar Taylor moment comparisons versus the Bessel generating formula through beta degree six. Exact SU2 quaternion multiply/inverse; not a restricted Q8/Z2 Haar measure.
2. \`check_ym_p0_original_sun_f19_continuous_haar_local_t_20261123.py\`: **5095/5095 assertion groups PASS**. Original 64-pair source incidence and four-column per-step error certificate for many beta/delta values, all-original source Marked Hessian, constructive SU2 finite Haar cell nets, exact continuous SU2 one-fibre Bessel/Haar moments and finite Q8 cubature negative controls.

The Q8 *equal-weight* group cubature matches continuous SU2 moments through degree three but differs at degree four: continuous \`E[q0^4]=1/8\`; uniform Q8 gives 1/4. On the special all-identity original one-fibre source (beta=1/144, t=1/12), the independent all-degree moment-tail argument certifies genuine four-column relative errors (Q8 against *continuous* Haar):

\`\`\`text
eps0 <= 5/9950976              approximately 5.0247e-7
epsF <= 235145/9549619968      approximately 2.4624e-5
epsG = epsFG = 0.
\`\`\`

Q8 is a **cubature approximation for this specific source**, not an equally accurate δ-mesh for arbitrary original backgrounds. It must never be silently substituted for real compact Haar in CMP119's physical Sect.2 operation.

## Physical remaining gates and no-promotion

**NEW PAID mathematical/source cut:** exact one original continuous SU2 Haar fibre on arbitrary original noncommuting Wilson backgrounds and arbitrary beta; exact original incidence and all four columns; honest local/global original Haar→tagged-Haar quadrature errors and moment negative controls. This is stronger than the previous ten-link SU2-centre enumeration and stronger than an abstract error-modulus receiver.

**STILL OPEN:** the literal CMP119 (2.18) admissible Omega/Lambda/S determining-set sequences and (2.19)/(2.20)/(2.22) actual ordered T steps; exact CMP122 Eq.(1.71) *gauge-fixed* constrained operator with Faddeev–Popov/ghost/Jacobian, nonlinear Q_B averaging, R-modification and full E/R/B/V source density; original beta(a) multiscale four-mark physical source realization, differentiated actual residuals and literal original-vs-CMP119 four-column error terms; rooted *termwise absolute* W3 cutoff/volume-uniform connected shells and positive fixed-physical-distance rate; E1/D1/D2/N1/G1 original interacting R4 same-H OS gap. None follows merely from the exact local Bessel integral. No Agda/Lean kernel, CI or Clay solution claimed.

Attribution: original Wilson 1974 lattice action, normalized compact Haar/standard SU2 quaternion and Bessel identities, Bałaban CMP109/116/119/122 original localization/RG physics, existing DASHI original F19/marked error/CMP116 W3 owners.


## All SU(N): exact original twelve-staple external-field reduction

The SU2 quaternion/Bessel formula above is a specialization of a source-exact **SU(N) matrix integral** that needs no invented effective action. In the source's one original ordered pair at fixed W and fixed other 959 variables, write the four positive-link face factors in their actual native orientation \`U_a U_b U_c^-1 U_d^-1\`. Each of the twelve affected faces contains exactly ONE of U0=WV^-1 or U1=V. Expand that single factor into fixed original matrices and either V or V^†. Cyclicity and \`ReTr(M V^†)=ReTr(M^† V)\` show that each affected original face contributes precisely \`ReTr(H_p V)/N\` for a unitary SU(N) staple matrix H_p determined by the actual source W/other links. Consequently,

\`\`\`text
H = sum_{p among 12 original touched plaquettes} H_p,
||H||_op <= 12,
S_original(V) = C - (1/N) ReTr(H V),
C = sum_{p among other 1524 ORIGINAL plaquettes} J_p + 12.
\`\`\`

The resulting exact same-original-action **continuous SU(N)** one-fibre integration is

\`\`\`text
Z_N(H;beta) = int_SU(N) exp[(beta/N)*ReTr(H V)] dHaar(V),
T0_original = exp(-beta*C) * Z_N(H;beta).
\`\`\`

If this source pair touches F, then the one original marked plaquette gives \`F(V)=1-ReTr(H_F V)/N\`, with H_F the corresponding original unitary staple. Its exact source marked mass is

\`\`\`text
TF_original = exp(-beta*C) *
              [Z_N(H;beta) - beta^(-1) D_{H_F} Z_N(H;beta)]
\`\`\`

for beta>0, with the genuine continuous limit at beta=0, where \`D_{H_F}\` means the derivative of Z_N in its matrix source direction H_F. If that pair does not touch F, F is a constant of the frozen other variables and TF=F_const*T0. Likewise for G. No original pair touches both F and G, so one of the two is constant at each local conditional step; the **unique global FG** source column is preserved as TFG=G_const TF or F_const TG, or F_const G_const T0. That local factorization is not a factorization after integrating the remaining interacting spectators/other fibres and must not be promoted to zero global covariance.

In the quaternion realization of SU2, ReTr(HV)/2=h.q and Z_2(H;beta)=2 I1(beta*|h|)/(beta*|h|), reproducing the exact all-background Bessel formula above. The all-N source identity follows for any N from original holonomy orientation, group matrix multiplication, adjoints and trace cyclicity, without an approximation. It is stronger than the arbitrary-background SU2 test, but **not** a closed elementary formula for Z_N at every N.

Independent local SymPy 1.14.0 exact-matrix acceptance: **1,634/1,634 groups PASS**. The locally executed extended checker \`check_ym_p0_original_sun_matrix_staple_f19_t_20261123.py\` evaluates noncommuting rational SU2 matrices and noncommuting rational SO3⊂SU3 matrices, the original full action's 1536 face words (with the 1524-face complement), the twelve actual source staple sum, direct Wilson action response at multiple SU(N) V, and the four globally marked original source factors. This is an independent finite matrix regression for N=2,3, plus a **symbolic all-N algebraic derivation**, not an all-N exhaustive numerical test.

GitHub [compact reproducibility checker](../../scripts/check_ym_p0_original_sun_matrix_staple_f19_t_20261123.py). The two previous [arbitrary-background SU2](../../scripts/check_ym_p0_original_su2_arbitrary_background_f19_bessel_t_20261123.py) and [local Haar-cell/Q8 bound](../../scripts/check_ym_p0_original_sun_f19_continuous_haar_local_t_20261123.py) checkers are also committed. **Acceptance provenance:** the larger local extended programs produced the reported 2,936/2,936, 5,095/5,095 and 1,634/1,634 groups. The GitHub scripts were authored from those checked calculations and read back, but are compact source editions; do NOT claim their exact bytes were run locally or that their exact assertion totals are equal to the extended runs. Agda/Lean kernel and GitHub CI are still unrun.

### Exact remaining high-priority physical weld

Find/inhabit one *actual Bałaban CMP119 Sect.2* admissible Omega/Lambda/S history and matching CMP122 Eq.(1.71) **gauge-fixed constrained** T with Wilson/F19 variables, nonlinear printed Q_B, source E/R/B/V, FP/ghost/Jacobian, running beta(a), boundary residual, and genuine original global 1/F/G/FG differentiated step identity. Only then apply the already-owned CMP119 factorized marked approximation budget and this original-source Haar-cell modulus to the real physical T. Then prove the still-open individual **absolute** CMP116/W3 connected shell charges and cutoff/volume-uniform physical rate. The source exactness of Z_N does not itself attach it to CMP119's literal T or discharge W3/E1/D1/D2/N1/G1.

# YM P0 W0→W1 — four-column marked-log stability, exact source regression and W3 nonimplication (23 Nov 2026)

## Source precedence and scope

The *source* is the original full 4D compact Wilson Gibbs measure, transported through the existing R445/F19 original ordered 64 two-link pairs and **all 896 interacting spectators**. Reuse \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\`, \`YMClayOriginalWilsonPhysicalF19PartitionExact\`, \`YMClayNative1024FullMarkedWilsonReindexExact\`, \`BalabanCMP119Equation218FactorizedFunctionalDensityExact\`, \`BalabanCMP119FactorizedDensityApproximationExact\`, \`BalabanCMP119FactorizedMarkedBudgetVanishesExact\`, \`BalabanCMP119Equation171WeightedStepApproximationExact\`, \`BalabanCMP122Equation171TOperationSemanticsExact\` and \`BalabanLiteralTwoWilsonCMP116ConnectingTailExact\`. **Do not** reconstruct a new T algebra or declare the physical Eq.171 operation inhabited merely because those records exist.

What is new: an explicit elementary **Lipschitz certificate** converting four *source-normalized coefficient error budgets* (including the mixed FG column) into an actual uniform error bound on the **two-global-mark mixed logarithmic response**. This sits *after* CMP119 factorized step-error budgets and *before* source-first marked-W3 identification. It does not itself identify CMP119's physical T, provide a cluster charge or prove a mass gap.

## Source data and all-complex-tilt theorem

At a fixed original coarse field W (or after integrating W) let \`a=K0>0\`, \`b=KF\`, \`c=KG\`, \`d=KFG\`, with the **same one positive original Wilson Haar conditional measure** and genuine original plaquette deficits \`F=1-ReTr(P_F)/N\`, \`G=1-ReTr(P_G)/N\` in [0,2]. All the unique original fine marks and spectators remain inside their common integral. Then \`0<=b,c<=2a\`, \`0<=d<=4a\` and \`|ad-bc|<=a^2\` (the last by Cauchy-Schwarz/Popoviciu variance).

Define the global affine two-source polynomial and mixed source-log Hessian

\`\`\`text
K(s,t) = a + s b + t c + st d
M      = a d - b c
H(s,t) = d_s d_t log K(s,t) = M / K(s,t)^2.
\`\`\`

The last identity holds for all complex s,t for which K is nonzero: the determinant numerator is exactly independent of both tilts. In the original |s|,|t|<=r=9/100 bidisk, positivity of the underlying unmarked source gives

\`\`\`text
|K(s,t)| >= lambda*a
lambda=1-4r-4r^2=1519/2500>0.
\`\`\`

Let a candidate CMP119 four-column density \`K'(s,t)=a'+s b'+t c'+st d'\` obey **all four** pointwise original-source-relative errors (for each actual selected physical slow field/domain path, if instantiated):

\`\`\`text
|a'-a|<=eps0*a,   |b'-b|<=epsF*a,
|c'-c|<=epsG*a,   |d'-d|<=epsFG*a.
\`\`\`

Set \`e=eps0+r(epsF+epsG)+r^2 epsFG\` and
\`D=4eps0+epsFG+eps0 epsFG+2(epsF+epsG)+epsF epsG\`.
If \`e<lambda\`, then \`|K'|>0\` throughout that same complex bidisk and the exact universal error bound is

\`\`\`text
|d_s d_t log K' - d_s d_t log K|
   <= D/(lambda-e)^2 + e(2lambda-e)/(lambda^2*(lambda-e)^2).
\`\`\`

Proof: \`|K'-K|<=a e\`, \`|M'-M|<=a^2 D\` by expanding \`(a+da)(d+dd)-(b+db)(c+dc)\`, and \`|M|<=a^2\`. Split \`M'/K'^2-M/K^2\` into \`(M'-M)/K'^2 + M(1/K'^2-1/K^2)\` and use \`1/K'^2-1/K^2=(1/K'-1/K)(1/K'+1/K)\`, with denominators bounded by \`lambda*a\` and \`(lambda-e)*a\`. At the physical unmarked origin s=t=0, replace e by eps0 and lambda by 1 in the denominator term, retaining the same D.

For equal \`eps0=epsF=epsG=epsFG=eps\`, \`e=(1+r)^2 eps\`, \`D=9eps+2eps^2\`. At eps=1/1000 the rigorous bound is approximately 0.035104 throughout the **complex** bidisk, improving to 0.0110231 at the origin. These are deliberately conservative source-agnostic bounds, **not** observed Wilson errors or empirical accuracy of CMP119 T.

This is a quantitative error-to-response theorem, **conditional** on the physical CMP119 T actually furnishing source-matched four-column \`eps_j\`. It does not infer them from an arbitrary aggregate single scalar \`markedMajorant\`: CMP119 residual/constraint and globally unique marks must be differentiated and controlled for all four columns separately. If the CMP119 density contains additional non-affine dependence on global sources, first prove matching source derivatives and a valid remainder bound instead of silently replacing its genuine source by this polynomial.

## Local independent exact result on the existing original-action restricted source

Committed [check_ym_w0_four_column_to_marked_hessian_lipschitz_20261123.py](../../scripts/check_ym_w0_four_column_to_marked_hessian_lipschitz_20261123.py) imports the **existing** [check_ym_p0_original_wilson_marked_ordered_t_20261123.py](../../scripts/check_ym_p0_original_wilson_marked_ordered_t_20261123.py) instead of reimplementing its full 1536-plaquette source. That owner enumerates all 1024 assignments of 10 active original fine links in the SU(2) centre subgroup, with the other 1014 frozen, using the *whole original Wilson action*. It retains 64 original R445 coarse link slots, 896 spectator slots, and four exact coarse fibre densities. Its native marks are trace signs, so the NEW script converts each of the 1/traceF/traceG/traceFG four columns **exactly** into the deficit 1/JF/JG/JFJG columns.

Local Python+SymPy 1.14.0 exact run (not CI) **PASS, 6,324/6,324 assertion groups**: 3 generic symbolic determinant identities; 145 checks of source cone/nonzero properties; 6,080 candidate-error perturbation checks across five exact source densities, 16 four-column sign patterns, four error sizes and nine real tilts; 80 exact algebraic complex-tilt nonvanishing checks; 16 negative-control checks. The source owner additionally rechecks full 1536-plaquette action, the independent original 1/F/G/FG fine-vs-F19 stage sum, normalized finite counting Haar *on that restricted centre slice*, and exact fibre+between covariance reconstruction. GitHub committed script Git object **828c1552b75e591cd828b556c200991ecaca712c** is byte-identical to the locally executed new checker. Neither checker tests the complete continuous SU(N) Haar theory.

## Sharp logical no-go for physical W3 from uniform accuracy alone

Even perfect agreement of a,b,c and the physical four-moment cone is insufficient: take the abstract valid corner laws on (F,G) in {(0,0),(2,0),(0,2),(2,2)} with true \`(a,b,c,d)=(1,1,1,1)\` and candidate \`(1,1,1,1+eps)\`. For 0<eps<1 both are positive probability laws with the same two marginal moments. Nevertheless \`H(0,0)=0\`, \`H'(0,0)=eps\`. If eps is independent of support separation R, no bound of the form \`C exp(-m R)\` follows from this error budget for arbitrarily large R, even if eps is small. This abstract witness is **not** an original-Wilson source realization; it is a counterexample to a generic implication. The exact original Wilson centre-slice source already has mixed-sign nonzero conditional fibre covariances, showing why signed cancellation cannot replace termwise absolute W3.

## Actionable physical attachment, no duplicated compilers

**W0→W1 open producer:** for at least one genuine CMP119 source domain sequence and actual running beta(a), extract the original Wilson F19 \`(a,b,c,d)\` and original \`K'(s,t)\` from the *selected source* (2.18) sequences, (2.19) disjoint components and (2.20)/(2.22) ordered T, including original E/R/B/V, source Q_B(U), gauge/FP/ghost/Jacobian, R-modified constraints, every original interacting spectator and its conditional boundary state. Establish four independent normalized pointwise approximation bounds, **including FG and residual derivatives**, rather than identifying unrelated instantiated scalar records. Only after those exist does the estimate above convert CMP119 approximation budgets to an actual mixed Wilson log response.

**W2/W3 still open:** prove *individual original source-connected activity* absolute rooted-shell charges, including large-field, entropy and UV physical scale, with \`Q(a)<1\`, \`inf_a[-log Q(a)/a]>0\` and a cutoff-/volume-uniform prefactor. A small \`eps_j\`, a two-mark signed Hessian, the 64-pair finite source slice, and a published conditional CMP122 theorem do not pay this. E1/D1/D2/N1/G1 same-original interacting R4 continuum/OS gap remains OPEN. No Agda/Lean kernel, CI or Clay solution claimed. Source authorship: Wilson/Haar, Bałaban CMP109/116/119/122, existing DASHI F19 and CMP119/122/W3 producers; this calculation is an elementary stability/negative-control audit.

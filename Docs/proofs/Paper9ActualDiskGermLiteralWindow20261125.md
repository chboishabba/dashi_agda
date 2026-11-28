# Paper 9 — actual disk germ and literal adjacent-prefix window

25 November 2026. Source-written Lean, UNCOMPILED. Actual local SymPy/Fraction arithmetic replay; no native proof receipt, no CI. Starting Agda #1546 head 43579aaa and Lean ab9df47. Original CM, modular forms, Ramanujan, Chudnovsky, Machin, Bishop and pinned Mathlib sources retain attribution. This work composes the repository's original normalized analytic and rational prefix producers rather than introducing new carriers.

## A5 actual germ, no residual derivative

Let t=cmPoint, d=2t+1, L(w)=d/(1-w), u=wL(w). Reuse centeredJTaylor: centeredJ(u)-[K+a u+b u²/2]=u³ r(u) locally for r continuous at zero; K is the actual selected j-value. Then the original disk j-value minus K is wX(w), where
    X(w)=a L(w)+(b/2) w L(w)²+w² L(w)³ r(wL(w)).
The center is retained, X(0)=A=a d and X'(0)=B=a d+b d²/2. The continuous remainder is multiplied twice by w; derivative of w f(w) at zero equals f(0) for f continuous there (punctured slope proof). No derivative of r is needed. Use diskTauLocal and original chartValue corrections to bind Xp(w)=alpha X(alpha w), Xm(w)=alpha^-1 X(alpha^-1 w). Original alphaLinear=(t+1)alpha=-t, fixedPoint, alphaTrace=-81/41; no inverse j.

At zero N=Xp Xm has A² and derivative -(81/41)AB; M=(X-Xp)(X-Xm) has (163/41)A² and derivative (163/1681)AB. Polynomial evaluation at wX gives P2,P3 A and S2,S3 A for the two complements. Original chartAffineAnalytic and jExtAnalytic give continuity of all 42 chart values along the disk. The actual remaining 40-root polynomial's coefficient continuity follows by finite coefficient convolution. Finite restSlope evaluation therefore gives continuous T, and actualTZero supplies T(0)=S3. No derivative of any residual factor or of T away from zero. Apply normalizedActualCross and crossPeriodOfCross, then literalPeriodFromDisk.

Lean commits: fc571737d205850b9cc6595c045ed50c98086f0d (Paper9DiskGeometry, linear tangent identity); dceb3a244341735bf1f1cd93f39dc7bece661c5b and 37533f04e5cbbb2d4358f5bedfc4f5dcbcc1bccb (Paper9DiskGerm). The intended endpoint literalPrefixFromFiniteChecks consumes unitOK,diagOK,shiftOK,sliceOK,jetOK,piRoundOK,sqrtRoundOK,expWindowOK and concludes the original literal factorial prefix limit 426880 sqrt(10005)/pi. No abstract analytic germ or root assumption in this endpoint statement. Source only: all elaboration/API/tactic repair and actual native checks remain required. Pinned Mathlib 8f9d9cff6bd728b17a24e163c9402775d9e6a365 Deriv/Slope and Deriv/Polynomial source APIs inspected. No claim of typechecking.

## F5 original adjacent-window closure

For literal prefix S_n=T_n/Q_n, d_n=S_(n+1)-S_n=product(n+1)*weight(n). The original signed leaf identity gives d_(n+1)=-rho_n d_n, where rho_n=-leaf(n+1)*weight(n+1)/weight(n). Reuse the existing BishopChudnovskyPositiveGapExact source gap (positive coefficients independently replayed):
    0<=rho_n<2^-41<1.
Thus S_(n+2)=rho_n S_n+(1-rho_n)S_(n+1). Adjacent windows [min(S_n,S_(n+1)),max(...)] are nested, and nonempty prefix positivity follows from the first positive pair. No separate even/odd proof is required for this enclosure. Every fixed window contains all sufficiently late terms, so closed-order limit transport gives the actual series value in EVERY such window from the existing A7 period theorem. This is not inference from a sampled bound or a new convergence theorem.

At literal cutoff n=1+floor((k+4)/41), root scale s=2^(k+2), r=floor(s sqrt(10005)), the source already supplies r²<=10005*s²<=(r+1)². Positive denominator corners yield
    L_k=426880*r/(s*max(S_n,S_(n+1))) <= pi
    pi <= U_k=426880*(r+1)/(s*min(S_n,S_(n+1))).
For the original Machin stage m_k and radius e_k (22/7 at zero, 4/25^k otherwise), the existing error bound gives L_k<=m_k+e_k, m_k<=U_k+e_k. These are rational inequalities; the classical real is eliminated from the conclusion. This is the exact input of BishopChudnovskyCrossOnlyEndpointExact, NOT a proof object imported into Agda.

Lean Paper9LiteralWindow (91efa9c13652b7eed4a3076fce43d561bc85c464, corrected signed adjacent combination 5f405bc4b0913f53843d4705d5c6e1ee9b72f0ef): rhoBounds, adjacentConvex, nestedAdd, laterInside, loPositive, limitInside, rootBracket, actualPiInside, rationalCross. This last theorem takes the actual period limit, source root-square witnesses and Machin error as explicit inputs. Still need actual all-index rational source correspondence/transport (raw prefix, root floor, cutoff, Machin stage and radius) and proof reflection into the original Agda Q^u Cross. Existing PrefixSemanticsExact, PairedTotalityExact, WidthReflectionExact, BishopMachinRationalStageEmbeddingExact and BishopMachinCrossEnvelopeBishopOrderExact are the original owners. No magical cross-kernel transfer. Native proof acceptance, full finite residual rerun, independent performance remain separate.

## Executed arithmetic

scripts/check_paper9_disk_prefix_cross.py local SymPy 1.14/Fraction executed; committed at 40360db7be25f55f452b1c6d6d43a8474a6161d9, exact git blob 0e4095aa0dcabe874bab9f0a82fa0c15937e7a8d matches local hash. Nine exact germ/cross identities, positive coefficients of the all-index gap polynomial, 19 adjacent nesting controls, 20 positive prefixes, 513 exact rational cross and width stages (0..512) PASS. No decimal pi, floats, CI or full original CM163 coefficient residual replay. Local lean/lake/agda absent. Tests do not pay the universal native cross or kernel acceptance. Keep higher-jet transverse acquisition off current pi endpoint critical path.

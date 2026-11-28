# Paper 9 — actual selected CM disk, signed certificate consumers and rational endpoint

25 November 2026. Parent 0509d446b8b31019b94b0ef7eda0539ab2e493b5.
Lean companion research/paper9-original-eisenstein-derivative-20261125:
85eff0dd4590c0f6c37f9dc26c02ef68dff95dd0 and 979f2ba17ceb7bb701efc79377b6ff6dfdbf6156.
New proof terms source-written, UNCOMPILED. Local exact arithmetic checked the three normalization constants, the disk bound, and three symbolic tangent linear combinations; no actual CM packet replay, compiler, kernel, CI, or benchmark.

## A6: consume existing original series, not new analytic infrastructure

Read Integration/MoonshineEisensteinAgdaTarget.lean: e4Term/e6Term, summable_e4Term/summable_e6Term, e4Limit_eq_mathlib_E4/e6Limit_eq_mathlib_E6 are the actual original shifted-index streams and their converged Mathlib target equalities. Also read Paper9OriginalEisensteinDerivative, Paper9RootODE and Paper9HypergeometricSeriesODE. Pinned Mathlib v4.28.0 UpperHalfPlane/Exp.lean explicitly owns Periodic.im_invQParam_pos_of_norm_lt_one; use the q chart lift for any nonzero q in the small disk and the separate normalized zero mode, not an inverse of j or z.

For m=n+1 and k<=5, sigma_k(m)<=m^(k+1)<=64^m, so on |q|<=2^-36 each original shifted term has norm <=504(2^-30)^m. Its sum is <=504/(2^30-1)<1/16. The E6 sign is retained before taking the norm. Actual source x,y stay within 1/16 of 1; Re x>0, |x|,|y|>=15/16. Expand around the original normalized zero mode: |x^3-1|<=817/4096, |y^2-1|<=528/4096. Consequently |z|<=1345/3375=269/675<1/2. No elliptic singularity or branch switch in this disk. Paper9SelectedCMDomain.lean source-writes originalBandsAt, originalBands, goodSelected, actualHyperIdentitySelected and actualHyperFirstJetSelected on the original x,y,rootF,H,jet and L. The first-jet theorem differentiates a neighbourhood equality, not an isolated scalar identity. The selected actual CM q membership still needs native binding: tau=(-1+i sqrt163)/2, |q|=exp(-pi sqrt163)<exp(-36)<2^-36 using pi>3, sqrt163>12, exp(1)>2. Real negative q follows from exp(-pi i)=-1; the Fourier coefficients are real, and both x,y>0 by the band. These last selected-point and positive root statements are ordinary mathematical derivations, not yet Lean proof terms.

## A3–A5: original certificate consumers, precise missing producers

Existing Paper9WidthReflectionHeckeLaurent20261125 and Paper9CM163SourceReplaySignedTaylor20261125 already derive the actual 42 Hecke charts, normalized Laurent products and signed tau Taylor equation; their finite replay script is unexecuted in this cut. No full bivariate polynomial or new modular-function carrier needed. Paper9CM163CertificateConsumer.lean writes isolateHalfUnit for the real shifted diagonal root, all 80 complementary coefficients retained. It consumes actual factorization, original dyadic half-unit bound and strict coefficient dominance, not a fitted root. Reflect the existing finite packet's integers into those premises; no claim that has been done.

The same module writes signedTangent and actualSliceTangent. For f(alpha)=41alpha^2+81alpha+41, c20=S2, 41c11=81c20 and 2c21=P3-2S3, multiply the cubic residual by 41 then alpha-1. Exact identities (82alpha+81)(alpha-1)=-163(alpha+1), 41(1+alpha^3)=-122alpha(alpha+1) follow from f=0. Cancel alpha+1 (nonzero by f(-1)=1), obtaining
163 S2 [(alpha^2-alpha)b+a gamma] = a^2(alpha^2-alpha)(41P3-326S3).
The signed branch alpha remains retained. Local SymPy expanded the three linear combinations used in these source terms to exact zero. This is algebra only; actual j Taylor/Hecke source, derivative existence, coefficient reflection, dyadic interval soundness remain unpaid. actualJZ source-writes the algebraic relation jTarget(tau)*zCoord(qParam tau)=1728 on the original normalized discriminant and explicit apartness, not the CM root.

## A7: positive period normalization, reverse direction

Put C=640320^3, A=13591409, B=545140134. On actual certificate outputs j=-C and s2=77265280/90856689, z=-1728/C and (1-s2)/6=A/B. The source-written actualHyperFirstJetSelected and periodAlgebra give
A H(z)+B jet1(z)=B/[pi sqrt163 sqrt(1+1728/C)].
The two exact integer identities 144 B^2=163(C+1728) and C=144*426880^2*10005 imply B^2=426880^2*10005*163*(1+1728/C). All factors positive. Hence, setting v=sqrt(163*(1+1728/C)) and R0=sqrt10005,
B/(pi*v)=426880*R0/pi.
Conversely positivity and this identity recover the squared integer relation; no arbitrary sign of a square root. Lean positiveNormalization consumes these positive scalar inputs. Bind v and R0 to the original real branches and selected CM q; no source-independent pi introduced.

Using the actual factorial recurrence, A H+B jet1=the sum of (A+B n)c_n z^n. The literal sourceP(0)=sourceQ(0)=1; for successor j=i+1 the exact ratio c_(i+1) z^(i+1)/(c_i z^i) equals sourceP(j)/sourceQ(j). In original sourcePrefix n, T/(Q B_split) equals the sum through index n-1 by the existing ordered split merge semantics. Native rational reflection is still needed, and B_split is the split-node coordinate (not constant 545140134).

## F5: two rational inequalities, not a carrier equality assumption

The original BishopChudnovskyRationalOverlapExact nativeMembershipToCross and literalConvergenceFromCross, together with WidthReflection and OverlapBudget, already specify the consumer. A sound classical proof of the original interval bounds and literal Machin error yields lower(CH_k)<=M_k+e_k and M_k<=upper(CH_k)+e_k for every k. These are rational inequalities: reflect them through their actual numerator/denominator source equations, without asserting an undocumented isomorphism between Lean and Agda reals. The all-index reflection/translation itself must be proved, not assumed from finite digit matches. No new downstream adapter. F1 native prefix, A1 literal Machin semantics and A3–A5 certificate reflection remain the major unpaid producer gates. The production GMP path and F6–F9 unchanged.

## Attribution and evidence

Original Mathlib contributors retain analytic q chart and Eisenstein limit results, classical Hecke/modular functions, Ramanujan, Chudnovsky, Machin, Bishop/Bridges, Murray/Csimma retain attribution. Existing DASHI/JMD indexed and signed residual donors remain attributed as in the previous register. Latest PR metadata inspected (including newest Hopfion/Shem/ordered-cube lanes); no unrelated theorem imported and no donor modified. This cut applies the original limit owner to selected disk and writes source-specific certificate and period consumers. No formal solvedness promotion; exact head compilation and kernel acceptance unpaid.

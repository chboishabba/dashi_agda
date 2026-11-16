# BSD S1 — actual original Q₂ valuation producer and good-prime support; gate remains OPEN

16 November 2026. **Original gate S1 NOT CLOSED.** This round pays two independently identifiable mathematical producer obligations and exposes the remaining same-object cohomology weld. The expanded ledger remains **10/28 resolved, 18 open**, all six original Clay endpoints open.

## Original source audited

- \`DASHI/Mathematics/Arithmetic/EllipticSupportedSquareClassSieveExact.agda\` blob \`2979b3c64909cf6a136bb7dd5bdd03f806a3de19\`: the 16→8→4 finite sieve; explicit statement that original rational-square-class and local Kummer image predicates are supplied, not proved.
- \`DASHI/Mathematics/Arithmetic/EllipticRationalPlaceTwoDescentProducerExact.agda\` blob \`98a920f68832d71e6eb5a381170c057f5d18a059\`: \`archimedeanNecessary\` and \`dyadicNecessary\` fields of \`OriginalAllPlaceSieveEvidence\`, not constructed proofs.
- \`DASHI/Mathematics/Arithmetic/EllipticOriginalSelmerCohomologyExhaustionExact.agda\` blob \`e8a2d7507a91502b7829da8120cb21eac5ca9c45\`: \`genuineSUnitSupport\`, \`actualTorsionKummerCompatibility\`, \`globalCohomologicalSquareClassFaithful\` are fields of \`OriginalSelmerCohomologyRealization\`.
- \`DASHI/Mathematics/Arithmetic/EllipticRationalPlaceSelmerExact.agda\` blob \`3a9c1ec65cdb987c644863f305bc5f9ca06fac6c\`: \`GlobalCohomology\`, \`FiniteLocalCohomology\`, \`FiniteKummerImage\` supplied abstract carriers, not genuine Galois H¹.

## Actual Q₂ point valuation lemma, proved

Let \(E/\mathbb Q_2:y^2=x^3-x\), and \(P=(x,y)\in E(\mathbb Q_2)\) with \(x\ne0\). Let \(v=v_2(x)\in\mathbb Z\). For \(y\ne0\), the curve identity yields
\[
2v_2(y)=v_2(x)+v_2(x^2-1).
\]
- If \(v>0\), then \(v_2(x^2)>0\), so \(v_2(x^2-1)=0\), hence \(2v_2(y)=v\) and v is even.
- If \(v<0\), then \(v_2(x^2)<0\), so \(v_2(x^2-1)=2v\), hence \(2v_2(y)=3v\), and v is even.
- If \(v=0\), it is even.

For the 2-torsion points x=±1, v₂(x)=0. At (0,0) and O, the ordinary x-square-class is not defined and MUST be handled by the dedicated torsion Kummer representatives, not by division by zero.

Therefore every nonzero x-coordinate of an actual Q₂ point has even 2-adic valuation, and its square class in \(\mathbb Q_2^*/\mathbb Q_2^{*2}\) has even valuation parity. This is an **actual point-level necessary condition**, not a statement that arbitrary elements of H¹ satisfy it.

## Actual real point sign lemma, proved

For a real point with y≠0, \(x(x-1)(x+1)=y^2>0\). The cubic sign chart yields exactly \(-1<x<0\) or \(x>1\). In the first interval x and x−1 are both negative; in the second both positive. Thus sign(x)=sign(x−1). For 2-torsion, the sign convention uses the dedicated four original Kummer representatives, already in the source, not undefined square classes at x=0 or x=1.

## Good odd primes and S-unit support: classical theorem, not native instance

The discriminant is 64, so every odd prime p is good reduction. The prime-to-p multiplication-by-2 map on the Néron model of E is étale; for good reduction at odd p, the image of the local Kummer map \(E(\mathbb Q_p)/2E(\mathbb Q_p)\to H^1(\mathbb Q_p,E[2])\) lies in unramified cohomology. Because all three nonidentity E[2] points are rational, the Galois module E[2] is constant \((\mathbb Z/2)^2\), and \(H^1(\mathbb Q,E[2])\cong(\mathbb Q^*/\mathbb Q^{*2})^2\) by actual Kummer theory. Unramified at every odd p means both global square-class coordinates have even v_p at every odd prime, so each admits a representative from \(\{\pm1,\pm2\}\). This is the genuine **mathematical** S={2,∞} support theorem for global Selmer classes.

Its use requires the **actual** global/local Galois-cohomological Kummer identification, compatibility of local restrictions, and a consistent choice of basis for E[2] matching the repository's \`originalGlobalSquareClass\`. These are established classical theorems and choices but have not been instantiated in the Agda \`RationalPlaceTwoDescentData\` fields. Do not infer their kernel-checked existence.

## Why this does not yet close S1 or S3

The point-level dyadic parity and real sign conditions do not themselves prove the **cohomological** implications \`dyadicNecessary\` and \`archimedeanNecessary\` for the selected two-coordinate Kummer map. To lift them one must explicitly identify each local H¹ class with the square classes of x and x−1 (including torsion branch values), show all-place localization commutes with that identification, and show the global square-class representation is faithful. For S1, the original eight Q₂ witnessed classes must additionally be shown exhaustive for the actual local Kummer image, not merely as an eight-element list. For S3, the original 4 surviving global classes must be proved to exhaust the **actual** Selmer H¹ with no lost classes, then actual MW finite generation/rank must be deduced. The 16→8→4 sieve alone is not that proof.

**Exact new mathematical result:** the original curve's real sign and dyadic parity necessary conditions are proved at the level of actual points, with odd-good-prime S-unit support deduced classically. This is progress on original S1 producer dependencies, but NOT an accepted S1 gate closure. Do not change the canonical gate counts.

## Regression

\`scripts/check_clay_s1_actual_local_valuation_20261116.py\` checks exact rational points and valuation cases, sign intervals, original torsion exceptions and finite-code bounds; it does not certify all Q₂ points, which are covered by the preceding valuation proof, or all cohomology classes, which remain an open native weld.

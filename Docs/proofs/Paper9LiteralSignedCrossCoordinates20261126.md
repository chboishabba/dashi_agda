# Paper 9 — literal signed integer cross and strict source floor

26 November 2026. PR #1546; previous head c31c82bb. Source-written Lean/Agda, UNCOMPILED. Exact local arithmetic replay separate. Preserve original Chudnovsky, Machin, Bishop/Bridges, Murray/Csimma, pinned Mathlib and stdlib attributions. Reuse existing BishopMachinBindingManifestExact and BishopMachinPiLeanSemanticReceiptExact as provenance only: they explicitly do not import a proof term. No added postulate, new real carrier, CI or kernel receipt.

## Exact source coordinates

For the existing raw prefix (P,Q,B,T), E.prefixBOne gives B=1; E.prefixPStep, prefixQStep, prefixTStep supply P'=P p, Q'=Q q, T'=T q+P' a. The Lean Paper9LiteralFactorialPrefix.prefix has exactly this recurrence; its Q is Nat and P,T are Int. The Agda positiveView at nonempty index has numerator T and denominator Q, from PairedTotalityExact and WidthReflectionExact.sourceDen. The existing PrefixSemanticsExact identifies its rational value. Keep the sign of P and the zero prefix. No reduced-Rat byte identity.

The original cutoff and root scale are n=1+(k+4) div 41 and s=2^(k+2). Root source Floor.floorSquareRootUpToMaximal implies strict target < (r+1)^2 (not merely <=); the same maximality and square order show uniqueness. New declarations floorSquareRootNextSquareStrict and floorSquareRootUnique in the original FiniteNatFloorSquareRootExact.agda, commit cbce74cca25e49b844e2b7a0459cd6005d8411aa. Lean Mathlib Nat.eq_sqrt' yields exact unique Nat.sqrt of 10005*s^2. Both proof directions are source-written; no proof of inter-kernel equivalence from runtime scans required. The existing scan reference is not a performance algorithm.

Sort original adjacent prefixes by T_n Q_(n+1) <= T_(n+1) Q_n. If h is the high-prefix index and l the low-prefix index, the literal unreduced corner pairs are
    L=(426880*r*Q_h, s*T_h)
    U=(426880*(r+1)*Q_l, s*T_l).
The strict positivity of T for nonempty prefixes licenses natural denominators. Lean rawCorner, rawWindow, rawSort, rawWindowValue and rawWindowDenPositive are the source-shaped counterparts. At equality the existing left-on-tie branch is retained.

For the existing qMachinTerm(k), let a=(2k+1)*5^(2k+1), b=(2k+1)*239^(2k+1). Its unreduced numerator and denominator are
    ((-1)^k*(16*b-4*a), a*b).
This follows from the actual oneFifth, oneTwoHundredThirtyNinth, inverseOddRational, qPow, qSign, sixteen, four and unnormalised multiplication/subtraction. Original qMachinStage(0)=(0,1); stage addition (a,b)+(c,d)=(ad+cb,bd). Lean rawStageValue is an induction to the rational-valued machinStage. Radius (22,7) at 0, (4,25^k) otherwise. Lean machinRadiusSound uses the existing atanBracket and first-omitted term. Both omitted magnitudes bounded by (1/5)*(1/25)^k; 16+4=20 gives 4/25^k. At zero use the rational upper bracket with 3 terms of atan(1/5) and 2 of atan(1/239), strictly below 22/7. No fixed decimal approximation.

## Universal cross normal form

Write each actual coordinate as signed numerator N and positive denominator D. Exact equivalent integer comparisons:
    Ln*Md*Ed <= (Mn*Ed+En*Md)*Ld
    Mn*Ud*Ed <= (Un*Ed+En*Ud)*Md.
Use original order definition Q.*<=* (Agda Unicode *≤*) and preserve zero/equality; no absolute values, sign normalization or numerical tolerance. Agda BishopChudnovskySignedCrossReflectionExact uses actual O.window, Stage.qMachinStage, O.machinRadius. SignedLe, toOrder/fromOrder, SignedCross, toCross/fromCross; expandedToSigned/signedToExpanded expand the exact unnormalised addition using associativity. ExpandedCross is equivalent to SignedCross and its inhabitant feeds literalConvergenceFromExpandedCross, reusing CrossOnlyEndpointExact and existing width/convergence. Agda source commits 2b39f8fd38590d73c76271f5aa721d43645b14bf and dba6f14853a7d9718da04ceefd438cb4b839f2ac. No postulate of ExpandedCross.

Lean Integration/Paper9LiteralCross.lean commits 66c3df09f4c88399228c347ed252afdb55e2c00a, 94821c919fa54c77ec6ae07dc16f30b9e01a4c66, 8c6be8e3c09d40d66ade0d0c0142f023abc61afd, fb223368fa1a5ab91f78bfad27b7a645b2c5f08b: literal cutoff/rootScale/rootNumerator, stage/radius, error, fraction order, raw stage/corner values and positivity, RawCross and rawCrossFromFiniteChecks. Intended theorem eight explicit finite predicates -> forall k, RawCross k. Reuse literalPrefixFromFiniteChecks and rationalCross. No arbitrary root, period, stage, radius or denominator value as a premise. All new declarations UNCOMPILED; library API/tactic repair possible. Actual proof of the inter-kernel coordinate correspondence still required: the matched recurrences and source pinning establish a source-level specification, not a serialized proof. Agda ExpandedCross all-index inhabitant remains open. Do not call finite per-index checking an all-index proof; do not import a Bool or receipt as a theorem.

## Source pins and executed arithmetic

Inspected original Agda source at c31c82bb: HypergeometricBSplitIntegerMergeExact blob 92f4ca0bb72666503c2079d1d841755c44be0ef5, IndexedEdgeAlgebraExact 18599edad11788cd331f1a5cc2fdbddd117b896a, PairedTotalityExact d46cb6d9fada5f1b21b0a77be15ca59f361402fe, WidthReflectionExact f870224321ad9c71aef1ed0c71bfce04f147d288, RationalOverlapExact 96570e30d967afe3ad28f5f8b452f75ad7e18ead, original finite root aeb72f267282fb0715822f2c5aa51dc80398c381, Machin construction be11dee1db4eb6856346267134dcd85fed96fc2a, Machin window 83de91837cd4d2d75654448ce2d7d88d07c9dc98. Inspected Mathlib Nat.sqrt lemmas at pinned 8f9d9cff6bd728b17a24e163c9402775d9e6a365; inspected Agda stdlib v2.3 Unnormalised/Base and Nat/Properties APIs, not native elaboration.

Local exact checker scripts/check_paper9_signed_cross_coordinates.py executed with 90s timeout; PASS 5 exact gap coefficients, stage-zero rational bound, 129 unreduced stage/window/cross comparisons (258 expanded inequalities), 1000 signed fraction order/add controls, 1000 strict integer-floor uniqueness controls, explicit zero/equal/different-sign controls. Git blob 431b39b688e555120e0e244ca133f0458bd35353 local hash matches commit 50e009d57128e52caa28557c244ab88694dddb19. Reference regression uses Python integer/Fraction and SymPy, not executed Lean or Agda. Existing 513-stage normalized regression retained; not a full p=41 GMP/A3c replay, no native performance run.

## Remaining hard boundary

1. Elaborate and repair the complete Lean dependency chain; execute the eight finite native predicates, audit axioms and proof assumptions. No local Lean/Lake/Agda found.
2. Prove or transport the all-index actual raw coordinate and integer inequality witness into Agda, with native acceptance. Provenance and source matching alone cannot pay this; the existing native endpoint consumes a dependent function k -> ExpandedCross k. Either verified cross-prover proof translation for the relevant theorem or an independent native proof (e.g. original analytic period route) is necessary. Merely having a decidable inequality and finite PASS is insufficient.
3. Full independent GMP coefficient/prefix and performance gates, publication scope and external prior-art review remain. Higher jets stay off current pi critical path.

# Tian-Yau three-family, original E6 charges and zeta commuting square
Date 2026-11-18. Scope: source-backed exact comparisons; not physical TOE closure.

## Classical CY three-family route

The complete intersection in CP3 x CP3 has divisor multidegrees D1=(3,0), D2=(0,3), D3=(1,1). Define H1,H2 as ambient hyperplane generators. The total Chern class follows from the classical normal sequence:
c(TX)=(1+H1)^4(1+H2)^4/[(1+3H1)(1+3H2)(1+H1+H2)].
Its c1 is zero; c3=-8H1^3-H1^2H2-H1H2^2-8H2^3.
The ambient coefficient of H1^3H2^3 in c3*(3H1)*(3H2)*(H1+H2) equals -18.

Classical Tian–Yau and complete-intersection three-generation construction supplies a suitable smoothly acting FREE Z3 on a selected invariant smooth member, distinct from the nonfree Fermat-quintic coordinate permutation. The quotient therefore has Euler -18/3=-6 and Hodge (6,9), and heterotic standard embedding V=TX has net chiral family index magnitude |chi|/2=3. Published original geometry/freeness and heterotic index are prerequisites, NOT proved by the finite script or Agda arithmetic. Exact selected quotient polynomial coefficients, projective freedom proof, gauge-bundle descent, stable connection, cohomology and anomaly-safe worldsheet are still to be pinned and proven. This is a genuine classical three-generation alternative, not an observation-based new construction.

Primary geometric original references: Tian–Yau construction, https://people.maths.ox.ac.uk/~szendroi/cornertalk.pdf and Candelas/Lutken/Schimmrigk Complete Intersection Calabi–Yau Manifolds II: Three Generation Manifolds (1988), https://www.sciencedirect.com/science/article/pii/0550321388901733. Mathematical structure is not novel DASHI research.

## Actual original DASHI physical Standard Model charge source

Original user-developed DASHI first-Tits E6 27 PR #1106 and KK Higgs/physical PR #1241 ALREADY contain the E6-derived trinification group SU3c x SU3L x SU3R, orbifold-selected 27 chiral 16L + vectorlike 11R, source Chi33/E32/E21 VEV stabilizers, SU2L and hypercharge, post-E21 photon and faithful quotient. Existing executable owners:
- scripts/check_kk_e6_post_e32_sm_global_z6.py
- scripts/check_kk_e6_post_e21_u3_photon.py
- DASHI/Physics/Gravity/KKE6TrinificationDiagonalZThreeQuotientExact.agda
- DASHI/Physics/Gravity/KKQEDQCDHyperchargeBIDIExact.agda
- DASHI/Physics/Closure/U1YChargeAssignmentTableReceipt.agda
- DASHI/Physics/Closure/AnomalyCancellationVerificationReceipt.agda

Those source scripts derive the selected residual (SU3c x SU2L x U1Y)/Z6 with 6Y=-qz using the chosen original Higgs vacuum and the original 27 weights, and after E21 the selected (SU3c x U1em)/Z3, abstractly U3. The second source checks integral 3Qem and the original SU3 colour-triality congruence on all 27. q_z and the selected Higgs breaking determine the charge; it is NOT just KK fifth momentum n. Existing per-generation perturbative charge anomaly sums vanish on the selected original table but the 5D global eta/CS/WZ, actual Higgs vacuum and physical 10D geometric bundle remain open. The source original programme owns these results.

New scripts/check_string369_tian_yau_three_family_original_e6_join.py computes the Euler using SymPy and calls BOTH ORIGINAL executable scripts via runpy with exact 27 checks; it adds no copied/independent E6 charge list. The Chern algebra was independently verified in-session; this exact committed repo script has not been executed from a checkout here. New String369TianYauIndexThreeBoundaryExact.agda gives only conditional integer arithmetic; no geometric freeness or index theorem was implemented in Agda.

## Correct zeta commuting square attribution

The named zeta-square has multiple existing owners. DASHI/Analysis/ZetaIrrationalFibreCommutingSquareBidiExact.agda owns the generic finite StageCommutingSquare, consumer agreement and finite-stage coherence, without claiming analytic Riemann zeta convergence. DASHI/Analysis/BishopMachinQuantitativeZetaCommutingSquareExact.agda owns a different quantitative Machin/Bishop -> actual Riemann zeta square, conditional on analytic same-object continuity/domain witnesses. Never conflate analytical zeta(s) with the primitive third-root phase zeta_3/omega acting in E6's Z3 centre.

New String369TianYauE6ChargeZetaSquareExact.agda instantiates the ORIGINAL generic StageCommutingSquare on the literal first-Tits 27 central action: fine observer centralTrivialOn27(a,b,c), coarse observer diagonalZThree(a,b,c), commuting proof from ORIGINAL centreKernelIffDiagonal (all 27 source triples). The imported squareConsumerAgreement then preserves any downstream Boolean central-kernel consumer. This is an actual source-derived central-phase square rather than merely C3 label equality. It does NOT yet identify the Tian–Yau free geometric deck action with the E6 central kernel or original 369 physical spatial action.

The same module reuses original physical hypercharge source: up charge +4/6, electron -6/6, and proves no decoder using only arbitrary KK momentum n can recover all source qL/eR hypercharges (different charges can coexist at the same n). A physical charge bridge requires an explicitly chosen internal gauge bundle and E6-to-SM generator, with KK momentum either independent or mixed through a proved gauge/action mechanism.

## Remaining exact physical acceptance

1. Instantiate a concrete Tian–Yau smooth invariant F,G,H and actual free Z3 action; formalize quotient/holonomy and reproduce actual χ=-6 in kernel, not only externally.
2. Provide the same selected heterotic gauge bundle and its equivariant lift; Bianchi, Hermitian-YM stability, spin/Dirac chiral index and actual cohomology zero modes.
3. Connect FREE geometric deck Z3 to original E6 27 through a nontrivial Wilson line and explicit representation intertwiner; independently preserve the original SU3c/SU2L/U1Y global quotient and charge tables.
4. Full twisted/quotient-state and 5D/10D global η, Chern–Simons, Wess–Zumino, Green–Schwarz/anomaly conditions; not just perturbative anomaly sums.
5. Derive 4D field and action reduction from same 10D worldsheet/string/background and transport to original 369 Yang–Mills Wilson, same TSFV observer, gTPS/Hamiltonian and GRQFT metric variation.
6. Full original collider/low-energy phenomenology and held-out tests.
7. Exact new Agda head kernel acceptance and full checked-out Python script execution (not yet performed).

## Attribution rules

Historical Tian, Yau, Candelas, Lutken, Schimmrigk, Atiyah-Singer and heterotic theory original work retains its source authors. Johl Brown/DASHI retains original first-Tits E6/27, chosen Higgs/KK charge and 369/TSFV and zeta-square proof ownership. This round adds a conditional CICY Euler verification, source-joined checker, source-backed central-square reuse, independent bare-KK-charge obstruction, and this audit; no original physical 3-family or SM unification discovery is claimed.

## New explicit invariant representative: freeness independently checked

The extra source-aligned script scripts/check_string369_tian_yau_selected_free_c3_equations.py selects concrete homogeneous equations of bidegrees (3,0),(0,3),(1,1):

G(x)=x0³-x1x2x3+x1³+x2³+x3³,
H(y)=y0³-y1y2y3+y1³+y2³+y3³,
F(x,y)=x0y0+x1y1+x2y2+x3y3.

They are exactly preserved by simultaneous cyclic permutations x1→x2→x3→x1 and y1→y2→y3→y1. A projective fixed point for each factor lies either in its invariant projective line [a:t:t:t] or one of its two nontrivial eigenlines. On a nontrivial eigenline the corresponding cubic has value 2 (in a normalized coordinate), so cannot meet the intersection. On the invariant lines the equations reduce to a³+2t³=0, b³+2u³=0, ab+3tu=0. Eliminating a by the resultant gives t³(-2b³+27u³); using b³=-2u³ forces 31t³u³=0. Both t,u must be nonzero for valid projective zeros of the cubics, contradiction. This is an EXACT freeness witness for this selected algebraic complete intersection in characteristic zero, beyond merely assuming the historical existence of a free action.

Crucial boundary: smoothness/transversality of this VERY SAME selected triple remains UNPROVED (and cannot be inferred from generic smoothness or freeness). Until a no-singular-points Jacobian/saturation proof is produced, it cannot be promoted as an independently certified smooth CY3 or physical three-generation vacuum. The original literature independently establishes existence of smooth invariant free-action members; do not silently identify these with the above particularly simple coefficients. Next high-alpha task is the full projective Jacobian/transversality calculation or replace with published exact smooth coefficient data.

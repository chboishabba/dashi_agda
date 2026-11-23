# Clay non-RH/YM large bite — original-source physical and machine end-to-end reverse solve
23 November 2026 · Active PR #1542 · master-based, source-first, NO Clay promotion.

## Main mathematical result: original physical NS source sign-reversal, fixed coherent output

Read original owner chain (do not create a replacement Agda theorem owner):
- NSTriadKNPhysicalTriadEnumeration.agda, blob 78f57dd8776206a5172f8f7e13ff15e4e513dd20 — the actual cutoff-cube p+q=k; all incidences
- NSTriadKNPhysicalOutputFiber.agda, blob 87fcfadccb1af3320a22535da453379a45d42b94 — genuine output selection
- NSTriadKNPeriodicHelicalFourierInfrastructure.agda, blob 57dca27f479a49da0f9d169308e8af76b02c7a11 — original curl/Leray helical projectors
- NSTriadKNFixedOutputMixedCommutatorDampedTangentExact.agda, blob e4a8ecf10abf883094a565be367b553c7673e4ff — mixedProductCell = P+u(p) CROSS P-u(q)
- NSTriadKNMixedHelicityDampedProductTangentRound231Exact.agda — the product IS the original complex3Cross, not a freely stipulated cell vector
- NSTriadKNRawCurlFibreGramRound179Exact.agda — actual real-Hermitian work W(M,A)=2 Re<M,A>
- NSTriadKNPhysicalParabolicCriticalRegionRoutingExact.agda — physical R236 classifier from strict Round25 jp+3<jq (not <=)
- NSTriadKNFixedOutputInputLaplacianCriticalRegionPairBlocksExact.agda, blob 70034a0f53151bd03f58555b95874daf4d122bc7 — original SIX unordered signed blocks
- NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact.agda — original coherent covariance numerator and physical reduction.

### Literal original cutoff/output/zero-work carrier

Cutoff N=16, output k=(16,0,0), viscosity nu=1. The proposed cutoff N=15 is INVALID because the original physicalTriadEnumeration requires k itself within the cutoff cube. Correcting this source geometry gives:

    p=(x,y,z), q=(16-x,-y,-z),
    x=0..16, y,z=-16..16
    original fibre = 17·33² = 18,513 incidences
    sum of original r(p,q)=|p|²+|q|² = 9,972,336
    physical R236 tags: deep-FL 36, deep-HH 0, core 18,477.

Include ALL incidences, even when A_{p,q}=0 and w_{p,q}=0. Dropping those spectators changes the complete centered signed covariance, because N and the global rate total change.

Choose the genuine divergence-free Fourier initial velocity supported at modes +/- (1,0,0), +/- (8,0,0), +/- (15,0,0). For a positive x-axis Fourier mode j set h+=(0,1,i) and h-=(0,1,-i). Then:

    i e_x × h+ = h+;    i e_x × h- = -h-;
    h+ × h- = -2i e_x.
    u(j) = h+ + b_j h-,   u(-j) = conjugate(u(j)).
    P+(j)u(j)=h+,        P-(j)u(j)=b_j h-.

Thus the mode support is transverse, Fourier-reality-compatible, and uses the actual source helical cross product, NOT free independent A_i. Exactly three mixed-product output incidences are nonzero:

    (p,q)=(1,15), (8,8), (15,1)
    A_{p,q}=-2i b_q e_x
    r=(226,128,226), R236 tags=(deep-FL,core,deep-FL).

Take the exact one-parameter family b_1=b_15=t, b_8=3-2t.
Then for EVERY rational t:

    M = sum of all actual A = -6i e_x;   ||M||² = 36.
    sum w_{p,q} = 72.
    S(t) = -sum_{alpha<beta}(r_alpha-r_beta)(w_alpha-w_beta)
         = R_total*W_total - N_total*V_total
         = 547392384 - 87085152*t
         = 87085152*(44/7 - t).

The exact signs are:

| parameter t | (b1,b8,b15) | fixed ||M||² | complete signed S |
|---|---|---:|---:|
| 1 | (1,1,1) | 36 | +460,307,232 |
| 44/7 | (44/7,-67/7,44/7) | 36 | 0 |
| 13/2 | (13/2,-10,13/2) | 36 | -18,661,104 |

The complete six-block moment formula and an independently enumerated contribution of every ACTIVE-to-SPECTATOR pair, plus active-active pairs, agree exactly. The physical deep-FL / core routing is not merely an abstract label. All original 18,513 rates enter the scalar normal form.

**Source no-go paid:** even at this one fixed original finite cutoff, the genuine helical NS initial-data source admits BOTH signed covariance signs with identical M and ||M||², and |S(t)| is unbounded as |t| grows. Any proposal to pay the signed B1–B4 terms solely from M, its norm, and the fixed source geometry is therefore impossible for this family. A successful estimate must consume additional original physical data: individual modal amplitudes, legitimate input energies, differentiated norms/dynamical compensation and then cutoff-independent estimates.

This does NOT refute global Navier–Stokes regularity: the input velocity norm grows as |t| increases, and the argument is at the finite initial-data/source level. It is not a global-time regularity theorem or an Agda-kernel receipt.

Exact executed local reference: scripts/check_ns_original_helical_full_fibre_20261123.py. The original local prototype passed SymPy exact projectors/reality and full signed six-block active-spectator tests. The committed focused script is source-reviewed, but exact committed-blob execution should be repeated before claiming an exact-head test receipt. No GitHub CI.

### Reverse-solved remaining NS endpoint: not a sign guess

1. Start from the genuine p/q input amplitudes, cutoff, energy class, and exact original triad helical constructor, retaining every zero-work spectator.
2. Bound the combined FL/core/HH signed ledger by honest input-space controls: do not obtain sign from the fixed coherent M or independent region recentering.
3. Establish the actual cutoff-uniform analytic budget, physical commutator/tangent/endpoints and Galerkin continuation.
4. Use the original NSTriadKNPhysicalCriticalTouchingDefectBipartite20261007Exact and merged #1539 physical W2 counterexamples rather than resurrecting refuted unconditional positivity.

### A legitimate all-finite-source energy upper bound (not cutoff-uniform)

The genuine mixed-product structure also gives a replacement for an
impossible output-only bound. For arbitrary fixed-output physical
incidences define N=|F(k)|, R=sum r, mu=R/N, M=sum A and
B=sum (r-mu)A. The original signed covariance satisfies the **exact**
source identity

    S = -2N Re < M, B >.

Apply Hermitian Cauchy-Schwarz across the actual incidence family and
the standard complex cross-product Lagrange inequality:

    |S| <= 2N ||M|| (sum (r-mu)^2)^(1/2)
                       (sum ||A_{p,q}||^2)^(1/2)
        <= 2N ||M|| (sum (r-mu)^2)^(1/2)
                       sqrt(Eplus Eminus),

where Eplus=sum_{p in cutoff}||P+u(p)||² and
Eminus=sum_{q in cutoff}||P-u(q)||². The last inequality follows from
||a×b||²<=||a||²||b||² and the fixed-output pair sum being a subset of
the complete nonnegative (p,q) product sum. This is about the ACTUAL
same Fourier field, not a supplied numerical norm of arbitrary cells.

For the physical witness:
    mu=1616/3, sum(r-mu)^2=1,005,066,656, Eplus=12,
    Eminus(t)=4*(2t²+(3-2t)²), ||M||²=36.

The executable exact squared inequality reduces to a quadratic
polynomial in t with strictly positive leading coefficient and
strictly negative discriminant, thus holds for EVERY real parameter t.
This is a positive source-specific finite estimate consistent with
the sign reversal and growth in the genuine original input energy.

**Remaining blocker:** the prefactor 2N sqrt(sum(r-mu)^2) grows with
the cutoff. Bounding it without its large carrier price requires a
genuinely signed/cancelling R236/Bony and dynamical estimate; this
finite ceiling is NOT B1–B4 cutoff-uniform regularity control. Use it
as a valid fallback/negative-control metric, not a Clay promotion.

## Karp: original graph word all the way to first-enabled terminal observation

This cut reuses, rather than rediscovers, original Agda owner sources:
- Karp21NativeWholeBinaryPriorityMachineExact: actual ordered rules advance, finish, reject, original full bit-graph and 2m witness
- Karp21NativeBinaryToOriginalRawMachineStepExact: nonterminal same-source raw-state simulation
- Karp21NativeWholeBinaryStepPotentialExact and Karp21NativeWholeBinaryFiniteRunExact: at most m+1 source rule firings, **NOT** the physical bit time
- Karp21FinFreePairwiseQuadraticCountExact: correct original full-scan address comparison upper count 2m(m-1)
- Karp21NativeWholeBinaryVerifierOriginalExact: source-written all-word accept/reject parity, not kernel accepted.

The new complete differential script scripts/check_karp21_original_priority_end_to_end_20261123.py replays the literal original input grammar (gamma n+1, gamma m+1, m times signed triple, strictly-positive gamma W, no suffix). It includes malformed/truncated/extra-bit input, exponentially large vertex IDs in short gamma words, two bits per edge, signed arbitrary weights, chronological history, two signed ripple-ledger lanes and threshold. Source first-enabled rule order is advanced, finished or rejected with the exact terminal caveat: original raw cursor FINISHED means the threshold observation is still outstanding; it cannot be silently equated to BINARY ACCEPTED.

Independent local prototype execution PASS:
- 132,281 original graph-word/certificate cases, 7,012 accepted, 5,062 malformed source words
- selected bit-operation observed maximum 652; measured heap tally maximum 235; observed source priority steps maximum 5
- all decisions equal the separate direct-language parser/verifier; all phases/short/extra certificate cases match
- all observed source trace lengths <= m+1; all original history equality tests <= 2m(m-1); no full decoded-n label vector built.

The observed maxima are finite test diagnostics, NOT a worst-case physical TM-clock proof. The original selected E2 classical NP membership proof from ClayE2OriginalN21BitwordNPClassical20261115.md already exists and is NOT duplicated as new mathematics. This work targets the still open E1 selected FRACTRAN/priority bit-TM compiler.

### Reverse-solved remaining Karp source-to-physical payment

1. F1: compile the ACTUAL native gamma n/m/u/v/zigzag(w)/W parser and history/ripple/threshold branches into a single literal finite local TableProgram; charge malformed inputs too.
2. F3: give a concrete physical relation Rel(original raw/priority state, physical tape configuration), preserving exact word coordinates, histories, signed lanes, and terminal observation quotient with explicit bounded stuttering.
3. F2.2: pay EVERY live buffer, copy, stack, pointer, head and intermediate on the physical representation, not a reference list length.
4. F4: sum the TRUE head-local instruction counts into a single polynomial covering all original words and certificates; use the existing m+1 source potential only AFTER per-rule compilation.
5. G2/G3/G4: inhabit the original concrete PolynomialCostModel, polynomialTimeVerifier, polynomialCertificateBound and originalN21InNP, then receive local pinned Agda 2.9 acceptance.

No finite source trace or classical NP certificate implies the independent universal SATNotInP lower bound.

## Other two non-RH/YM lanes: do not inflate the counter

BSD selected E32 S5 is already established classically with Rubin attribution. Its inert-prime/twist symmetry does not identify actual same-E32 eta/Mellin or universal rank S6. Hodge (P1)^r has the classical complementary intersection/cycle inverse; repeated finite test counts do not solve generic all-variety H1/H3. No new artificial output is claimed for either lane in this cut.

## Mathematical/implementation trust

The exact finite source witness is stronger than an abstract free A_i model but does not instantiate a complete source Galerkin trajectory, prove a cutoff-uniform PDE estimate, provide a physical tape compiler, or typecheck Agda. No RH/YM development. Preserve original Karp, Waleffe and Lei–Lin–Zhou, Künneth/Hodge, Rubin/CM and original DASHI owner attribution. Zero of six original Clay problems proved here.

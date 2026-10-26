# Sharp horn regularity cut: one quickly shrinking branch, arbitrary SU(3) image

Date: 2026-10-25. Existing PRs: Agda #1249 and Lean #84. Source-original Hatcher horn group, original Agda #1244 A5/VOA and #1247 selected W remain individually attributed. This is a new conditional norm consequence, not a new horn embedding or experimentally demonstrated effect.

## Original mathematical input

Allen Hatcher, Algebraic Topology, Example 2B.2 pp. 170–172 (https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), identifies the exterior fundamental group as a direct limit of free groups with marked generator substitution m_w=[m_w0,m_w1]. The marked inclusion comes from the boundary of a once-punctured torus in the linked Z-block. Hatcher provides no quantitative arclength ratio for the particular later three-copy wild embedding.

For any two UNITARY matrices A,B, the elementary operator-norm identity

    d([A,B]) = ||AB-BA||op <= 2 min(d(A), d(B)),
    d(U)=||U-I||op

follows by right multiplication by the unitary BA and the triangle inequality. This strictly improves the previous correct but weaker quadratic-commutator single-branch factor FOUR to factor TWO.

For any honest homomorphism rho from the marked Hatcher exterior group to U(N), along ANY one marked depth-n descendant w,

    d(rho(m_root)) <= 2^n d(rho(m_w)).        [SHARP BRANCH]

There is NO finite-image prerequisite and NO requirement that all 2^n leaves are small.

## Flat source connection and exact finite-depth criterion

Suppose rho is holonomy of a FLAT unitary connection with compatible gauge frames. If gamma_w is a GENUINELY MARKED local representative of m_w of arclength L_w and the connection coefficient norm along it is bounded by M, standard unitary transport gives d(rho(m_w)) <= M L_w. Basepoint whiskers conjugate the holonomy, leaving d unchanged.

Therefore d(rho(m_root)) <= 2^n M L_w.

The other worker's originally selected W belongs to Agda neutrino #1247. Our earlier independent source character/norm certificate proves d(W)^2>=854996726408/648677790003>1, without any numerical eigensolver. If at some actual depth n a correctly marked loop obeys 2^n M L_w<=1, its flat bounded connection CANNOT have W as selected root.

For a TRUE geometric descendant branch with L_w<=L0*q^n and q<1/2, every finite uniform M eventually violates the selected root norm. This q<1/2 threshold supersedes the prior q<1/4 requirement based on the unnecessarily loose factor FOUR. No assumption that Hatcher's actual chosen three-copy geometry satisfies q<1/2 is made.

## Exact test receipt

New Agda #1249 script scripts/check_horn_single_fast_branch_unitary_cut.py checks exact rational rates with hypothetical M=100,L0=1:

- q=1/8 reaches the obstruction at depth 4.
- q=1/5 at depth 6.
- q=1/4 at depth 7.
- q=1/3 at depth 12.
- q=1/2 and q=3/5 never reach it for that positive M.

It also checks 31 exact depth thresholds. As a separate full-tree consumer, the quadratic commutator inequality yields the HETEROGENEOUS estimate

    2*d(root) <= product_{depth n leaves w} (2*epsilon_w),

when each leaf has d(U_w)<=epsilon_w. The binary scalar envelope identity was checked on 9 exact heterogeneous trees (through depth 8 with 256 leaves). This is more flexible than one uniform epsilon, but needs every leaf's bound.

New Lean #84 file Integration/DASHITOE/HornSingleFastBranchUnitaryCut.lean contains source-written finite-group-tree statements, arbitrary-depth source-conditional factor TWO theorem, exact rational q cutoffs and heterogeneous-tree product identity. Lean/Lake kernel NOT run. The true SU3 operator norm/flat holonomy analytic bridge is an explicit prerequisite rather than an imported, certified matrix theorem.

## Genuine geometric deliverable still open

A complete 3D source proof must exhibit the actual linked Hatcher Z-block; its van Kampen marked inclusion; coherent all-stage embeddings with clearance from every future horn; actual local marked meridian loops gamma_w and their arclength bounds; compatible basepoint stems/conjugacies; and a selected flat/bounded SU3 gauge connection. A symbolic commutator word, Cantor address, unlinked synthetic collar or merely shrinking handle diameter does NOT pay the geometric marking and LENGTH requirement. The nearby topology PR #1254 separately demonstrates that same-address combinatorics do not prove ambient linking.

A NONFLAT physical Wilson connection needs more: the Hatcher pi1 commutator identity holds on holonomy automatically only for FLAT monodromy. If actual loop concatenation is used instead, the chosen root loop and its word representative differ by a homotopy whose curvature/Stokes defect must be explicitly bounded. Existing FlatFormalDiskHolonomySurface owns those analytic interfaces.

This cut discharges a sharper CONDITIONAL mathematical constraint but not the source geometry, source physical metric, a Witten/Monster/369 same-object map, a neutrino prediction or a Clay theorem. Continue the actual linked Z-block marked-meridian construction rather than adding another C3/27 numerology layer.


## Further exact sharpness certificate: the factor 2 cannot be universally reduced

The bound d([A,B])<=2d(A) is OPTIMAL as a uniform all-unitary constant, not merely a convenient improvement. Consider, in SU(3),
A_n=diag(z_n,z_n^-1,1), z_n=(n+i)/(n-i), and
B=[[0,1,0],[-1,0,0],[0,0,1]]. Then B A_n B^-1=A_n^-1
and [A_n,B]=A_n². Consequently

    [d([A_n,B])/d(A_n)]²
       = |z_n+1|² = 4n²/(n²+1) -> 4.

The ratio tends to 2 as n→∞. Exact rational tests n=1,2,5,10,100,1000 PASS in the latest GitHub #1249 source script; independent explicit 3×3 SU3 numerical matrices corroborate the formula. Lean #84 source now states the rational optimality ratio and exact positive deficit 4/(n²+1); Lean kernel remains unverified.

This validates why the general selected one-branch geometric rate cutoff is precisely q<1/2 *for this universal per-level bound*. Geometry or representation-specific restrictions could still improve the factor, but cannot be assumed. It is an acceptance criterion, not proof the actual linked Hatcher blocks contract at q<1/2.


## New nonflat physical-interface cut: exact curvature/homotopy defect propagation

For a CURVED unitary gauge connection, the fundamental-group equality m_w=[m_w0,m_w1] does NOT establish equal holonomy matrices for independently selected geometric representatives. On an actual linked, based Hatcher Z-block let

    eta_w = ||Hol(gamma_w) - [Hol(gamma_w0),Hol(gamma_w1)]||op.

The eta_w must be independently produced from a genuine geometric homotopy plus transported curvature/non-Abelian-Stokes estimate, not set to zero because of the group relation. The optimal unitary commutator bound then implies for ANY chosen descendant branch of depth n

    d(Uroot) <= 2^n d(Uleaf) + sum_{k=0}^{n-1} 2^k eta_(ancestor at depth k).

If d(Uleaf)<=M Lleaf, the exact rejection condition for the previously certified selected d(W)>1 is

    2^n M Lleaf + sum_{k=0}^{n-1} 2^k eta_k <= 1.

This is a concrete acceptance test for either (i) a FLAT connection with eta=0, or (ii) a curved connection with REAL source-controlled homotopy defects. It prevents the prior physically invalid promotion of pi1 identities into arbitrary Wilson-loop equalities.

New committed exact Fraction script: scripts/check_horn_curved_branch_stokes_defect_cut.py checks the recurrence equals the explicitly weighted sum for 21 arbitrary heterogeneous depth fixtures; rejects a HYPOTHETICAL n=12 source with q=1/3, M=100, L0=1, eta_k=(1/100)(1/3)^k, whose exact bound is 8508407/10628820 ≈0.80050 <1. It also deliberately FAILS CLOSED for eta_root=2 and for the critical q=1/2. No selected geometric homotopy area, curvature, flatness, connection stress or physical source bound was constructed.

Lean #84 new Integration/DASHITOE/HornCurvedBranchDefectCut.lean source-writes an arbitrary branch error-envelope induction, proves monotonicity, and derives the finite source conditional curved-rejection theorem. The matrix norm/Stokes-to-eta analytical bridge is EXTERNAL/UNPAID and Lean/Lake kernel/typecheck NOT RUN.

The logical next producer is now a geometry+connection DOUBLE certificate: genuinely linked/marked Hatcher loops of quantitative length together with explicit based homotopy surfaces and their area/transported-curvature error, or a genuine failure of these in the selected three-copy embedding. Simply matching lengths or a symbolic commutator is not enough for nonflat physics.


## 2026-10-25 source reconciliation and stronger sibling-adaptive successor

The statement above that the *abstract* selected-W infinite-image horn-group representation is still open is **superseded** by independent Agda neutrino PR #1247, `tests/test_neutrino_horned_su3_positive_bridge.py`: Gotô's 1949 compact semisimple commutator-surjectivity theorem, applied recursively to Hatcher's marked injective free-group direct system, provides an abstract group representation with that specified SU(3) root. Flat-bundle existence on the open exterior follows by the standard universal-cover quotient. This says nothing about a uniformly bounded gauge potential, selected experimental spectrum or naturalness. Attribution: Hatcher and Gotô own the original mathematical theorems; #1247 owns the previously built DASHI positive bridge.

**New stronger geometrical interface**: `docs/hyperfabric-horn-sibling-adaptive-stokes-maxcut-20261025.md`, `scripts/check_horn_sibling_adaptive_stokes_maxcut.py`, Lean #84 `Integration/DASHITOE/HornAdaptiveSiblingStokesCut.lean`. The sharp sibling-dependent coefficient is 2*min(1,d(sibling)); the cumulative coefficient can decay SUPEREXPONENTIALLY if a genuinely marked sibling family has geometric length bound L0*q^k for any q<1. For FLAT bounded compatible holonomy, this forces the root to I without a shrinking terminal leaf or q<1/2. Curved transport keeps actual Stokes-area defects explicitly. This is conditional on source geometry, not a claim about Hatcher's actual metric embedding.


## 2026-10-25 spectral-arc sharpness and genuine nested-stage clearance (NEW CANONICAL SUCCESSOR)

The earlier universally sharp ***unconditioned sibling*** Lipschitz factor 2 is correct. With the ADDITIONAL source-specific sibling operator gap cap delta<=sqrt(2), centering B at the positive scalar lambda=1-delta^2/2 yields the better and SHARP fixed-delta coefficient 2 delta sqrt(1-delta^2/4). Consequently the qualitative flat sibling-tail contraction threshold is **delta_star=sqrt(2-sqrt(3))≈0.517638**, strictly improving the prior <1/2 sufficient cutoff. The old 1/2 theorem remains valid as a weaker corollary. See `docs/hyperfabric-horn-sharp-su3-arc-source-clearance-maxcut-20261025.md` for an original-source-attributed exact proof and tests. NO source-linked Hatcher loop lengths have been supplied to inhabit that cap.

Exact committed-source local receipts: `scripts/check_horn_su3_sharp_sibling_arc_cut.py`, byte-matched Git blob c436fb6870c453abd83ae21b0b4a15830172aaca, PASS; `scripts/check_horn_stage_clearance_c3_reuse.py`, blob f335654136997c2d985370f724a596b6d30b5cae, PASS. These are no more than mathematical exact/countercontrol tests. Lean #84 `HornSharpSiblingArcCut.lean` and Agda #1249 `HornStageClearanceC3SourceCutExact.agda` are SOURCE-WRITTEN, not kernel-checked.

Crucial geometry reduction using the ACTUAL original Hatcher nested compact X_n: a correct meridian lying in Y_n=R3 minus X_n cannot intersect any later X_m subset X_n or limit B, and positive clearance follows from compactness of its image and X_n. Rotational isometry from the actual three-satellite owner #1244 gives equivalent physical loop lengths in the other two sectors, conditional on the correct based generator marking. Thus P0 now asks for ONE SAME-OBJECT finite-stage meridian that avoids the entire stage X_n, has a source-certified free generator, and is metrically short; NOT redundant infinite future-clearance checks or three independently reconstructed copies. Hatcher original Ex2B2 pp171–172 owns the topology; Alexander 1924, Gotô 1949, Agda #1244 and #1247 own their respective prior mathematical/representation sources.

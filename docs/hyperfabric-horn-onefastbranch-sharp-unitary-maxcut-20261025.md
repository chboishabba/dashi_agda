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

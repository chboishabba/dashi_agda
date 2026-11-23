# YM P0/W3 — sharp five-exterior minimum relative to the original two-time tube (square-free mod-two source)

23 November 2026. Same original 4D SU(N) Wilson product-Haar source at L=4: 256 native gauge sites, 1024 native positive links, 1536 native positive plaquettes. Original normalized real Wilson marks F=((0,0,0,0),1,2), G=((2,0,0,0),1,2) separated by native Euclidean time two. Reuse the original eight-wall temporal tube T, the original single-omission census and the 24 cube-flip fourteen-face spheres; do not fabricate a new polymer object. Source geometry is GF(2) boundary of original 4D plaquettes. It is an admissibility test for square-free fundamental-orientation surfaces, not a full SU(N) representation or absolute W3 theorem.

## Exact source theorem and scope

Let B be the set of twenty original fine links in the ten-face closed surface {F,G} union T. Let E be the **1,525 original spectator plaquettes** not in T or the three original internal planes F/G/H, where H is the intermediate-time same-spatial plaquette. For any subset S of E with 1<=|S|<=4, and ANY subset A of T (retained original walls), the square-free 2-chain {F,G} union A union S cannot be mod-two closed.

In fact a stronger *outside-link boundary* property holds for every nonempty connected tube-rooted S of size at most 4: the GF(2) boundary of S on the original links not in B is nonzero, so no choice of A subset T (whose boundaries lie within B) can cure it.

**Exact exhaustive local source support enumeration** (native 1024-bit link XOR, no floating solvers):

| Size of connected tube-rooted exterior S | Distinct sets | Outside-link boundary zero |
| --- | ---: | ---: |
| 1 | 76 | 0 |
| 2 | 992 | 0 |
| 3 | 18,314 | 0 |
| 4 | 388,968 | 0 |
| **Total** | **408,350** | **0** |

Construction: root at an exterior plaquette containing at least one native link in B (exactly 76 roots). Expand sets via shared **external** native links, not via chart adjacency or merely common lattice sites, de-duplicate each set, test the 1024-bit XOR projected onto the complement of B. The first 1,525 exterior faces consist of 76 with three new links and 1,449 with four. A disconnected exterior set decomposes into components with pairwise disjoint external-link supports. If its total external-link boundary vanishes, the boundary of EACH component must vanish. A component that can affect the original tube must be connected through the original tube via one of the 76 roots; no such component of size <=4 has zero outside boundary. Moreover a nonempty totally unrooted component cannot cancel the F/G tube deficit, and no component of at most four external faces can be a closed standalone surface in the same native square-free incidence (each connected closed square lattice plaquette surface needs at least six faces). These facts justify the global (not only connected-family) minimum relative to the original T.

At size five there are at least 24 witnessed exact original native solutions: for each source 3D cube boundary c meeting exactly one wall q in T and neither F nor G, take S=c without q. Each 5-face S has outside-link boundary zero and full native link boundary exactly equal to the removed original wall q. Thus {F,G} union (T without q) union S is the original 14-face closed connecting sphere. There are 24 distinct resulting interaction 12-sets. Therefore **the minimum exterior cardinality is exactly FIVE**, in the class of square-free incidence-parity completions of this fixed eight-wall tube with F/G fixed and internal H not additionally inserted. This upgrades the prior documented cube-flip *witness* count to a sharp minimum for this precise class, not to a universal all-source analytic onset.

## Exact acceptance

New [standalone original-native checker](../../scripts/check_ym_w3_minimum_five_exterior_squarefree_20261123.py) reconstructs all 1536 original faces and the 1024 link incidence bits, enumerates all 408,350 rooted external connected support subsets through size four, verifies none cancels the projected external boundary, and verifies 24 independent genuine five-exterior cube replacement witnesses. An independently executed equivalent native Python enumeration returned precisely 76, 992, 18,314, 388,968 and zero cancelling subsets, plus 24 exact 3D-cube witnesses. The committed checker is SOURCE-WRITTEN and verified by GitHub readback; no claimed exact-byte checkout rerun, Agda/Lean kernel or GitHub CI.

## Exact W3 trust boundary

- **Paid:** the sharp original L4 square-free exterior link-parity support minimum 5 *relative to this tube and with only T-wall deletions*; all 24 original 12-coupling selected Haar character coefficients remain as previously proved.
- **Not paid:** that the first analytic correction at arbitrary exterior finite couplings is fifth order. Repeated insertions of a spectator face can leave square-free GF(2) and carry higher SU(N) character channels; additionally the original F/G/H internal plaquettes can be coupled, as already proved, and other original connecting paths compete.
- **Not paid:** any bound on the number/total absolute activity of **all** high-order Wilson surfaces, all homogeneous common-beta Taylor coefficients, actual renormalized CMP119/122 E/R/B/V and FP/Jacobian and 896 spectators, physical beta(a) running and cutoff-uniform rate or nontrivial OS same-H gap.

Next physically meaningful maximum-cut: derive an **absolute**, source-domination-correct activity ledger for the family of all original differentiated CMP116 connecting clusters, splitting square-free outside-link support classes from repeated-face/multiple-character classes; reuse `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell` and `BalabanLiteralTwoWilsonSourceFirstJetLocalizationExact.SourceFirstLiteralWilsonJetLocalization.localizedLiteralShellChargeSum`, which remain conditional. Retain physical Euclidean time t, Singer chart index k, RG scale and original zero-branch/sign residuals separately.

Attribution: original Wilson action and product Haar, elementary original 4D lattice homological parity, standard Peter-Weyl/Schur SU(N) fundamental contraction for preceding 24 sphere coefficients, original DASHI 8-wall and cube-flip source owners and Bałaban CMP116/119/122. No Clay or kernel completion claimed.

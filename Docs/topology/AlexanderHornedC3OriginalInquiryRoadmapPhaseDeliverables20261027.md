# Alexander horned C3 — original inquiry, max-cut phases, deliverables and acceptance (2026-10-27)

**Current implementation:** [PR #1244](https://github.com/chboishabba/dashi_agda/pull/1244), draft, on `alexander-horned-c3-equivariant-20261024`.
**Stacked geometry/end-space comparison:** [PR #1254](https://github.com/chboishabba/dashi_agda/pull/1254), draft, **BASE = PR #1244's branch**, not an independent master merge.
**Independent analytic/cyclotomic inquiry:** [PR #1260](https://github.com/chboishabba/dashi_agda/pull/1260), draft, base master.
**Scope:** source-authored mathematics, formal proof interfaces, explicit geometric choices, finite executable tests, and separately scoped experimental proposals. Nothing in this document certifies exact-head Lean/Agda compilation or a physical discovery.

## 1. Return to the original question

The foundational geometric inquiry is whether three chosen, supported copies of the CLASSICAL Alexander–Hatcher horned wild solid, joined by an ordinary star of tubes in Euclidean three-space, yield a genuine (C_3)-invariant embedded topological ball with

```text
 E := S³ \ B;
 π₁(E,x₀) ≅ G_A * G_A * G_A;
 [R_*] ∈ Out(π₁(E,x₀)) has exact order 3.
```

Here `G_A` is the nontrivial perfect one-sector Hatcher exterior group, not an arbitrary perfect finite quotient. The research needs three distinct answers: **(i)** a valid source-supported classical/PAPER construction, **(ii)** a fully specified same-object ambient proof with exact-homeomorphism/collar witnesses, and **(iii)** a kernel-checked formalization. A finite simulation does not pay (ii) or (iii).

The nearby SECOND inquiry asks whether a finite, programmable nonabelian flat gauge emulator can show a robust **relative** SU2 `-I` Wilson signal and recursive commutator compatibility. The signal is a design/emulation test, not a manufactured wild topology or spontaneous spin holonomy.

The #1260 `π,e^i,9999!` / Pickover inquiry is a THIRD, **independent** signed real-angle problem. Reused C3 roots and CRT residues are representation-level cross-pollination, not a route from the wild exterior to `sign(sin(99^(9999!)))` without a new analytic attachment.

## 2. Source roots and non-promotion boundaries

| Root / owner | What it actually proves / implements | Not automatically established |
|---|---|---|
| J. W. Alexander, *An Example of a Simply Connected Surface Bounding a Region Which Is Not Simply Connected*, PNAS (1924) | Original wild embedded sphere | OUR rational C3 placement |
| A. Hatcher, *Algebraic Topology*, Example 2B.2, author-PDF pages 179–180 / printed pages 171–172, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf | Decreasing X_n handlebodies, increasing exterior Y_n, π₁(Y_n)=F_(2^n), injective commutator maps, compactness and direct limit | A kernel witness for OUR three-sector relative collar |
| F. Lippert, *The Alexander Horned Sphere and Bing's Hooked Rug*, §§2.1–2.3 | Source-supported shrinking horn stages and undisturbed patches | Coordinate-by-coordinate infinite-stage Lean embedding |
| Classical van Kampen, Schoenflies, tame tree-neighbourhood and based-path transport | Group gluing for certified geometric covers | A proof that the chosen source covers/homotopies exist |
| Deicyde/hatcher-at (pinned `fb20d71`), Mathlib | Existing `coprodIEquiv`, homotopy/pointed transport, `IsPathConnected.union`, van Kampen consumer | A checked DASHI exact-head import or new geometric maps |
| DASHI #1244 pre-existing code | C3 scaffold, source-side Agda meridian algebra, 2I recursion, clopen finite tests, conditional Lean cover/group adapters | Exterior group of a fabricated finite tame ball |
| DASHI #1254 recent source branch | Chronological cylinder orientation, PL ancestry, bounded genus-zero surface caps, Richards-end interfaces | Wild Hatcher X_n handlebodies or a Richards infinite realization |
| Machin (1706); Lindemann (1882), Weierstrass (1885); Manuel Eberl AFP (2021) | Original arctangent identity, analytic transcendence, actual Isabelle formal theorem | Signed Pickover phase, or an imported Lean/Agda theorem |
| Sugawa et al. (2021), Liang et al. (2024) | External NONABELIAN synthetic-gauge experiments in their selected systems | Experiment on our wild solid or automatic physical flatness |

Original roots, reprints, independent measurements, theorem statements, source code, finite tests, toolchain receipts and empirical observations must be distinguishable in every claim.

## 3. Phase ledger: actual closures and missing acceptance

| Phase | Mathematical / deliverable target | Status and source | Exact remaining acceptance |
|---|---|---|---|
| A. Historical one-sector mathematical source | Hatcher's F_(2^n) commutator tower; G_A perfect nontrivial | ORIGINAL classical construction; prior DASHI word/group probes and formal interfaces | No reinvention; retain original pages/coordinates and the source-vs-printer distinction |
| B. Three-sector explicit finite scaffold | c_i=9e_i, radii 15/4 and 17/4, spokes, separator sphere disks, C3 orbit | Rational geometric construction and executable checks in #1244 | Actual chosen wild satellite maps must fit their reference envelopes and preserve stationary caps |
| C. Intrinsic end cylinders / clopen balls | Three binary Cantor address copies, mass, C3 orbit, chronological append correction | Existing Agda sources; tame Euclidean comparator; #1254 owns generic orientation theorem | NEVER substitute the tame Cantor image for a wild ambient embedding |
| D. Point-set cover and overlap | The relative OPEN cover U_i=C∪S_i, pair/triple overlap C; pierced-shell interval×disk chart | Actual formulas and Lean **source-written** radius adapter | Pinned Lean compile; instantiate metric inclusion E→R³ |
| E. Connectedness reduction (THIS CUT) | Avoid assuming each U_i path-connected separately | New `ThreeArmRadiusConnectedAssembly.lean` composes Mathlib `IsPathConnected.union` with literal p_i∈C∩S_i; `scripts/alexander_horned_c3_radius_overlap_witness.py` reuses original geometry. Independent exact rational p_i/c_i audit PASS | Show C and S_i individually path-connected in the **actual** wild exterior; actual Lean `p_i:X` with membership, not merely ambient coordinates; exact-head kernel check |
| F. Central π1 | `π₁(C,x₀)=1`, although `H₂(C)=Z` in R³ | Classical tame-tree/Schoenflies argument; `ThreeArmCentralPi1Reduction` consumer | Explicit tame-tree ambient equivalence or suitable existing formal theorem and kernel witness |
| G. Hatcher relative satellite → member | Genuine source space W_i, homotopy equivalence W_i≃ₕU_i, based path to x₀, induced meridian map | Real conditional interfaces in `ThreeArmHatcherPathTransport.lean`; source Hatcher construction | **PRINCIPAL OPEN GEOMETRIC GATE**: map actual linked handlebody/exterior tower through preserved cap and collar, all finite stages and limit |
| H. Ambient group and outer C3 | `π₁(E) ≅ G_A*G_A*G_A`; rotation noninner order3 | Classical paper-level gluing and algebraic factor argument | G/F + actual C3 naturality + Lean source typecheck. Do not report this as a fully internal theorem earlier |
| I. Flat gauge finite emulator | 2I=120 commutator section; q³=-I, Q8 negative control; U6 three channels; synthetic noise/shot model | Runnable bounded finite implementation with protocols; no lab observation | Actual independent physical plaquette flatness, calibration, hardware controls if an empirical claim is desired |
| J. Analytic Pickover cross-project | `sign(sin(99^(9999!)))`; exact e^i seeded complex power, Machin pi enclosure | #1260 moderate-exponent signed regressions and CRT non-descent; phase sign UNKNOWN | Effective certified terminal real-angle separation, with both producer and verifier resource cost |

### The three indispensable finite / ideal objects (do not collapse them)

1. The finite **tame expanding ball** `B_n`: smooth/tame boundary, simply-connected exterior by tame Schoenflies.
2. The finite **enclosing handlebody** `X_n`: genus `2^n`; exterior `Y_n=R³\X_n` has `π₁=F_(2^n)`. Its three-sector analogue has rank `3*2^n`.
3. The **wild limit** `B=⋂X_n`: source exterior `E=⋃Y_n` has nontrivial PERFECT `π₁` but trivial `H₁`, via commutator bonding. In R³ the exterior has `H₂=Z`; in S³ the complement has trivial reduced homology.

A finite genus-zero capped PL sphere from #1254 is not the source Hatcher handlebody `X_n`, even if its boundary is a combinatorial sphere and its ends use the same tree.

## 4. Current exact residual after the new connectivity reduction

```text
OWNERS / ALREADY PAID
  [source]   Alexander + Hatcher supported wild one-sector geometry
  [finite]   C3 centres, radius inequalities, p_i = 13 e_i,
             distinct satellite balls, pierced-shell atlas, basepoint paths
  [Lean-src] literal metric radius-core / radius-arm sets, open cover,
             disjointness, coverage, central-to-overlap pi1 reduction,
             IsPathConnected(C union S_i) from C, S_i and C∩S_i≠∅,
             source W_i homotopy+basepoint-path -> ambient pi1
  [Agda-src] finite word/address and abelian-character blindness
  [Python]   2I source recursion and finite Wilson synthetic controls

OPEN ACCEPTANCE LEAVES (minimal consumer-shaped input)
  G1  specified same-object supported Hatcher wild ball B_A with
      explicit stationary inward cap and linked stage X_n maps
  G2  actual π1(C)=1 + IsPathConnected(C) (tame star complement)
  G3  IsPathConnected(S_i) and actual X-valued overlap p_i
  G4  source W_i ≃_h U_i and meridian-map naturality for all sectors
  G5  geometric C3 transport of G4 and exact-head Lean/Agda kernel build

PRIORITY: G1/G4 are the bottleneck; G2/G3 can be handled separately,
using prior Mathlib/topology modules without another free-product engine.
```

Do not invent `G1/G4` by asserting a group equivalence that is merely
isomorphic on finite labels. The user-supplied "assume already in repo"
means exhaust donor archaeology, including the **source** handlebody
and supported cap modules, before introducing a new existence premise.

## 5. Pareto/snowball/Ibrahim implementation sequence

**Cut P0.1 — paid finite geometry:** maintain one canonical actual-cover test import path. The new test directly imports the existing `alexander_horned_c3_explicit_open_cover` and `equivariant_basing_paths`, rather than copying formulas. It certifies `|p_i-c_i|²=16`, `|p_i-c_j|²=250 (j≠i)`, `|x₀-c_i|²=921`, true overlap, support-envelope exclusion, rotation, and deliberately invalid `12e_i` and `14e_i` controls. Coordinate witnesses by themselves do not prove path-connectivity or wildness.

**Cut P0.2 — exact topology:** use the pinned Hatcher-at `StrongDeformationRetract.fundamentalGroupMulEquivOfEq`/homotopy and standard based-path APIs to formalize a relative satellite cap-slide and central tame complement. Compare directly with Hatcher Example 2B.2's *annular/punctured-torus* patch; treat a sphere-minus-disk as a different cut in the later threefold gluing. Complete the actual chosen stage geometry and meridian mapping, not a fresh group presentation.

**Cut P0.3 — proof kernel:** run `lake build HornedC3` under pinned versions. Run the focused Agda modules via `scripts/check_alexander_horned_c3_exact_head.sh`. Record actual commit SHA/toolchain/log and every error; no release-ready status without an affirmative receipt. If a source theorem fails, repair it first without weakening the geometric hypotheses or adding an axiom.

**Cut P1 — physical feasibility:** publish the finite emulator's depth/noise/shot protocol and actual independent controls. If a device is ever chosen, require verified flatness and relative interference. A graph gauge demonstration and a sculpted wild-looking solid are categorically different experiments.

**Cut P1b — Pickover resource certificate:** #1260's repaired fixed-point `e^i` source and signed-`99^k` controls are genuine finite analytic progress. Its exact new budget audit
`scripts/check_pickover_factorial_pi_interval_width_budget.py`
checks `E=9999!` (35,656 decimal digits; 118,445 bits).
Since `99^10>10^19`, `N=99^E>10^(19E/10)`.
For ordinary full-width `π` brackets `[L,U]⊂(3,4)`
with `U-L=10^(-P)` and
`P≤19E/10-2`, `N/L-N/U>100/16>1`.
Thus this CERTAIN NAIVE interval method cannot isolate a single winding
bin at that P. This is not an information-theoretic lower bound for every
algorithm and does not give the terminal sine sign.

**Cut P2 — write-up and experiment boundary:** one original-source math
paper separates the classical threefold gluing proof from fully
machine-checked claims. A second finite-gauge methods report specifies
U6 controls and noise statistics; any empirical paper requires data.
The Pickover problem remains a separate analytic manuscript/proof target,
not a purported consequence of wild topology.

## 6. Completion / deliverable sign-off matrix

- **D1 Mathematical note:** explicit chosen `B`, source citations,
  untouched cap charts, a detailed argument for relative collars,
  actual threefold cover, and C3 outer-action naturality.
  **Paper-level only until every cited existence map is specified.**
- **D2 Formal Lean root:** `HornedC3.lean` importing the exact
  metric cover, connectedness reduction, central π1, group/homotopy
  transports. **SOURCE-WRITTEN; exact-head receipt outstanding.**
- **D3 Agda group/end sources:** original Horn word, compatible 2I,
  chronological Cantor-cylinder orientation and mass, abelian BIDI,
  with original source roots. **Do not claim intrinsic end homeomorphism
  implies exterior homeomorphism.**
- **D4 Reproducible finite tests:** current cover, basing, overlap, 2I,
  Wilson noise/shot and destructive controls in focused Python workflow;
  exact source run + log should be attached before claiming a green
  head.
- **D5 Analytic Pickover certificate:** terminal real phase bound and
  signed verifier. **OPEN**, notwithstanding exact CRT and selected
  six moderate-`k` signs. Resource audit documents why ordinary brute
  π enclosures are not a solution strategy.
- **D6 Applied/prototype evidence:** no hardware measured; realistic
  null/positive experimental comparisons remain planned.

## 7. Exit and attribution rules

The programme is **not fully complete** until the specific wild
embedding and source member retractions are constructed and proof-checked.
No amount of finite images, repeated web reporting, modular phase labels,
coinciding scalar traces, or additional unmerged sibling PRs discharges
those maps. Do not call a topological model physically measured.

Provenance tiers to track by deliverable: original root → independent
source/exposition → repository-specific derivation → source-written
code → locally executed finite test → exact-blob/CI receipt →
kernel-verified formal theorem → independent experimental measurement.
A result may remain valid at an earlier tier without inheriting later
tiers. Do not overwrite earlier owners or present external results as
new DASHI inventions.

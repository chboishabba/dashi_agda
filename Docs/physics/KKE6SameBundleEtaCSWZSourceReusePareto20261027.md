# E6 orbifold eta / CS / WZ reuse: one same-bundle max-cut (2026-10-27)

## Scope / acknowledgement of existing source owners
**Correction to prior repo-search claim:** The repository DOES already contain eta-, CS-, WZ- and inflow-related content. The problem is not a complete absence of those concepts. The actual reusable owners include:

| Owner | Actually available | Not transported automatically |
|---|---|---|
| `DASHI/Physics/QFT/FermionicLoopCSShiftReceipt.agda` | candidate 2+1D SU2 CS fermion level shift | 4+1D spin CS or regulated eta on H |
| `DASHI/Physics/QFT/BulkBoundarySU3Receipt.agda` | conditional 2+1D SU3 boundary / 3+1D bulk reading | 4D fixed-plane H anomaly |
| `DASHI/Physics/QFT/CSLevelFlowFullReceipt.agda` | level-flow candidate bookkeeping | selected E6 quotient gauge theory |
| `DASHI/Physics/Closure/KTheoryNovikovReceiptSurface.agda` | typed `globalAnomalyEtaInvariantTarget` | constructed spectral eta/Pfaffian and APS boundary condition |
| `DASHI/Physics/Gravity/KKMinkowskiChernSimonsFiveDConsumerExact.agda` | non-transport of 3- vs 5-form; finite five-form checks | global quantized CS5 |
| `DASHI/Physics/Gravity/KKE6OrbifoldCSWZTransferConsumerExact.agda` and `scripts/check_kk_e6_orbifold_cs_wz_anomaly_transfer.py` | selected polynomial, independent endpoint variations, one-end Chi33 WZ cochain cancellation | quotient differential cocycle and regulator |
| `DASHI/Physics/Gravity/KKE6TrinificationDiagonalZThreeQuotientExact.agda` | faithful quotient and finite nontransport | full spin-bordism classification |

The already implemented first-Tits 27 action is owned by **Agda #1106**. Physical orbifold, parity, Higgs, source, anomaly transfer and this cross-owner join are owned by **Agda #1241**. Native rational Albert/other representation carriers in Lean #52, Agda #1098, and Lean #84 are not silently identified with this physical action. PR #1266 supplies the consumer non-descent method; the newer source-first optical PR #1272 supports same-device rather than analogy-based claims. Nothing imports team-governed ESD.

## New single-object witness: anomaly free period and Higgs zeros intersect

Use exactly the source-selected parity-even faithful boundary group

`H=[SU3c x S(U2xU1)L x S(U2xU1)R]/Z3_diag`.

On the closed spin **sixfold** `X=(S2)^3`, choose the following triples of parity-even equator clutch paths. Each cell is `(p,m,n)`, interpreted by the actual group path
`diag(exp(2πi(p/3+m)t), exp(2πi(p/3+n)t), exp(-2πi(2p/3+m+n)t))`.

| S2 factor | SU3c | SU3L | SU3R |
|---|---|---|---|
| first | (1,1,0) | (1,0,0) | (1,0,0) |
| second | (1,1,0) | (1,0,0) | (1,0,0) |
| third | (1,0,0) | (1,1,0) | (1,0,0) |

All 9 paths begin at I and end at the same diagonal Z3 element omega I, commute with the parity, and therefore define a genuine **single nonliftable H principal bundle** on X. Restriction of this bundle to the sixfold's embedded S2 factors has common p=1 lifting obstruction. Each 27 weight line descends, because the diagonal Z3 acts trivially on the original first-Tits representation.

1. `Chi33`, the parity-even `(1,3L,bar3R)` singlet, has equator clutch degrees `(0,0,-1)`. Hence its associated line has nonzero `c1=-u3`, so no global nowhere-zero Chi33 section is possible on this bundle, by the standard line-bundle clutching theorem.
2. The SAME bundle's complete parity-signed 27 Dirac indices on X, evaluated with the spin Atiyah-Singer product formula, are `A=-24`, `B=+13`, `C=-1`, total `-12`, so the half-index is `-6`. The underlying complete unsplit 27 index is zero; parity-positive and parity-negative indices are `-6` and `+6`.
3. Existing local source cochain still satisfies `(I6/2,I6/2)+(+I6/2,-I6/2)=(I6,0)` and local `Chi33` WZ cancellation **where the phase is defined**. Those equalities do NOT construct WZ on the forced-zero bundle.

The sixfold is an **index period/obstruction test manifold**, NOT asserted to be the physical five-dimensional orbifold spacetime or a full APS boundary geometry. Its topology exposes a real defect in attempts to extend a pure unpatched phase-only boundary WZ uniformly to all admissible H-bundles. Pullback/restriction to an appropriate 4D fixed-plane geometry separately requires its own source boundary conditions. Nonzero index is not by itself a proof of a nontrivial global gauge anomaly.

New `scripts/check_kk_e6_same_bundle_eta_cs_wz_join.py` **runs the actual existing Python owners**, tests this single bundle on both index and Chi line, verifies local source cochain and the quotient mixed-instanton donor, and ensures named 2+1D, 5D, eta-target and local inflow files remain distinct. No new duplicate group-action model or anecdotal finite analogue. `DASHI/Physics/Gravity/KKE6EtaCSWZSameBundleConsumerExact.agda` reuses actual Agda owner modules and requires proof-relevant constructor types for physical completion. Its finite Bool labels and toy possible eta-sign pair are deliberately **not** Dirac-spectrum kernel proofs.

## Pareto/Ibrahim decision, snowball source roots
The **free-period spin index criterion** is paid analytically using the classical Atiyah-Singer theorem together with the source 27 decomposition, not as a new original general index theorem. The **unpatched phase-only all-bundle Chi33 WZ ansatz is obstructed**, including on the same bundle that exercises a nontrivial signed index. These conclusions do not obstruct a patched/defect-aware WZ action or another compensator.

The next highest-value non-dominated proof input is therefore **not** another spin-index sample. It is one *selected-H-bundle* spectral/differential-cocycle construction which produces:
- a physical 5D Dirac domain (including orbifold endpoint conditions), an APS/eta or equivalent determinant/Pfaffian-line phase and its response to all admissible small/large gauge transformations;
- a fully normalised exponentiated CS5 contribution on the faithful quotient, accounting for the diagonal Z3 class and correlated Abelian charges;
- a globally extended WZ/Goldstone/defect functional on the actual scalar configuration space, including Chi33 zero loci;
- one proof of the combined phase identity on the **same** action, coupled sources and allowed configurations, before importing it to the interval spectrum/stress/observable owners.

The 2+1D CS and K-theory eta receipts are useful conceptual/typed inputs, but still require physical dimensional/representation/action adapters. Positive flat/free index and mixed PSU3 period calculations do not automatically determine torsion eta phases.

### Original literature roots; no duplicate corroboration
- X. Dai & D. Freed, *eta invariants and determinant lines* (1994), J. Math. Phys. 35, 5155, preprint [hep-th/9405012](https://arxiv.org/abs/hep-th/9405012).
- E. Witten & K. Yonekura, *Anomaly Inflow and the eta-Invariant* (2019 preprint / 2020 publication), [arXiv:1909.08775](https://arxiv.org/abs/1909.08775); globally refined inflow. Preprint and journal are **one original root**.
- K. Yonekura, *Dai-Freed theorem and topological phases of matter*, JHEP 09 (2016) 022, DOI [10.1007/JHEP09(2016)022](https://doi.org/10.1007/JHEP09(2016)022); eta/determinant-line method.
- G. von Gersdorff & M. Quirós, *Localized anomalies in orbifold gauge theories*, Phys. Rev. D 68 (2003) 105002, DOI [10.1103/PhysRevD.68.105002](https://doi.org/10.1103/PhysRevD.68.105002); original local cancellation and GS distinction.
- M. Scrucca, M. Serone, L. Silvestrini & F. Zwirner, *Anomalies in orbifold field theories*, Phys. Lett. B 525 (2002), [hep-th/0110073](https://arxiv.org/abs/hep-th/0110073).
- A. Hatcher, *Vector Bundles & K-Theory*, original vector-bundle clutching reference, https://pi.math.cornell.edu/~hatcher/VBKT/VBpage.html.
- K. Yonekura, *General anomaly matching by Goldstone bosons*, JHEP 03 (2021) 057, DOI [10.1007/JHEP03(2021)057](https://doi.org/10.1007/JHEP03(2021)057); methodological global WZW completion donor.

The original sources **do not** themselves prove the repository-specific Chi33 winding or the signed index -12 on this selected bundle. Those are source-derived calculations owned by the selected KK programme (Johl Brown / OpenAI ChatGPT-assisted implementation). A paper, a preprint of that paper, an interpretation and a Python script are not four independent experimental confirmations.

## Verification / stop boundary
- Current source-level GitHub commits and checks are not Agda/Lean kernel receipts.
- Local *independent* exact-Fraction calculation of the same chosen 27 bundle reproduced signed indices A=-24, B=+13, C=-1, total -12, and Chi33 degrees (0,0,-1). The GitHub head regression imports the owner scripts but was not executed byte-for-byte in this environment.
- Neither a globally quantised 5D eta-CS-WZ cancellation nor a physically stable quantum vacuum is established. The proof-level obstruction is a missing same-source spectral eta/differential-character functional with a defect-aware WZ extension, **not** an absent eta/CS/WZ vocabulary or a missing finite representation.

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


## 27 October full-boundary-Cartan theorem (stronger than single-bundle witness)

New owner: `scripts/check_kk_e6_chi33_full_cartan_anomaly_factor.py`, also consumed by `scripts/check_kk_e6_same_bundle_eta_cs_wz_join.py`.

Let `c0,c1,c2=-c0-c1`, `l0,l1,l2=-l0-l1` and `r0,r1,r2=-r0-r1` denote formal Chern roots of the three SU3 maximal tori. The selected parity-even boundary group only requires the S3 colour and S2L×S2R doublet Weyl permutations. Define
`D=l2-r2=r0+r1-l0-l1`, the *actual original C33 Higgs line character*.
For the selected orbifold signed 27 virtual representation `Eplus-Eminus`, exhaustive sum of the **same 27 source weights** gives

`ch1^signed = 8D`;
`Tr_signed(F^3)=4 D Q`, with
`Q=3(c0²+c0 c1+c1²)+2(l0²+l1²+r0²+r1²)+l0 l1+r0 r1+2(l0+l1)(r0+r1)`.

The 4-form `Q` is invariant under S3c × S2L × S2R, so by the standard rational splitting principle the polynomial identity is meaningful as a rational characteristic-class identity for ALL principal H bundles, not only torus-split ones. Using the classical spin Dirac index theorem on any closed spin sixfold X,

`ind(D_Eplus)-ind(D_Eminus) = integral_X D*(2 Q/3 - p1(TX)/3)`

with the convention that the formal Chern roots represent integral first Chern classes and `ch3=Tr(F^3)/6`.

**New consequence:** if `c1(L_Chi33)=0` in rational cohomology, the perturbative/free sixfold index vanishes. Conversely, a **nonzero free signed index** forces `c1(L_Chi33)≠0` rationally, hence the complex line bundle has no nowhere-zero continuous section; the phase-only Chi33 WZ is obstructed *on every such nonzero-index background* unless the action provides patches, defects, a restricted field domain or an alternative UV completion. This is a source-specific statement about an unpatched scalar-phase ansatz, not a general no-go against all WZW anomaly matching.

This implication is independent of the earlier specific signed-index=-12 witness, which now serves as a concrete independent calibration. **Crucial negative control:** if D=0, only the *free* anomaly polynomial/index vanishes. Torsion global anomalies, eta-invariant holonomy, global CS levels and path-integral zero-mode issues do not follow and remain open.

The local source cochain `I6=(FL-FR)X4` is a restriction of this stronger invariant-polynomial factorisation to a selected central U1 basis. The new calculation identifies the *actual global line-character candidate*, without claiming a physical normalized differential cocycle. The original first-Tits action #1106 remains the representation owner; physical parity #1241 remains the anomaly source owner.

**New terminal max-cut:** construct the Dai-Freed/Witten-Yonekura determinant-line functional and quantised spin CS level on the selected H quotient, and a global patched/defect-aware WZ functional compatible with the Chi33 line class. Do not waste another cut checking only torus sample parity or a non-source 2+1D CS level. No Agda kernel or full quantum anomaly cancellation asserted.


## 27 October torque / fifth-dimension / 9999! cross-owner acceptance note

Canonical cross-PR result: `Docs/physics/KKTorque9999Chi33SameActionParityPareto20261027.md` and `scripts/check_kk_torque_pickover9999_chi33_fifth_parity.py`, plus source-written `KKTorquePickover9999Chi33FifthConsumerExact.agda`.

The real original owners are merged torque/EM #1164, KK fibre shift #1239, Hopf U1 #1235, **Pickover 9999! #1260** (sibling, not necessarily present as an Agda import in this branch), source E6 #1106, physical KK #1241. The sample Pickover power `k↦4950k mod9999` **annihilates the order-three torsion subgroup**, so cannot faithfully read diagonal quotient deck information under the selected μ3→μ9999 comparison. Its odd-order finite charge-two invertibility also cannot promote a globally single-valued half-phase on U1. In the actual parity-even E6 boundary group Chi33 has primitive Chern winding ±1 at fixed nonliftable Z3 deck; torsion samples and WZ functional remain distinct.

The conventional S1/Z2 orbifold projects **metric g_{mu5}** to odd modes (no geometric graviphoton zero mode), but can retain **independent B_mu** even and **E6 EW** photon; retaining both latter without a mixing/Higgs consumer creates **two** massless U1s. Spatial torque/right-hand orientation from #1164 has no authority to identify either with a fifth coordinate. None of these limited checks constructs APS eta or globally patched WZ; earlier original-source ownership and explicit quantum-wall criteria remain intact.

# Physical KK/E6 global breaking chain: source 27 to SM to color/electromagnetism (2026-10-27)

## Explicit originals and claim-status firewall

**Actual source/PR ownership:** original 27 first-Tits/trinification representation, action and two-VEV source in Agda #1106; chosen S1/Z2 parity, Chi33/E32 and extra E21 candidate, K global character, anomaly/eta/CS/WZ and LARES-2 observable in physical Agda #1241. This tranche derives the *global finite-cover kernels and charge lattices of their original same action*, not a new E6 representation or newly discovered Standard Model. Torque/EM orientation #1164, Pickover #1260, hyperfabric/Monster and Lean original-Q witnesses are **not** substituted for an actual gauge action.

**Original independent literature:** R. Slansky, *Group theory for unified model building*, Phys. Rep. 79 (1981), DOI 10.1016/0370-1573(81)90092-2; D. Tong, *Line Operators in the Standard Model*, JHEP 07 (2017) 104 [arXiv:1705.01853](https://arxiv.org/abs/1705.01853); J. Davighi, B. Gripaios & N. Lohitsiri, *Global anomalies in the Standard Model(s) and beyond*, JHEP 07 (2020) 232, DOI 10.1007/JHEP07(2020)232; H.-L. Li & L.-X. Xu, *Understanding the SM gauge group from SMEFT*, JHEP 07 (2024) 199, DOI 10.1007/JHEP07(2024)199. These supply the mathematical global-form/charge-bordism methods; they did not originally derive this repo's selected Higgs stabilizers. A different 2026 E6->G2×SU3A proposal (EPJC DOI 10.1140/epjc/s10052-026-16104-1) has its **own** Higgs chain and should not be counted as independent validation of ours. Orbifold anomaly, full spin-QFT and exact physical source obligations retain their original authors and owners.

## Actual source carrier and global groups

The faithful boundary gauge group after the orbifold parity (and before Higgs VEVs) is
[
H=[SU(3)_c\times U(2)_L\times U(2)_R]/\mathbb Z_{3,diag},
]
with `U(2)` embedded into `SU(3)` by `U -> diag(U,det(U)^(-1))`. The original first-Tits 27 consists of
[
A=(3_c,\bar3_L,1),\quad B=(\bar3_c,1,3_R),\quad C=(1,3_L,\bar3_R).
]
Its `Chi33=C[3,3]` (one-based row/column) has a **globally defined** H character `chi33(h)=det(U_R)/det(U_L)`. The existing #1241 topology proves `pi1(H)=Z^2` and that Chi33 has primitive character. The actual Higgs-reduced kernel `K=ker chi33` is connected with `pi1(K)=Z`, **still carrying all three diagonal-Z3 cover-deck sectors**. None of these topological statements constructs a stable scalar source or an all-H anomaly-free quantum theory.

There is a source-exact finite covering presentation:
[
(g,A_L,A_R,z)\mapsto
[g,\;\mathrm{diag}(zA_L,z^{-2}),\;
       \mathrm{diag}(zA_R,z^{-2})],
\qquad g\in SU(3)_c,\; A_L,A_R\in SU(2),\;z\in U(1).
]
Its kernel is the **six** powers of `gamma=(omega3 I3,-I2,-I2,-omega3)`. Consequently
[
\boxed{K=[SU(3)_c\times SU(2)_L\times SU(2)_R\times U(1)_z]/\mathbb Z_6.}
]
The finite `Z6` belongs to a covering-group center and does **not** contradict torsion-free `pi1(K)=Z`. If `t_c\in Z3` is colour triality, `s_L,s_R\in Z2` the weak-center parities and `q_z\in Z` the U1 charge, the selected quotient permits a representation exactly when
[
\boxed{q_z\equiv 2t_c+3(s_L+s_R)\pmod6.}
]
This is a **necessary AND sufficient center-descent rule** for candidate representations of that cover, not quantum anomaly cancellation. A lone singlet of U1 charge one fails the quotient and must not be invented as an automatic compensator.

### All eight source K multiplets (27 weight states)

| Block | SU3c | SU2L | SU2R | q_z | Multiplicity |
|---|---|---|---|---:|---:|
| A | 3 | 2bar | 1 | -1 | 6 |
| A | 3 | 1 | 1 | +2 | 3 |
| B | 3bar | 1 | 2 | +1 | 6 |
| B | 3bar | 1 | 1 | -2 | 3 |
| C | 1 | 2 | 2bar | 0 | 4 |
| C | 1 | 2 | 1 | +3 | 2 |
| C | 1 | 1 | 2bar | -3 | 2 |
| C | 1 | 1 | 1 | 0 | 1 |

**Exact test** `scripts/check_kk_e6_k_global_z6_selection.py`: all 27 weights, eight block multiplicities, six-element center kernel, zero/charged Higgs status. Chi33 is a K singlet. The original `E32=C[3,2]` is an SU2R doublet with `q_z=-3`, and `E21=C[2,1]` a bidoublet with `q_z=0`. Therefore **K is only the first Higgs-phase stabilizer**, not the original desired electroweak photon subgroup.

## The second selected VEV E32 recovers the global Standard Model quotient

For a *nonzero E32 VEV in the selected second R-doublet basis direction*, its invariance requires
[
A_R=\operatorname{diag}(z^3,z^{-3}).
]
Consequently `SU3R` fundamental weights become `(+4,-2,-2)` and `SU3L` remain `(+1,+1,-2)`. The SAME cover kernel gamma survives and the full stabilizer of both Chi33 and E32 is
[
\boxed{S=[SU(3)_c\times SU(2)_L\times U(1)_z]/\mathbb Z_6}.
]
In this selected basis `6Y=-q_z`. The exact representation-descending charge rule survives the `Z6` quotient. This is *the conventional global group form* of the Standard Model, not proof that all Standard Model dynamics has been generated.

**Original parity-split 27:** six left-handed SM multiplets (16 Weyl weight states) plus five right-handed exotic/vectorlike multiplets (11 states):

| Chirality | (SU3c, SU2L) | 6Y | Dimension |
|---|---|---:|---:|
| LH | (3,2) | +1 | 6 |
| LH | (3bar,1) | -4 | 3 |
| LH | (3bar,1) | +2 | 3 |
| LH | (1,2) | -3 | 2 |
| LH | (1,1) | +6 | 1 |
| LH | (1,1) | 0 | 1 |
| RH | (3,1) | -2 | 3 |
| RH | (3bar,1) | +2 | 3 |
| RH | (1,2) | +3 | 2 |
| RH | (1,2) | -3 | 2 |
| RH | (1,1) | 0 | 1 |

The LH 16 is a source-selected one-generation SM + right-handed-neutrino conjugate **representation**. The RH 11 is vectorlike/conjugate-pairable under S, but no actual exotic mass/Yukawa operator or localization-decoupling theorem has been generated by this group calculation. Original `E21=C[2,1]` is a weak doublet of `6Y=+3`, hence a candidate electroweak Higgs **if the source action actually admits its VEV**. The existing original E6 scalar potential does not automatically produce that E21 VEV; see the previous #1241 Higgs negative control.

**Perturbative anomaly acceptance** `scripts/check_kk_e6_post_e32_sm_global_z6.py` executes the EXISTING physical #1241 27/parity source, compares all 27 original chirality indices, enumerates the exact Z6 kernel, and checks that within each listed 16 LH and 11 RH set, separately:
- mixed gravitational-U1 and cubic U1 sums vanish;
- SU3^3, SU3^2U1 and SU2^2U1 anomaly coefficients vanish;
- ordinary SU2 fundamental-doublet count is even.
The original **full H** UV anomaly is still nonzero and not cured by merely studying its SM subgroup. Davighi–Gripaios–Lohitsiri's **published** 2020 spin-bordism results on the true SM global group are the correct donor for IR global-anomaly classification, but no claim is made here that their group calculation constructs the full orbifold's eta determinant and relative anomaly cancellation.

## Electroweak E21 yields a global colour/electromagnetism U(3) quotient

If the source ALSO supports a neutral, nonzero `E21=C[2,1]` VEV, its adapted weak-doublet stabilizer requires `A_L=diag(z^{-3},z^{3})`. This makes the original L/R fundamental U1_z exponents respectively `(-2,+4,-2)` and `(+4,-2,-2)`. The selected three Higgs coordinates are all neutral.

All 27 surviving electric U1_z exponents are EVEN, making `w=z²` the faithful circle parameter. The color/U1 cover's original sixfold kernel contains `z=-1` and reduces to the cyclic order-three kernel generated by `(omega3 I3,w=omega3²)`, so
[
\boxed{G_{\mathrm{colour+EM}}
=[SU(3)_c\times U(1)_w]/\mathbb Z_3\simeq U(3).}
]
The integer electric charge `e=3Q_em=-q_z^{residual}/2` satisfies
[
\boxed{e\equiv -t_c \pmod3.}
]
For colourless states, electric charge is integer; triplets and antitriplets have the familiar fractional thirds. This is a group-and-charge-lattice result, **conditional on all three physical VEVs, absence/removal of the unrelated bulk Maxwell U1_B, and the standard orbifold removal of the metric graviphoton zero mode**. It does not predict the physical electric coupling, gauge kinetic mixing, photon spectrum beyond Cartan, W/Z masses or an observed photon from a fully renormalized 5D action.

**Exact regression** `scripts/check_kk_e6_post_e21_u3_photon.py` runs the prior SM Z6 owner, preserves all 27 source state labels/chiralities, tests the sixfold kernel/Z2-to-Z3 quotient, unit 3Q quantization and 16+11 consistency.

## Phase/Pareto/Ibrahim decision: what was paid and where the next wall actually is

**Phase 2 / 3 math now paid conditionally**: actual `H -> K -> S -> Gcolour+EM` global group stabilizer *chain*, source-admissible charge lattices, original 27 parity decomposition, SM-subgroup perturbative anomalies, primitive Chi33 line and nonliftable deck preservation. These are exact finite/covering-group calculations using original mathematical results and the selected VEV assumptions. They strengthen the source-wide motivation for the chiral orbifold branch B but do not construct an E6/SM quantum theory.

**First dominant physical wall remains original full-H 5D global quantum consistency**: a normalized η/Pfaffian determinant + quantized spin-CS5 and a WZ/defect completion valid across the actual unrestricted Chi33 field configurations. The Higgs-restricted K or S anomaly-freedom does not retrospectively cancel an anomalous UV H action. Original-source methods: Dai–Freed determinant-line and Witten–Yonekura eta inflow; global WZW/Goldstone construction by Yonekura (2021). Group-level source selection is not these spectral calculations.

**Second independent blocking wall**: the ORIGINAL same-action scalar potential with bulk/Robin terms must actually support E32, Chi33, **and E21** VEVs jointly, with a nonconstant interval solution and a positive full even/odd physical spectrum. No synthetic zero-mode Hessian or finite group stabilizer pays that. Need full field content, 27 chiral fermions, Yukawas and anomaly-consistent odd tower to keep just the correct four-dimensional spectrum.

**Then**: renormalized same-action radius/VEV/holonomy one-loop vacuum + conserved stress from Casimir owner #1165; a five-dimensional Earth-compatible interior/exterior matching including matter frame; orbit-level physical LARES-2 signal using the published observed tracking combinations and nuisance/geopotential covariance. Existing #1241 LARES observables are conditional geometry, not an observed KK effect or meaningful bound without such sources.

**Verification scope**: the locally executed stand-alone source equivalents test the three finite global-group results; the source-written GitHub files should be executed from their EXACT committed bytes, checked for Agda/Lean transfer and registered in a build before declaring kernel proof. None of this work introduces or validates Monster 3B/Ibrahim representation identifications, 9999! real sine sign, antigravity, fifth-dimensional torque-as-geometry or novel observed physics. Preserve original mathematical authors/dates, existing source PR ownership and status of each inference.

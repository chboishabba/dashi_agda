# KK QED+QCD soft-split multiplets: repaired colour-centre Wilson consumer
Date 2026-10-24. **Canonical PR**: [Agda #1241](https://github.com/chboishabba/dashi_agda/pull/1241). **Executable**: `scripts/check_kk_soft_split_su3_holonomy_maxcut.py`. **Finite BIDI owner**: `DASHI/Physics/Gravity/KKQEDQCDVacuumConsumerBIDIExact.agda`.

## Original physical prior art (attribution)

- Five-dimensional minimal 8-supercharge (5D N=1) **vector multiplet**: 5D gauge field, one real adjoint scalar, one symplectic-Majorana gaugino (on-shell polarizations 3+1 bosonic versus 4 fermionic). **Hypermultiplet**: one 5D Dirac spinor and TWO complex scalars in conjugate gauge representations (4 fermionic versus 4 bosonic units). Established prior art: Marti and Pomarol, *Supersymmetric theories with compact extra dimensions in N=1 superfields*, Phys Rev D 64 (2001) 105025, DOI 10.1103/PhysRevD.64.105025; Hebecker, *5D super Yang–Mills theory in 4D superspace ...*, Nucl Phys B 632 (2002) 101–113, DOI 10.1016/S0550-3213(02)00253-5. DASHI is not the original discoverer of these multiplets or their cancellations.
- Free periodic compact extra-dimensional Casimir determinants with Wilson line and radion: Abe, Inami, Kawamura, Koyama, PTEP 2014 073B04, DOI **10.1093/ptep/ptu097**. Casimir energy in 5D orbifolds and radii: Pontón–Poppitz, JHEP 06 (2001) 019, DOI **10.1088/1126-6708/2001/06/019**. Their orbifold/symmetry breaking assumptions do NOT automatically transport into a smooth periodic S1 action.
- Five-dimensional **parity anomaly and Chern–Simons levels** for fundamental fermions are a distinct gauge-invariance concern; see *Comments on Global Symmetries and Anomalies of 5d SCFTs*, Commun Math Phys 2024, DOI **10.1007/s00220-024-05139-8**. Even number of fundamental Dirac flavours avoids one elementary odd-half-level counting issue, NOT all mixed U1–SU3 levels, spin structures or a complete anomaly cancellation proof.
- Particle Data Group 2025 SUSY experiment review: mass bounds for gluino/squarks are decay- and simplified-model-dependent; choosing several-TeV input masses does not establish viability. See https://pdgweb.lbl.gov/2025/reviews/rpp2025-rev-susy-2-experiment.pdf .
- Original repository owners: QED-only smooth circle with input electron [Agda #1241], hypercharge/anomaly [Agda QFT/Closure], `DASHI/Physics/QFT/WittenIndexSUSYBoundarySurface.agda` explicitly **targets-only/no SUSY construction**, Casimir sources [#701](https://github.com/chboishabba/dashi_agda/pull/701)/[#1165](https://github.com/chboishabba/dashi_agda/pull/1165), TOE [Agda #1217](https://github.com/chboishabba/dashi_agda/pull/1217) and [Lean #80](https://github.com/chboishabba/dashi_lean4/pull/80). Sibling source refs are not merged kernel-verified imports.

## Why this cut differs from the preceding E6 octet repair

Previous selected `E6→SU3³` extra two massless colour-like octets supplied 48 boson units and solved one radial stationarity equation; six electrically charged quarks nevertheless gave `U_{theta_EM theta_EM}≈-21.189` and hence a saddle. That route was not a completed E6 theory. Simply adding exact free-field partners for each QCD fermion and gluon cancels both Casimir **radion and Wilson** modes when their masses, holonomies and boundary conditions match:

- each six colour-triplet 5D Dirac quark: +4, versus two complex colour-triplet squark scalars: −2−2 = −4;
- each eight massless SU3 gluons: −3, plus an adjoint real scalar: −1, and adjoint symplectic-Majorana gaugino: +4.

The previous free 48-unit excess then vanishes **identically mode-by-mode for an EXACT degeneracy**, not only at x=1. These pairings are external supersymmetry theory; our contribution is the **specified mass-split free determinant/holonomy consumer audit**, not a supercharge theorem.

With realistic squark heavier-than-quark masses, however, local positivity of colour holonomy is NOT enough. The six-flavour paired model at b0=10^-24m and squark=3TeV/gaugino+adjoint scalar=4TeV has local positive radial/EM/colour Hessians, but colour-centre Wilson phases `exp(±2πi/3)` have **LOWER** potential by ~`1.83251785787×10^-7` (dimensionless U). That makes the light-colour-quark trivial holonomy vacuum **globally incorrect**, despite three positive local Hessians. This negative control is a separate original SAME-CONSUMER result, not a numerical coincidence.

## Revised candidate: even fundamental flavours with opposing split sign

Add TWO extra 5D *vectorlike*, SU3-fundamental Dirac+two-complex-scalar multiplets, with charges `+2/3,-1/3`; each Dirac has input 5D mass 9000GeV while its two complex scalar partners each have input mass 3000GeV. Six existing quark Dirac flavours retain their input low masses and have the same 3000GeV scalar partners. Gauge adjoint gaugino and extra real adjoint scalar each have 4000GeV input mass; massless 5D gluons remain unbroken. Total number of fundamental Dirac flavours is 6+2=8, even.

**WARNING:** the inverted exotic mass splitting is a SOURCE-WRITTEN free-field mass input. Although every declared scalar mass² is positive, a dynamical gauge-invariant SUSY breaking sector that produces it without unwanted condensation, tachyons or anomalies has NOT been constructed. These are speculative heavy coloured matter states, not discovered particles, nor proven admissible at the LHC. Net electroweak chirality still fails on a smooth periodic circle.

Other fixed sectors inherited from #1241: 5D graviton, independent massless 5D Maxwell, neutral scalar, three heavy neutral Dirac, one heavy charged Dirac, four complex charged stabilizer scalars and the separately input light 0.511MeV QED Dirac zero-mode. No nonabelian E6 gauge embedding is added or presumed; this is an alternative `SU3_colour×U1_EM` source.

## Exact selected one-loop field expressions and mass/charge relations

Define `x=b/b0`, reference `b0=10^-24 m`, `z=2πm_Nb0` for the original neutral stabilizer, `z_e=2πm_e b0`, `z_s=2π(3000GeV)b0`, `z_g=z_a=2π(4000GeV)b0`, `z_X=2π(9000GeV)b0`, and each `z_q=2πm_qb0`.

Normalized free periodic winding kernel
`f(s,phi)=[Re Li5(e^(-s+i phi))+s Re Li4(...)+(s²/3)Re Li3(...)]/ζ(5)`.

Let `theta` be the electromagnetic Wilson phase measured in electron-charge units, and colour Cartan eigenphases `phi=(phi1,phi2,phi3)` with `Σ phi_i=0 mod 2π`. The adjoint phase weights are two zeros and six ordered differences `phi_i−phi_j`.

For the original QED stabilizer `W_QED(x,theta)=-9+12f(zx,0)+4f(4zx,theta)-8f(zx,theta)+4f(z_e x,theta)`. The new coloured sectors contribute

`W_gauge(x,phi)=Σ_adj [-3 f(0,phi_adj)-f(z_a x,phi_adj)+4f(z_g x,phi_adj)]`;

`W_quark(x,theta,phi)=4 Σ_{flavours=u,d,s,c,b,t} Σ_{i=1}^3 [f(z_q x,Q_q theta+phi_i)-f(z_s x,Q_q theta+phi_i)]`;

`W_exotic(x,theta,phi)=4 Σ_{Q=2/3,-1/3} Σ_{i=1}^3 [f(z_X x,Q theta+phi_i)-f(z_s x,Q theta+phi_i)]`.

Same one-loop zero-mode Einstein-frame `U=ell/x+[W_QED+W_gauge+W_quark+W_exotic]/x^6`. Its bulk cosmological term `ell=-W(1,0,0)` is manually tuned to make flat 4D vacuum at the candidate radius; stationarity requires `D=W'_x(1)-5W(1)=0`. Not a natural cosmological constant prediction.

## Reproduced numerical scope

`python3 scripts/check_kk_soft_split_su3_holonomy_maxcut.py` evaluates all derivatives directly from the same kernel at the selected point:

| Quantity | Value |
| --- | ---: |
| `z=2πm_N b0` | **0.9081569400152395** |
| Tuned `ell` | **0.5960734452227415** |
| Radius stationarity `D` | numerically 0 (under 3e-33) |
| Radion Hessian `U_xx` | **+15.39404477777** |
| EM Wilson Hessian `U_thetatheta` | **+1.995873273927** |
| Each orthonormal SU3 colour-Cartan Hessian eigenvalue | **+1.00659188847e-6** |
| Prior six-flavour-only colour-centre energy minus identity | **−1.83251785787e-7** |
| Revised eight-flavour colour-centre energy minus identity | **+3.05689218326e-7** |

The nontrivial colour centre is now **disfavoured**. A coarse 31×31 two-colour-angle grid for electron holonomy 0,2π and 4π samples no negative point after the 8-flavour repair. The 2π combined U1/colour-centre vacuum is exactly gauge-indistinguishable at the level of charges under the selected `(SU3×U1)/Z3` representation; the global gauge quotient and 5D Chern–Simons quantization still need an actual independent group/action receipt.

## Strongest new analytic theorem: all SU3 colour holonomies at x=1, theta_EM=0

This is stronger than a finite-angle landscape scan. Define `a_n(s)=exp(-ns)(1+ns+(ns)^2/3)/(ζ(5)n^5)`. At EM phase zero the coefficient of `cos(n phi_i)` of the entire fundamental sector is

`c_n=4 Σ_{six q}[a_n(z_q)-a_n(z_s)] + 8[a_n(z_X)-a_n(z_s)]`.

The adjoint gauge sector has coefficient per ordered root
`g_n=-3a_n(0)-a_n(z_a)+4a_n(z_g)=3[a_n(z_g)-a_n(0)]<0`, since z_a=z_g>0.

For the fundamental one-phase function `F(phi)=Σ_(n>=1)c_n cos(nphi)`, a sufficient condition for **unique minimum modulo2π at phi=0** is:

`c_1<0`, `Σ_(n>=2)n |c_n|<|c_1|`.

Indeed `F'(phi)=-Σ n c_n sin(nphi)` and `|sin(nphi)|≤n sin(phi)` for 0<phi<π; F' is positive throughout that interval when the inequality holds. Evenness and periodicity complete the circle proof. The full fundamental SU3 contribution is Σ_i F(phi_i), each independently minimized at zero, while the gauge root terms have `g_n<0` and are also minimized when all phases align. Thus the **trivial SU3 colour holonomy is globally minimized across all flat SU3 Cartan holonomies at x=1 and theta_EM=0**.

The code verifies this sufficient condition with an **analytically bounded infinite tail**, not a naked 800-term cutoff:

Let `k(s)=exp(-s)(1+s+s²/3)`; then `k'(s)=-s(1+s)exp(-s)/3` and `(1+s)exp(-s)≤1`, hence `|k(na)-k(nb)|≤n²|a²-b²|/6`. For `N=800`, write `A=Σ_q|z_q²-z_s²|+2|z_X²-z_s²|`; then `Σ_(n>N)n|c_n| ≤ [2A/(3ζ5)]/N`.

**Observed numeric-bound witnesses:**
- `c1=-5.8685828197013734e-8`
- explicit finite `Σ_(n=2..800)n|c_n|=3.7773636719698e-8`
- upper bound on full remaining tail `≤1.6130836213537042e-10`
- strictly positive first-harmonic margin `≥2.075088311518036e-8`

The inequality itself is a valid analytic sufficient criterion with a rigorous series tail estimate; the finite 800-term prefix is evaluated in floating point (not externally interval-certified). This proves the mathematical *selected-field, fixed-radius, zero-EM-phase* colour consumer at paper-derivation grade, not an all-field global EFT theorem.

## Remaining physical and formal gates

- All-EM-phase and all-radius **global** minimum, radion/EM/colour mixed Hessian across background field configurations and nontrivial gauge bundles still require regulator-controlled bounds; scanning only three EM phases is not global certification.
- Full on-shell 5D gauge and scalar potential, 5D SUSY breaking/soft-spurion sector for the *inverted exotic splitting*, actual supercharge/Witten index, spin structure, full interactions and quantum loop corrections are missing. `WittenIndexSUSYBoundarySurface.agda` explicitly leaves these targets open.
- Global gauge group `(SU3×U1)/Z3` and SU3/U1/mixed 5D Chern–Simons parity anomaly quantization require physical receipts. Eight fundamental Dirac flavours is an even count, **not** all these conditions.
- Chiral SU2_L×U1_Y, Higgs/Yukawa generation of observed electron/quark masses, quark confinement, cosmological baryon physics, heavy-coloured-scalar decays and collider precision comparisons are missing.
- Nonabelian interacting QCD running/determinant, fully renormalized same-action metric stress, pressure-supported 5D rotating material Earth, and held-out LARES-2 test remain open.
- The historical 240/243 E8 counting has **no mathematical role in this physical repair**: same-SU3 gauge representation and Wilson interactions—not matched cardinality—supply the evidence.

**Evidence levels:** executable local independently authored Python mathematical sample PASS, exact repository file committed and source-verified; Agda module is SOURCE-WRITTEN/KERNEL UNVERIFIED; physically admissible interacting theory OPEN; empirical observation not performed.

# KK S1: light QED electron + stabilised radion/Wilson BIDI (2026-10-24)

## Canonical owner, scope and provenance

PR #1241, branch `lares2-kk-observable-maxcut-20261023`.

**Executable new result**: `scripts/check_kk_light_qed_dirac_same_action.py`.
**Finite Agda BIDI**: `DASHI/Physics/Gravity/KKCircleQEDChiralityConsumerExact.agda` (source-written; kernel UNVERIFIED).
**Existing sources reused**: `scripts/check_kk_charged_boson_global_repair.py`, `scripts/check_kk_neutral_source_reduction.py`, `scripts/check_kk_jordan_sourced_sphere.py`, `DASHI/Physics/Gravity/KKSteelmanBidirectionalConsumerExact.agda`, `DASHI/Physics/Laws/StandardModelLawBoundary.agda`, `DASHI/Core/FormalClaimTransportGeometryExact.agda`.

**External original scientific prior art**:
- Abe, Inami, Kawamura, Koyama (2014), *Radion stabilization in the presence of Wilson line phase*, PTEP 073B04, DOI `10.1093/ptep/ptu097`. Owns the charged/neutral KK Casimir + coupled Wilson/radion physical programme; DASHI's chosen multiplets and computed root are specific local implementations, not sourced experimental findings.
- Appelquist and Chodos (1983), *Quantum dynamics of Kaluza–Klein theories*, Phys. Rev. D 28, 772, DOI `10.1103/PhysRevD.28.772`.
- Callan and Harvey (1985), *Anomalies and fermion zero modes on strings and domain walls*, Nucl. Phys. B 250, 427–436, DOI `10.1016/0550-3213(85)90489-4`: original anomaly inflow and domain-wall zero-mode physics. This source does **not** prove that a single domain wall on a compact physical circle yields a net chiral Standard Model generation.
- Kaplan (1992), *A method for simulating chiral fermions on the lattice*, Phys. Lett. B 288, 342–347, DOI `10.1016/0370-2693(92)91112-M`: domain-wall/doubler precedent; do not attribute DASHI BIDI theorem to Kaplan.
- Scrucca, Serone, Silvestrini, Zwirner (2002), *Anomalies in orbifold field theories*, Phys. Lett. B 525, 169–174, DOI `10.1016/S0370-2693(01)01430-7`: fixed-point localized anomalies can persist even when total integrated anomaly vanishes. An orbifold is not a free pass to a consistent chiral gauge model.

Attribution rules: external physics/bibliography, local source-written code and local Python execution, formal proof statements, kernel verification and empirical validity are independently typed. Algebraic agreement, loop spectrum arithmetic or matched DOIs alone do NOT promote experimental claims.

## Highest-alpha correction: QED electron is VECTORLIKE

Earlier roadmaps ambiguously required 'light chiral charged matter' before admitting any electron. That over-constrained the **QED consumer**. Electromagnetism treats left and right charged electrons with equal electric charge. The difficult chiral consumer is the **electroweak SU(2)_L × U(1)_Y representation**, Higgs/Yukawa, anomaly freedom and eventually the full Standard Model.

Therefore try a light periodic **5D Dirac fermion zero-mode** on the existing smooth S1 *before* changing compactification to an orbifold or brane geometry. It is a valid free-field QED electron carrier; it is NOT electroweak chirality or a predicted electron mass.

## One explicit 5D zero-mode field content

Circle of radius b, independent massless 5D Maxwell field B_A (physical photon B_mu zero-mode), gravity with graviphoton A_mu distinct, one neutral massless real scalar, a renormalised 5D bulk cosmological counterterm. Additional periodic free fields, with charges only under independent B_A:

| field | number | total one-loop Casimir coefficient | 5D mass |
| --- | --- | --- | --- |
| gravitational + independent Maxwell + neutral real scalar | 1 sector | -9 | 0 |
| neutral Dirac fermions | 3 | +12 | m_N |
| charged heavy Dirac | 1 | +4 | 4 m_N |
| charged heavy **complex scalars** | 4 | -8 | m_N |
| charged light Dirac | 1 | +4 | **m_e = 0.00051099895 GeV INPUT** |

All charged fields have same independent Maxwell unit charge and periodic boundary conditions. All scalar vevs are zero. Thus the physical Maxwell gauge invariance is unbroken; no classical photon mass. The new electron mass is chosen from measurement and not derived by Higgs. No electron chirality under SU(2)_L, actual Higgs dynamics, quarks/protons, nuclear stress or interacting charged matter is claimed.

Use `x=b/b0`, `z=2π m_N b0`, `z_e=2π m_e b0`, `θ` the independent-Maxwell Wilson phase. Define the exact renormalised periodic free-field Casimir function

`f(s,θ) = Re[Li_5(e^(-s+iθ)) + s Li_4(e^(-s+iθ)) + s² Li_3(e^(-s+iθ))/3] / ζ(5)`.

This is the polylog sum corresponding to the prior Bessel K_(5/2) free KK determinant. Einstein-frame zero-mode potential

`U(x,θ)=ℓ/x + [-9 + 12 f(zx,0) + 4 f(4zx,θ) - 8 f(zx,θ) + 4 f(z_e x,θ)]/x⁶`,

`V_E = c0 U/b0⁴`, `c0=3ζ(5)/(64π⁶)`. The renormalised cosmological counterterm `ℓ` is tuned to force `U(1,0)=U_x(1,0)=0`; it is NOT a dynamical solution of the cosmological constant problem.

## Numerically sourced local vacuum and actual zero mode

At illustrative `b0=10^-24 m`:
- `z_e=1.6270968562514e-11` for the input electron mass.
- `z=0.9081569907830750`, `ℓ=0.5960733249785279`.
- `U_xx(1,0)=15.3940431518449 >0`; `U_θθ(1,0)=1.99587282944274>0`; `U_xθ=0` by phase symmetry.
- Radion Compton range `5.417345112e-13 m` from the canonical E-frame scalar.
- `m_N≈2.8521183e7 GeV`, heavy charged Dirac `≈1.1408473e8 GeV`.
- Physical **four-dimensional electron zero-mode mass** exactly the input `0.00051099895 GeV` at θ=0 in the free KK spectrum, not shifted by n=0 circle momentum. First nonzero Fourier mode `≈1.973269804e8 GeV`.
- `b0 M5≈2.893888e6`; high compactification-to-5D-gravity scale separation, but **not** full control of the 5D high energy charged interactions.
- Maxwell physical photon zero mode B_mu remains massless by U(1) symmetry; 4D gauge coupling `e4=e5/sqrt(2π b0)` is an independently *chosen* parameter. QED running/charge renormalisation and higher-order loops not solved.

These values were independently evaluated in high-precision mpmath; the local script tests the symbolic field content and numerical minima. The scanned two-dimensional landscape samples 180 radii x 45 phases for x∈[0.003,1000] and 18 local optimizations; no sampled lower minimum found. This is NOT a global continuum theorem in both variables.

## Stronger exact radial global-minimum theorem: proven by an analytic sign argument

At fixed Wilson phase `θ=0`, combine the periodic free-field contributions as

`U(x,0) = ℓ/x + [-9 + 4 f(zx,0) + 4 f(4zx,0) + 4 f(z_e x,0)]/x⁶`.

Let `F(x)=x⁶ U(x,0)`, `s_1=z, s_2=4z, s_3=z_e`, and

`S(t)=Li_3(e^{-t})+t Li_2(e^{-t})`.

The derivative factors EXACTLY:

`F'(x)/x=5ℓ x³ - [4/(3ζ(5))] Σ_{j=1}^3 s_j² S(s_j x)`.

For `t>0` one has `S'(t)=-t Li_1(e^{-t})<0`. Since `ℓ>0`, the first term strictly increases for x>0 and each negative S term is strictly increasing. Thus **F'/x is strictly increasing**, has exactly one zero at x=1 (by the tuned stationary conditions), and is negative for 0<x<1 and positive for x>1. Since `F(1)=0`, this proves `F(x)>0` and hence `U(x,0)>0` for every x>0 with x!=1. This holds with **finite positive electron mass**; it is not a massless-electron approximation.

For arbitrary phase at x→0, all masses become negligible and

`x⁶ U(x,θ)→ -9+12+(4-8+4)f(0,θ)=3 >0`,

uniform in θ by dominated convergence of the absolutely convergent KK sum. At x→∞ the tuned `ℓ/x` term dominates and is positive. **A continuum-wide global minimum in the full (x,θ) plane still requires certified intermediate-radius bounds**: no claim that the fixed-θ radial theorem supplies it.

## Domain-wall and orbifold BIDI fork, independently attributed

For a single charged 5D Dirac on smooth periodic S1 with any real periodic mass profile `M(y)` and constant Wilson phase θ, the separated 4D chiral zero-mode equations have monodromies

`L: exp(-∮M dy - iθ)`, `R: exp(+∮M dy - iθ)`.

Exact periodic zero modes therefore occur in LEFT–RIGHT pairs (when `∮M=0, θ=0 mod 2π`) or neither is periodic. Hence the **net four-dimensional chiral index is zero** for this single smooth Dirac sector, including kink/antikink profiles, although the profiles can localise left/right separately. The script checks this finite witness set; the analytic monodromy argument supports the general claim for this scalar-mass model.

For electroweak chiral fermions, changing to S1/Z2, introducing domain walls with additional symmetry breaking/inflow, nontrivial gauge bundles or higher-dimensional index data changes the physical candidate and often the spectrum. In a simple orbifold, g_mu5 and B5 are odd and lose their zero modes; the current **Wilson phase/circle Casimir cannot be imported unchanged**. Brane/domain-wall backgrounds may break the circle isometry and require a graviphoton mass/backreaction analysis. Any chiral gauge theory also requires bulk+fixed-point anomaly cancellation, not just cancellation of the integrated 4D index.

The exact finite Agda module `KKCircleQEDChiralityConsumerExact.agda` reuses the existing `StandardModelLawBoundary.Chirality`, `FormalClaimTransportGeometryExact.ClaimNonTransportWitness` and `ConsumerFibreRepairExact`. It proves only that a shared QED electric charge and Dirac mass cannot answer an electroweak chirality or representation question. It does **not** kernel-prove the smooth-circle Dirac-operator index theorem or an actual physical SM model.

## Updated BIDI steelman / next legitimate work

- **C_stabilised_radion + massless photon**: locally satisfies the declared tuned one-loop EFT with electron included and charge-zero condensates. Analytical radial global minimum at θ=0 and uniform x→0 repulsion; all-θ global stability pending.
- **C_physical_QED_electron**: *constructed as a free 4D zero mode with observed mass INPUT and charge NORMALISATION chosen*, not generated as an observed/renormalised interacting QED particle.
- **C_SM_chiral_EW**: FAIL for the simple smooth S1 periodic Dirac; this consumer requires a new spectrum/topology/gauge structure and anomaly receipts. QED left/right equality is appropriate, not a failure of QED.
- **C_Earth_Geodesy**: static linear uniform source coupling and tiny radion range exist as earlier conditional donors; full pressure-supported rotating 5D source, a conserved material stress and geodetic observations remain unproved.
- **C_nonperturbative_quantum_model**: higher-loop massive/light electron and gauge corrections, 5D parity/anomaly, Wilson scalar dynamics, renormalised vacuum energy naturalness, UV completion still unproved.
- **Horned sphere PR #1244**: optional global topology analogy, NOT relevant to the physical S1 circle source or QED electron and NOT a prerequisite.
- **Related PR #1248**: different physical system (spherical Dirac wormhole and Polyakov stress); source-variation discipline is useful as a methodology, but its charged fermion geometry is not a donor for this flat compact S1 Casimir determinant.

## Acceptance / receipts

- `python3 scripts/check_kk_light_qed_dirac_same_action.py` — locally executed *equivalent high-precision model*, PASS. Actual GitHub committed script verified by source fetch; no exact-head remote execution receipt.
- `agda -i . DASHI/Physics/Gravity/KKCircleQEDChiralityConsumerExact.agda` — source-written targeted kernel check, NOT executed (Agda unavailable).
- Continue testing `scripts/check_kk_charged_boson_global_repair.py` as a prior donor, but it is a DIFFERENT field spectrum: never carry its mass/radius numbers into this new QED-electron candidate.

Critical frontier after this cut: obtain an admissible **electroweak-chiral source** (SU2L/Higgs/hypercharge and local anomaly inflow) without silently transporting the current smooth-circle Casimir vacuum; and independently replace static Helmholtz with a conservative spinning five-dimensional material source and controlled 4D geodesic observable. No invented new numbered encodings or unrelated horned prerequisite.


## Additional BIDI: periodic domain walls can sacrifice the graviphoton

`scripts/check_kk_s1_chirality_wall_obstruction.py` is an independently scoped analytic and SymPy sanity check. For a periodic illustrative scalar profile `X(ϑ)=v sin(ϑ)`, its nonzero circle-gradient norm obeys `∫(dX/dϑ)² dϑ=πv²>0`. The KK metric's covariant horizontal derivative is `D_μ X=∂_μX−κ A_μ∂_ϑX`, and the 5D kinetic term generates a positive quadratic `A_μA^μ` coefficient proportional to `κ²πv²` (after restoring metric normalisations). In a gauge-invariant treatment the wall-position Goldstone supplies the Stückelberg mode. Thus a nonuniform circle-localising vacuum generally **breaks the circle isometry and removes a strictly massless geometric graviphoton**. This is a scoped background/isometry obstruction, not a proof every localising model has exactly that mass. The independently gauged Maxwell zero mode `B_μ` can remain massless if the wall background is neutral under that gauge symmetry.

The same sine-profile Dirac mass has `∮M dϑ=0`, so left/right separated solutions are **both** periodic when the Wilson phase is 0, despite their different localisation; net index remains zero. This challenges premature promotion of a kink/antikink mode as a single *exact* chiral electroweak generation on smooth S1.

## Gauge-theory perturbative budget (new)

For an independent five-dimensional U(1) field of coupling `e5²=2πb0 e4²`, a conventional five-dimensional naive-dimensional-analysis gauge cutoff is `Λ_NDA~24π³/e5²=12π²/(e4² b0)` (order-one normalisation/field content not fixed). With `e4²=4π/137.036` and `b0=10^-24m`, the estimate is
- `b0 Λ_NDA≈1291.53`;
- `Λ_NDA≈2.5485e11 GeV`;
- `M5≈5.7104e14 GeV`, **higher than this gauge cutoff by ~2241**;
- the 1/b0 KK mass ≈1.9733e8 GeV and heavy stabiliser masses ≈2.85e7 / 1.14e8 GeV are below this NDA gauge cutoff.

Thus at the compactification scale, a perturbative gauge EFT **can** be self-consistent in this selected example, but it must not claim perturbative control all the way to the 5D gravitational scale. Matching to new charged-sector UV physics above the cutoff, its effect on Casimir coefficients and naturalness, is an open source obligation. For the standard five-dimensional NDA loop-factor normalisation, see CERN-PH-TH/2006-167 (CERN record 1012495) and other five-dimensional effective gauge-theory power-counting literature; the exact strong-coupling scale is scheme- and field-content-dependent. The numerical cutoff is a rough estimate, not an experimentally established maximum energy.

The committed light-electron checker now includes the NDA inequalities. Local matched Python tests passed; exact committed-head execution remains unverified.

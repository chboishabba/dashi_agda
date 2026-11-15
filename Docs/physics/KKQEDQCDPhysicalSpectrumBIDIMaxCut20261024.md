# QED × QCD × KK: consumer-specific physical spectrum and hypercharge audit
Date: 2026-10-24. Owner: PR #1241 (branch lares2-kk-observable-maxcut-20261023).

## Source and repository provenance — do not merge authority categories

PRIMARY EXTERNAL ROOTS
- Abe, Inami, Kawamura and Koyama, "Radion stabilization in the presence of a Wilson line phase", *Progress of Theoretical and Experimental Physics* 2014, 073B04. DOI **10.1093/ptep/ptu097**; preprint arXiv:1404.5125. Their original work provides the 5D gravity + U(1) + fermionic one-loop radion/Wilson framework, not our specific chosen spectra or QCD obstruction.
- Rubin and Roth, "Fermions and stability in five-dimensional Kaluza–Klein theory", *Physics Letters B* 127 (1983) 55–60. DOI **10.1016/0370-2693(83)91629-5**. Earlier compact-radius fermionic Casimir prior art.
- Particle Data Group, *Review of Particle Physics* 2025 update, quark summary https://pdg.lbl.gov/2025/tables/rpp2025-sum-quarks.pdf and QCD review https://pdg.lbl.gov/2025/reviews/rpp2024-rev-qcd.pdf . The source itself warns that light quark masses are scheme/scale dependent (u,d,s at 2 GeV; c,b at their masses; top kinematic extraction). DO NOT call low-scale mass inputs high-scale running masses or a 5D ultraviolet prediction.
- Edward Witten, "An SU(2) anomaly", *Physics Letters B* 117 (1982) 324–328, DOI **10.1016/0370-2693(82)90728-6**. Standard global even-doublet check; our check simply verifies the inherited SM table has four SU2 doublets per generation.

EXISTING DASHI ORIGINAL DONOR OWNERS, NOT NEW DISCOVERIES
- DASHI/Physics/Laws/GaugeInteractionLaws.agda: Maxwell/Yang–Mills geometry, action, source-current, and equation contracts.
- DASHI/Physics/Electromagnetism/U1AsSU2AbelianRestrictionExact.agda: Abelian restriction and group embedding; not full nonabelian dynamics.
- DASHI/Physics/Closure/QCDRunningFromCarrierScaleReceipt.agda: independent beta/coupling/LambdaQCD/threshold requirements; canonical physical continuum alpha_s still flagged as unconstructed from the carrier.
- DASHI/Physics/Closure/AnomalyCancellationVerificationReceipt.agda and GravitationalAnomalyCancellationReceipt.agda: inherited standard hypercharge anomalies; canonical result explicitly does not promote full SM.
- DASHI/Physics/Closure/U1YChargeAssignmentTableReceipt.agda; DASHI/Physics/QFT/ChargeNormalisationReceipt.agda: signed sixth hypercharges with convention Y(Q_L)=1/6.
- DASHI/Physics/Closure/HiggsElectroweakBoundary.agda and DASHI/Physics/Laws/StandardModelLawBoundary.agda: coupling, Higgs, representations and chirality obligations.
- DASHI/Physics/Closure/SU2SU3DecouplingLemmaReceipt.agda: conditional SET/level-rank argument; does not generate an independent physical full QCD+EW source.
- DASHI/Physics/Gravity/KKSteelmanBidirectionalConsumerExact.agda and core FormalClaimTransportGeometryExact/ConsumerFibreRepairExact: existing canonical BIDI owners.

NEW EVIDENCE / CONTRIBUTION
- scripts/check_kk_qed_qcd_casimir_budget.py: executed local mpmath source algebra, counterterm-invariant QED->QED+QCD incompatibility and restricted compensator lower bound.
- DASHI/Physics/Gravity/KKQEDQCDVacuumConsumerBIDIExact.agda: source-written, conditional finite non-descent and exact 24/72/48/240 field arithmetic; imports the pre-existing anomaly and QCD receipt owners. No Agda kernel run in this environment.
- DASHI/Physics/Gravity/KKQEDQCDHyperchargeBIDIExact.agda: canonical integer SM charge-table vs Higgs generator bridge and wrong-charge witness; source-written, not Agda kernel-certified.
- scripts/check_kk_hypercharge_anomaly_weld.py: executable Fraction exact arithmetic verifying QED/QCD charges, SU2/SU3 mixed and cubic/gravitational anomalies, Yukawas and even-doublet parity.
- Corrected the string label in *HiggsElectroweakBoundary.agda* on this PR from `Q_EM = T3 + Y/2` to `Q_EM = T3 + Y`, keeping the original sixth-charge owner unchanged. This is a **convention repair**: the alternate formula is valid only if Y is doubled everywhere. The master source was not altered by this PR until merge.

## Concrete restricted QED+QCD obstruction (same selected S1 candidate)

Previous `check_kk_light_qed_dirac_same_action.py` constructed a smooth-periodic S1 candidate with input light QED Dirac mass, massless independent photon, gravitomagnetic U1, and one-loop tuned scalar vacuum at b0=10^-24m, theta_EM=0. That candidate omitted physical SU3 gluons and six colour-triplet light quarks.

For a selected **5D vectorlike QCD donor** with periodic trivial-colour holonomy: eight massless 5D gluons contribute -8*3=-24 free Casimir units (three 5D vector physical polarizations each). Six free 5D Dirac quark flavours each with three colours contribute 6*3*4=+72 units. Thus the massless limit adds +48 to the free-field winding Casimir budget. The fermion-to-gluon factors are the established QCD representations, NOT an inference from a 369 chart.

Take x=b/b0 and (U(x)=ell/x + W(x)/x^6). A tuned flat stationary vacuum requires `U(1)=0` and `U'(1)=0`. Eliminating ell yields the **counterterm-independent** compatibility condition:

`D := W'(1)-5*W(1)=0`.

For PDG illustrative quark mass inputs at the selected b0 (physical inverse radius ~197326980 GeV), the new matter sector contributes

`delta W = -24+12*sum_{q=u,d,s,c,b,t} f(2pi m_q b0) = 47.999999999929958981`;
`delta W' = 12*sum_q (2pi m_q b0)*f'(2pi m_q b0) = -1.4008203834590e-10`;
`delta D = delta W'-5 delta W = -239.99999999978987694`.

The previous tuned source had D~0. Thus **at the same radius/phase and with these same light QCD zero modes, the previously advertised stationary-Minkowski vacuum is not a solution once QCD is included**.

Retuning only the 5D cosmological constant fixes vacuum energy (ell changes approximately +0.596073 to -47.403927) but NOT its first derivative. This is the actual no-go, not the superficial observation that some field counts differ.

### Analytic six-quark mass-independent bound

For the positive periodic free Dirac Casimir kernel `f(z)`, one has

`f'(z)=-z/(3*zeta(5))*[Li_3(exp(-z))+z Li_2(exp(-z))]<=0`;

`1-f(z) <= z² zeta(3)/(6 zeta(5)) + z³ zeta(2)/(9 zeta(5))`.

If every six quark bulk mass is below the conservative 200 GeV at b0=10^-24m, then `z_q<6.37e-6`, so `f(z_q)>=1-1e-10`. Hence `delta W >= 48-72e-10` and

`delta D <= -5 delta W < -239.999999`.

The masses used from the PDG are a numerical illustration; the bound is independent of a precise running mass prescription as long as the stated 200 GeV input bound holds. This is NOT a universal no-go: different compactification radii, fermion boundary conditions, Wilson/gauge backgrounds, chiral/brane matter, scalar physics or strong interaction counterterms would change the theory, so require new same-action calculations.

### Hiding QCD with a colour centre holonomy changes the consumer

An SU3 centre Wilson phase `exp(2pi i/3)` leaves adjoint gluons invariant but shifts fundamental quark KK momentum by `1/(3b0)`, about 65.8 million GeV at this radius. This removes the same massless/light quark zero-mode consumer. An electromagnetic Wilson phase has a similar effect; retaining the observed light electron requires its phase near zero, `|theta| ~< 2pi m_e b0 ~1.63e-11`. Nontrivial Wilson phases may repair a different theory but cannot answer the same light-quark/electron consumer without further ingredients.

### Restricted compensator Pareto bound

Keeping all initial sectors, radius, trivial gauge holonomies and the light quark zero modes fixed, add N free periodic real bosonic Casimir polarization units, with nonnegative masses and **no condensates**. Each unit contributes `5 h(z)` to D, where `h=f-z*f'/5`, `0<h(z)<=1`. Therefore **N>=48** is necessary to offset the ~240-unit deficit; 47 units contribute <235. An illustrative exact compensation with 48 degenerate new light real bosonic modes occurs near 86 GeV each, from the script's one-equation numerical root. This is merely a **mathematical repair** and has no supplied physical origin or established experimental admissibility. It is not a new particle prediction, nor an exhausted search over stabilisers. More exotic bosons/gauge embeddings or source terms would require a separate calculation.

### Perturbative-consumer scope

Illustrative one-loop 4D QCD running from alpha_s(mZ)=0.118, beta0=7 and NO threshold matching gives alpha_s(1/b0) about 0.04044. This indicates asymptotic freedom makes the *leading free-field counting* a reasonable first test, but it does not verify 5D interacting QCD vacuum loops or the actual high-scale 5D coupling. The inherited `QCDRunningFromCarrierScaleReceipt` rightly does not promote carrier-based QCD running.

## A second actual repo mismatch: Higgs generator vs inherited hypercharge

`U1YChargeAssignmentTableReceipt` stores physical Y(Q_L)=1/6 and Y(L_L)=-1/2. With these values the actual electromagnetic generator is

`Q_EM = T3 + Y`,

not `Q_EM=T3+Y/2`. Keeping the earlier Higgs label without doubling Y yielded wrong charges: u_L=7/12 (should 2/3), d_L=-5/12 (should -1/3), e_L=-3/4 (should -1). The PR updates the Higgs owner convention label and adds exact finite Agda/Python regressions. Another internally consistent convention is `Q=T3+Y_doubled/2`, but then the entire hypercharge table and gauge coupling would need to be doubled as well.

The exact-atom tests also show the inherited standard cancellation sums still vanish, and SU2 doublet parity per generation 3-colour quark doublets +1 lepton doublet =4 even (Witten 1982). They do not prove such fields are the 5D KK zero modes. Without actual EWSB and a chiral representation model, an independent KK bulk photon is not automatically the standard electroweak residual photon from SU2×U1Y mixing. The formal SM promotion remains fail-closed.

## Consumer-indexed research frontier, Pareto ordered

1. **C_QED** — one free light vectorlike electron plus massless independent photon: conditional existing one-loop toy PASS; physically renormalised QED and electron mass generation are NOT paid.
2. **C_QED+QCD same stationary vacuum** — FAIL for fixed b0, trivial holonomies, six light periodic 5D Dirac quarks and eight gluons, even after bulk cosmological retuning. Source: new exact stationary compatibility obstruction.
3. **C_light quark plus gluon plus stable radion** — NEED NEW ACTION OR STABILISER; at least 48 free bosonic polarization units in the especially restrictive additive no-condensate class, but that class is not assumed exhaustive.
4. **C_EW_Higgs+anomaly** — canonical charge sums and normalization now internally consistent; net chiral physical zero modes, Q_EM residual embedding, g/g' mixing, SU3 source matching and 5D anomaly inflow OPEN. A periodic 5D Dirac field is vectorlike, so inherited 4D anomaly identities are not a 5D chiral construction.
5. **C_Earth/LARES** — even a locally stable KK vacuum does not supply a sourced rotating material Earth with correct QCD nuclear stress, equivalence principle, radion matching, physical geodesics and experimental orbit residual. Highest-value approach is to determine eligible physical source/spectrum before refining more nodal proxies.
6. **C_horn** — PR #1244 Alexander horned sphere topology is unrelated to this physical smooth-circle QED/QCD vacuum; not a prerequisite.

## Verification and accept

Local independent `python3 /mnt/data/kk_qcd_maxcut/check_kk_qed_qcd_casimir_budget.py` and `python3 /mnt/data/kk_qcd_maxcut/check_kk_hypercharge_anomaly_weld.py` passed. Equivalent scripts committed to GitHub:
- `python3 scripts/check_kk_qed_qcd_casimir_budget.py`
- `python3 scripts/check_kk_hypercharge_anomaly_weld.py`

Agda formal-source files added to branch; no Agda executable available here. Hence **SOURCE-WRITTEN, KERNEL PENDING** for these Agda witnesses; not proven full QCD dynamics, 5D chirality, astrophysical gravity, or empirical measured KK deviations. Do not force QED-only agreement to imply QCD/SM consumer admissibility.

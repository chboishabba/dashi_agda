# 6 November 2026 — #1460 exact max-cut implementation / physical proof integrity receipt

## Governance and cross-worker cut

**Canonical:** [186 original lemma IDs + 186 source/kernel/physical status rows](../roadmaps/Emergent31QuantumYMKKExactLemmaRoadmap20261103.md). **Active phases:** [48 executable deliverables across five phases](../roadmaps/TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md). **Current TODO:** [our-lane max-cut](../roadmaps/TSFVUnificationTODO20261106.md).

**Independent YM parent:** #1444 owns Wilson/Gibbs/compact SU(N) Haar, R443/R445/R320/R333/CMP116, physical-cube fixed-ℓ Dobrushin and the independent Clay endpoint. **Our child:** #1460 owns microscopic TSVF observer response, independently measured spacetime, the original complete observer Hilbert/Stone, actual five-dimensional KK Einstein–matter source and source-identical comparison with whatever physical OS Hilbert the YM worker constructs. Never import child findings upstream into YM as evidence for its gap.

**Actual synchronization:** [PR #1470](https://github.com/chboishabba/dashi_agda/pull/1470) merged YM donor head `572de64743ade4c3fcbb092ea4be1ce70f85a3b1` into child via merge commit `1f71c1d58cc2d231a0fdc42c50b0c9969d35e49b`. The parent can advance concurrently; pin subsequent heads separately. Prior [PR #1469](https://github.com/chboishabba/dashi_agda/pull/1469) retained source separation into `BalabanRGTOERegression`, `TSFVUnifiedRegression` and `TSFVParentChildRegression`.

## New source-native P01/P02/P07 mathematics

### Exact selected local impulse response coefficient (S02, scoped chosen lattice)

Source: `DASHI/Physics/Foundations/TSFVAcousticLocalImpulseThirdDerivativeExact.agda` (`--safe` candidate). Selected model is the three-neighbour-axis scalar lattice with stiffness (Lq_n=\mu^2 q_n+k\sum_{6}(q_n-q_{n+e})). For an initial unit **velocity** kick at the origin, if a sufficiently differentiable solution of ( q''=-Lq) exists, calculus implies ( q'''(0)=-L\delta_0). The Agda module **defines** that algebraic third-derivative coefficient and proves:

- `allSixFirstNeighborResponsesReadCoupling`: each chosen local neighbour channel has (-L\delta_0=k), for every rational (k,\mu^2), axis and orientation.
- `outsideNearestBallHasZeroThirdDerivative`: every site outside the chosen local neighbourhood has zero leading third-derivative coefficient.
- `originalKickedSiteThirdDerivative`: kicked-site coefficient (-\mu^2-6k).
- `firstNeighborImpulseResponseIsMassIndependent`: neighbour third-derivative alone does not identify (\mu^2).

**Not proved in Agda:** existence/uniqueness/differentiability of a C³ retarded solution, actual source-specific recorded measurement, measured spacetime dimension or continuum causal cone. The selected three axes are assumptions of this controlled model. Independent earlier full (N=5) selected-lattice Fraction reference covers all 125 sites, 6 nearest response channels, 3 opposite-direction pairs, 12 transverse pairs and 18 next-shell (t^5)-coefficient nonzeros. It is not an Agda kernel proof.

### Full response vs common Lorentzian cone (P02/P07 BIDI)

Source: `DASHI/Physics/Foundations/TSFVAcousticMassInverseBidiNoGoExact.agda` (`--safe` candidate), importing the *same* chosen acoustic `sourceMeasuredWavePrincipal` from `TSFVSelectedLatticeAcousticKKFlatControlExact`.

For any squared masses \(m_1^2,m_2^2\) the selected principal symbols are equal:
\[
Q_{m_1}=Q_{m_2}=k_x^2+k_y^2+k_z^2-\omega^2
\]
in normalized \(c=1\) coordinates. Nevertheless their FULL model Fourier denominators
\[
D_m(\omega,k)=Q(\omega,k)+m^2
\]
are distinguishable: \(D_m(0,0)=m^2\), and pointwise equality of \(D_{m_1}\) and \(D_{m_2}\) forces \(m_1^2=m_2^2\). `fullSelectedResponseEqualityForcesSameMass` and `differentMassCannotShareEntireResponse` formalize the backwards discriminator. This is a genuine mathematical reason a measured 4D cone alone cannot identify a unique underlying field mass/Hilbert/OS source.

**Not proved:** this formula is the actual original TSVF retarded dynamical denominator or that its mass is empirically selected. It is a source-control BIDI no-go, not the original physical completion.

Both new owners imported and publicly exported by `DASHI.Unified.TSFVUnifiedRegression`; native YM parent regression unchanged by our source proofs.

## Exact independent proof checks

- `scripts/check_tsfv_acoustic_impulse_mass_bidi_20261106.py`: 2,764 exact Fraction cases passed in an independent equivalent local run, including four nonzero couplings, four masses, all six local channels, source origin/far controls, 16 mass pairs and all chosen Fourier arguments. The committed GitHub script has not been run as part of a repo checkout/Actions.
- Live connector readback checked **186/186 unique canonical IDs**, **186/186 status rows**, **48 distinct execution tasks**, **7+12+12+9+8 phase counts**, and **101 distinct referenced original canonical IDs**. New `scripts/check_tsfv_unification_48_phase_cut_20261106.py` is committed but repository CI execution remains PENDING.
- New canonical `parallel_checker` wrapper `scripts/run_tsfv_unification_maxcut_20261106.sh` runs both document guards, original OS and spatial control checks, current acoustic reference, actual Agda `--safe` candidate sources and ordinary typechecking of the separate/native/combined roots. Updated `.github/workflows/tsfv-physical-maxcut-source-audit.yml` calls the canonical `scripts/run_agda29_parallel_check.sh` through the focused wrapper; the checker manages the pinned Agda/stdlib/vendor includes, cache, memory limits and logs. There is no user-facing direct Nix invocation.
- **No Agda/kernel green receipt:** local environment does not provide `agda`; earlier GitHub Actions inspection returned zero child-branch runs. A `--safe` header and a successful finite Python script do NOT establish transitive trust or physical truth. If an exact-head Agda compiler fails, do not record source proofs as kernel accepted.

## Unpaid physical S01–S11 maximum cut

| Leaf | Required real construction | Status |
|---|---|---|
| S01 | Selected original TSVF many-body quantum instrument/pointer/record and time | PHYSICAL OPEN |
| S02 | Physically observed original local retarded response and spatial discrimination | PHYSICAL OPEN; chosen oscillator coefficient only |
| S03 | Independent 4-dimensional causal-volume/continuum from microscopic observer | PHYSICAL OPEN |
| S04 | Original measured Lorentz principal, light cone, positive energy and 3+1 without assumed dimensions | PHYSICAL OPEN |
| S05 | Actual nontrivial 5D smooth Einstein–matter/KK source and stress/radion/global bundle | PHYSICAL OPEN; flat vacuum control only |
| S06 | 5D reduction equal to original **independently measured** observer g4 | PHYSICAL OPEN; chosen same-g4 algebra only |
| S07 | Actual interacting Yang–Mills nontrivial continuum OS H and spectral gap | YM #1444 EXTERNAL |
| S08 | Original noncollapsed complete Hilbert and physical Stone generator | PHYSICAL OPEN; free Fock control only |
| S09 | Onto unitary preserving original/YM OS states/H domains/spectra/observables and justified Wick | PHYSICAL OPEN; conditional graph BIDI only |
| S10 | Full original same-source forward/reverse diagram and uniform compatible physical limits | PHYSICAL OPEN |
| S11 | Exact-head Golden Agda, transitive trust and independent maths/physics validation | KERNEL + PHYSICAL RECEIPTS OPEN; pinned parent merge complete |

**Scientifically honest terminal status:** source-written progress and exact proof plan are substantial. The real original physical construction and complete all-sector unification are *not proved* by these finite and conditional modules. Do not promote either our model controls or the YM worker's finite/physical-cube conditional `q<1` into an unproved full Clay/unification theorem.

# OCT369 P0.30 — original experiments and source-conjugate evidence audit

**Date 2026-11-21.** Corrects the earlier framing that momentum-dependent nonzero response was a new finding.

## Evidence and original attribution
| Source owner | Source evidence | What was already known | Does it identify PtMn3 octupole static susceptibility? |
|---|---|---|---|
| Sprague et al., Nature Communications 2026 DOI 10.1038/s41467-026-76784-x; CoTaSe2PublishedARPESConstraintsExact | Original experiment/publication (k, energy, temperature band splitting) | Momentum-resolved band structure / nodal splitting | NO: different material and different observable |
| Mandujano et al. PRB 110 144420 (2024); CoTaSe2PublishedMaterialProducerExact | Published crystal/basis source | Refined sites, material parameters | NO |
| Existing DASHI CoTaSe2 Wannier3DResponse and NonAbelianTopology | Original repository **conditional computational producer** | Analytic Wannier dH/dk, Berry interband Kubo, gauge-safe projector/Wilson; nonzero momentum response is not novel | NO literal PtMn3 Hamiltonian |
| Existing DASHI MMPThreeIndependentRetardedSourcePorts | Original repository finite-time *numerical* Kubo response | Causal source pulse, differentiation vs unitary evolution | NO |
| Kang et al., Nature 658 (2026) DOI 10.1038/s41586-026-11172-5 | Original PtMn3/MgO/PtMn3 experiment, plus theoretical momentum-projected channels in paper | Room-temperature TMR, current-driven OTT switching and k_parallel-resolved calculated conduction channels | NOT a measured equilibrium static `chi_OO(k)` and NOT a gravity measurement |
| Ōiké, Peters, Shinada PRB 112 134412 (2025); Sato, Hayami npj Quantum Materials 11,32 (2026) DOI 10.1038/s41535-026-00865-9 | Original thermodynamic and gauge-invariant periodic magnetic octupole theory | Full thermodynamic multipole and mixed (k,h) formulas; Sato/Hayami Eq.22 Maxwell relation | Must be computed from a source-validated material input |

**P0.29 correction:** P0.29's nonzero values 0.76387–0.92727 are numerical *toy model regressions*. They are neither new empirical knowledge nor a reproduction of measured PtMn3 octupole susceptibility. Only its cross-producer consistency tests count as a new integration.

## New P0.30 same-owner consumer (59/59 local checks)
The exact tested Python source is `scripts/check_oct369_p030_domain_q_response_identifiability.py`, Git blob SHA `5de25d8131f2f07694f41c4b8e58547dd5ecdae8`. It imports P0.29, so no second H(k) or Kubo engine was invented. Quantitative results are dimensionless and source-conditional:
- Spinful TR maps +magnetic domain H(k,+) to H(-k,-), and the source OP to -OP. Therefore the *order expectation* is odd but the same-channel static susceptibility is even. Max numerical residual ~2e-15. This is an identifiable symmetry negative control, NOT a new effect.
- The finite three-cell DFT exactly maps a periodic real-space spin modulation to q=±1/3 crystal-momentum transfer; a uniform source is diagonal in k. Static susceptibility of the **same** H against unnormalized source amplitudes is 2.42848859 for uniform and 1.07055223 for each cosine/sine q-mode. Their different probe norms prevent naive direct interpretation as source-independent susceptibility suppression.
- An explicitly Maxwell current-free locally harmonic cubic magnetic potential `Phi=x^3-3xy^2` has a quadratic magnetic field. Sample it at the same three-cell Wannier site coordinates; take its actual finite source amplitude G and chemical potential μ as independent grand-canonical controls. `M=-∂_G Ω`, `N=-∂_μ Ω`; the finite mixed Maxwell identity `∂_μ M=∂_G N` passes central finite differences with residual ~8.7293e-8, agreeing with the independent Fermi-operator derivative ~3.0023366.
- The finite three-cell ring boundary with spatially inhomogeneous B is a controlled Hamiltonian fixture; it does not constitute a material-validated open-boundary film, finite coil or source-conserving EM stress. Zeeman strengths/lattice coordinates are dimensionless until physical source calibration.

## What is explicitly still not paid
Original Sato/Hayami Bloch Eq.11 full 18-component spin magnetic octupole, measured PtMn3 crystal magnetic domain and Wannier/spin basis, MgO interface channel data, calibrated field Hessian and force gradient, source coil Maxwell stress and reaction, physical Tmunu/Einstein field, six typed antigravity observation targets. No repulsive gravitational field or human levitation demonstrated.

# NV microwave-to-optical sensitivity max-cut — 22 October 2026

## Implemented
- `DASHI/Physics/QuantumSensors/NVODMRDetuningSymmetryExact.agda` provides a finite rational detuning denominator symmetry and an axial magnetic-field shift identity, source-written but not kernel checked.
- `scripts/check_nv_odmr_microwave_sensitivity.py` provides a symbolic Lorentzian line-shape model for a single NV transition under weak drive, with background fluorescence, contrast and linewidth parameters. It checks its detuning derivative, sign of field response, parity and conditional Poisson Fisher information.

Define detuning Δ=f_drive-(D+gamma B), Lorentzian L=Γ²/(Δ²+Γ²), expected photon count mu=bright(1-C L)+background. For linewidth Γ>0, photon brightness>0, background>=0, 0<C<1, and mu>0, ideal Poisson information I_B=(∂_B mu)²/mu. The script verifies algebra at Δ=Γ. The selected point is a convenient analytical fixture, NOT the global Fisher optimum, which depends on background and contrast.

This is one phenomenological resonance branch. The actual spin-1 NV ensemble includes both m_s=±1, transverse strain/field mixing, microwave polarization, hyperfine structure and orientation distributions. Detector deadtime, optical pulse time, collection efficiency, spin polarization, relaxations and technical background affect physical sensitivity. Thus this is neither an empirical sensitivity figure nor a physical lower limit for a particular MCG system.

## Cross-pollination
Reuse the source-attested optics propagation/collection and SPAD measurement owners, but do not identify a specific reported MCG instrument with a particular sensor architecture without a source-backed hardware receipt. Keep optical laser pumping, visible optogenetic stimulation and mitochondrial mid-IR stimulation as different physical interventions whose timing, heating, photon metrology and statistical inference can share methodology.

## Open physical cut
A sourced quantum master equation (including optical spin-selective intersystem crossing) and calibrated ODMR data are still necessary to map illumination/microwave pulse settings to spin populations and photon likelihood. Paired gradiometer and spatial biological current data are necessary for field reconstruction. KK 5D Einstein–Maxwell physical derivation is separate from the NV optical transfer.

## Verification
No CI or Agda kernel check run at user request. Committing a checker is not the same as executing it; no executable result is claimed in this round.

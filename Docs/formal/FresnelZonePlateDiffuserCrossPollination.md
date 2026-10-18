# Fresnel zone plates ↔ diffuser imaging ↔ observer fibres

## Verified external source identities

1. *Single-shot lensless imaging with fresnel zone aperture and incoherent
   illumination*, Light: Science & Applications (2020).
   DOI: 10.1038/s41377-020-0289-9.
   https://doi.org/10.1038/s41377-020-0289-9
   The paper uses a Fresnel zone aperture mask, compressive reconstruction,
   and discusses the relationship between a zone-plate pattern and a point
   source hologram. **This is a separate source from the Waller tutorial
   transcript.**
2. Jihui Chen, Feng Wang, Yulong Li, Xing Zhang, Ke Yao,
   Zanyang Guan, Xiangming Liu (2023), *Lensless computationally defined
   confocal incoherent imaging with a Fresnel zone plane as coded aperture*,
   Optics Letters 48(17), 4520–4523.
   DOI: 10.1364/OL.497086.
   https://doi.org/10.1364/OL.497086
   Reports an FZP-coded point signature associated with lateral and axial
   position and compressed-sensing reconstruction.
3. Xuanyu Zhang, Ming Gao, Jiawei Wan, Zihan Liu, Tianshui Yu,
   Wenbo Wan, Qiegen Liu (2026), *Coding-domain prior-aided FZA lensless
   imaging under finite-sampling*, Optics and Lasers in Engineering 202,
   109762. DOI: 10.1016/j.optlaseng.2026.109762.
   https://doi.org/10.1016/j.optlaseng.2026.109762
   Finite-sampling and twin-image/reconstruction issues are explicitly
   part of the published technical landscape.

## Mathematical connection

The physical mask differs:
- a pseudorandom **diffuser** generates calibrated scene-dependent caustic
  intensity point-spread functions;
- a **Fresnel zone plate** is a designed ring structure, with an idealised
  paraxial zone boundary approximately r_n² ≃ n λ f, and with wavelength-
  dependent diffractive propagation;
- a phase zone plate and amplitude zone plate do not share a universal
  throughput or coherent field transfer function.

Both admit a codec-style observation model for a suitable regime:

    3D source -> optical field/flux -> PSF-coded detector intensity
       -> full-well / shot noise / ADC -> recorded image -> decoder

For mutually incoherent sources, the expected detected intensity can
superpose across scene points. Coherent fields instead add as amplitudes
*before* intensity measurement; this can create interference cross terms.
Never identify the linear-intensity coding matrix H with a coherent complex
field propagator without a same-object physical bridge.

A zone plate shares a historical and mathematical relationship with point
source holography, but an incoherent coded-intensity measurement need not
measure optical phase. Likewise, the repository's
`DASHI/Physics/Holography/AreaLaw.agda` records a boundary/entropy
count abstraction rather than an optical wavefront hologram.

The finite Agda bridge:
`DASHI/Physics/Optics/FresnelZonePlateDiffuserCodecBridgeExact.agda`
defines separate physical masks, propagation/intensity calibration receipts,
an explicit saturated depth-collision example, its no-decoder theorem, and
a contrasting two-codeword round-trip with a restricted inverse.

Crucial boundary: the finite examples demonstrate possible recoverability
and loss, **not** that a measured zone-plate instrument realizes a particular
codebook, a sampling-optimal mask, or a guaranteed physical 3D inverse.

## Physical/empirical proof obligations

* Calibrated depth-indexed PSFs for the selected wavelength, mask geometry,
  thickness, propagation distances, sensor pixels and illumination regime.
* A target scene class C and quantitative restricted nullspace /
  stable-inverse guarantee for that *same calibrated* detector operator.
* Detector full-well, finite photons, ADC quantisation and read-noise model;
  explicit matched-flux comparison of mask versus diffuser versus lens.
* Characterise twin-image / parasitic diffraction-order ambiguity, finite
  sampling, off-axis response, occlusion and spectral colour mixing.
* Optimise the *recorded* observation information and reliable precision,
  not the nominal number of continuous-valued voxels in the decoded volume.

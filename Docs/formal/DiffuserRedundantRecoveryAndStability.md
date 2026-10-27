# Diffuser imaging: when multiple encodings recover information

This note corrects the overly broad reading of the earlier scalar saturation
example. A clipped detector element may lose its own distinction while the
**full recorded array** retains it through a different pattern coordinate.
The earlier theorem establishes `clip_1(1) = clip_1(2)`, **not** that the
entire diffuser image is necessarily non-injective.

## Constructive finite result

Module: `DASHI/Physics/Optics/DiffuserRedundantRecoveryExact.agda`.

Two possible depths are represented by two scene states. Prior to clipping
their two-sensor-codewords are

    near -> (1,0)
    far  -> (2,1)

After a capacity-one clip *per detector pixel*:

    near -> (1,0)
    far  -> (1,1)

The first pixel contains no near/far information after saturation, yet the
second pixel preserves the depth distinction.

The module gives an explicit decoder and proves:

    decodeDepth(recordedCode(scene)) = trueDepth(scene)

and

    decodeScene(recordedCode(scene)) = scene

for the selected two-state scene class. Therefore this complete recorded
two-pixel observation is injective on that class. Its first-pixel-only
projection is not. The proof is finite mathematics, NOT a physical
calibration of a diffuser or Fresnel zone plate.

This is the same consumer-indexed distinction owned by
`DASHI/Foundations/HyperformObserverFactorisationExact.agda`:
a consumer fails to descend through one coarse observation but can descend
through a richer independent refinement. Postprocessing an already-erased
observation cannot help; acquiring/retaining a second independent code
coordinate can.

## Quantitative conditional theorem

Module: `DASHI/Physics/Optics/DiffuserNoiseStableRecoveryExact.agda`.

Choose a calibrated encoder H restricted to admissible scenes C and
compatible scene/observation distance metrics. Suppose

    d_scene(u,v) <= kappa * d_sensor(Hu,Hv),   u,v in C

and a measured sample b and reconstructed admissible estimate vhat satisfy

    d_sensor(Hv,b) <= eps_noise
    d_sensor(b,Hvhat) <= eps_residual.

Then the triangle inequality yields

    d_scene(v,vhat) <= kappa*(eps_noise + eps_residual).

The theorem is proof-relevant and explicitly assumes the restricted
stability inequality. Its numerical conditioning constant must come from
the **actual chosen optical encoder and admissible scene family**.

Multiple overlapping codewords can therefore give useful redundancy. Their
quality depends on how distinct the *surviving joint patterns* are; mere
multiplicity of appearances does not guarantee additional information.

## Physical limits still not discharged

- Photon noise (shot-noise covariance depends on total illumination per
  sensor pixel) and read noise are not inferred from finite injectivity.
- Distinct 3D scene points require a calibrated spectral/depth response;
  codewords may be mutually correlated or nearly linearly dependent.
- Saturated measurements can be handled through censored likelihood or
  inequality constraints rather than discarded as if valid linear data.
- The strongest stochastic performance statements need a scene prior or
  minimax class, quantum efficiency, throughput, wavelength, exposure
  duration, background intensity and the full photon/ADC likelihood.
- Two sensor pixels in the example do not imply an information gain for
  a fixed photon budget; recovery can still be noise-dominated.
- For a fixed physical camera, additional spatially distributed independent
  photons/measurements may improve reconstruction. Merely making multiple
  algorithmic copies of the *same* saturated/quantised observation does not.

The highest-value next physical experiment is a **matched-photon**
comparison between a diffuser, a zone plate and a focused lens, evaluated
with depth accuracy, reconstruction error, saturation rate, and reliable
faint-on-bright contrast. The uniform restricted-stability condition for
that same calibrated instrument is the mathematical closure target.


## 2026 cross-pollination

These sources motivate tests. They do not discharge the formal physical
obligations above.

- *Large-scale compressive microscopy via diffractive multiplexing across a
  sensor array*, Nature Photonics (2026), DOI / article identifier
  s41566-026-01974-4. The reported instrument combines 48 independent sensors
  with a diffractive optical element that creates a multi-impulse PSF. The
  stated design goal is minimally ambiguous computational reconstruction of
  information falling between physical sensor regions. This is a physical
  example of the distinction formalized here: one local observation can omit a
  scene distinction while a richer joint optical code can preserve it.
- Landrot et al. (2026), *Full-field X-ray fluorescence imaging using a
  Fresnel zone plate as a coded aperture: optimized reconstruction algorithm
  and first trial of hyperspectral XANES mapping*, Journal of Synchrotron
  Radiation 33, 1093-1102, DOI 10.1107/S1600577526004789. The paper reports
  detector-linearity and pile-up correction issues and sensitivity to
  background and intensity-correction choices. These observations support
  keeping the finite sensor channel separate from the ideal optical encoder.
- Kawachi et al. (2026), *Single-Image Depth From Defocus With Coded Aperture
  and Diffusion Posterior Sampling*, IEEE Transactions on Computational
  Imaging 12, 1034-1045, DOI 10.1109/TCI.2026.3697618. The method combines a
  differentiable physical forward model with an explicit image prior. This is
  evidence that single-image depth recovery can require both a physical code
  and a constrained scene model. It is not evidence for unrestricted inverse
  recovery.

The formal consequence remains unchanged. Evaluate the information content of
the complete recorded observation. Do not infer whole-camera non-injectivity
from one saturated coordinate. Do not infer stable recovery merely from
multiple encodings.

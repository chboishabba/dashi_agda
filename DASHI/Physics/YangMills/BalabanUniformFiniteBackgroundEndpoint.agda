module DASHI.Physics.YangMills.BalabanUniformFiniteBackgroundEndpoint where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPatchRegimeGreenUniformity as Green
import DASHI.Physics.YangMills.BalabanExplicitSmallnessWindow as Window
import DASHI.Physics.YangMills.BalabanCriticalMapDisplacementWindow as Displacement
import DASHI.Physics.YangMills.BalabanUniformAnalyticSmallnessClosure as Smallness

------------------------------------------------------------------------
-- Final finite-volume endpoint before inserting the actual four-dimensional
-- regime estimates.
--
-- The certificate keeps together:
--   * common weighted G, grad G, and grad^2 G bounds;
--   * one positive chart/coercivity/Neumann/nonlinear radius;
--   * the correctly scaled displacement-at-zero self-map budget;
--   * the coherent Hodge, perturbation, residual, and contraction package.
------------------------------------------------------------------------

record UniformFiniteBackgroundInputs
    (Index State Bound : Set) : Set₁ where
  field
    greenData : Green.PatchRegimeGreenData Index State Bound
    smallnessData : Smallness.UniformAnalyticSmallnessInputs Index State Bound
    radiusWindow : Window.ExplicitSmallnessWindow Bound
    strictTransport : Window.StrictTransport radiusWindow
    displacementWindow : Displacement.CriticalMapDisplacementWindow Bound

    selectedRadiiAgree :
      Window.candidate radiusWindow ≡
      Displacement.selected displacementWindow

open UniformFiniteBackgroundInputs public

record UniformFiniteBackgroundCertificate
    (Index State Bound : Set) : Set₁ where
  field
    inputs : UniformFiniteBackgroundInputs Index State Bound
    commonGreenBounds : Green.CommonGreenBounds (greenData inputs)
    analyticSmallness :
      Smallness.UniformAnalyticSmallnessCertificate Index State Bound
    selectedWindow : Window.SelectedSmallnessWitness (radiusWindow inputs)
    displacementSelfMap :
      Displacement.DisplacementWindowCertificate (displacementWindow inputs)

open UniformFiniteBackgroundCertificate public

assembleUniformFiniteBackgroundEndpoint :
  ∀ {Index State Bound : Set} →
  (inputs : UniformFiniteBackgroundInputs Index State Bound) →
  UniformFiniteBackgroundCertificate Index State Bound
assembleUniformFiniteBackgroundEndpoint inputs = record
  { inputs = inputs
  ; commonGreenBounds = Green.assembleCommonGreenBounds (greenData inputs)
  ; analyticSmallness =
      Smallness.assembleUniformAnalyticSmallness (smallnessData inputs)
  ; selectedWindow =
      Window.selectCommonRadius (radiusWindow inputs) (strictTransport inputs)
  ; displacementSelfMap =
      Displacement.assembleDisplacementWindowCertificate
        (displacementWindow inputs)
  }

uniformFiniteBackgroundEndpointAssemblyLevel : ProofLevel
uniformFiniteBackgroundEndpointAssemblyLevel = machineChecked

uniformFiniteBackgroundRegimeInputsLevel : ProofLevel
uniformFiniteBackgroundRegimeInputsLevel = conditional

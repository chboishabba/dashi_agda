module DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Physics.FiniteToContinuumGeometry as FCG
import DASHI.Physics.BianchiLovelockCompletion as GR
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation

------------------------------------------------------------------------
-- BIDI GR-side compression.
--
-- The generic common-action layer asks for
--
--   GR StressEnergy = common metric variation.
--
-- But the existing literal GR closure already owns
--
--   EinsteinTensor = StressEnergy.
--
-- Therefore the genuinely variational theorem can target the geometrically
-- natural Einstein tensor.  The source equality then follows by the existing
-- field equation rather than being proved a second time.
------------------------------------------------------------------------

actualGREinsteinTensor :
  ∀ (U : Weld.UnifiedCandidate) (candidate : Weld.Candidate U) →
  FCG.ContinuumGeometry.Tensor2
    (FCG.ContinuumLorentzClosure.geometry
      (GR.EinsteinContinuumClosure.lorentzContinuum
        (Weld.grTarget U candidate)))
actualGREinsteinTensor U candidate =
  GR.EinsteinTensorData.EinsteinTensor
    (GR.EinsteinContinuumClosure.tensors (Weld.grTarget U candidate))

actualGRFieldEquation :
  ∀ (U : Weld.UnifiedCandidate) (candidate : Weld.Candidate U) →
  actualGREinsteinTensor U candidate
  ≡ Weld.actualGRStressEnergy U candidate
actualGRFieldEquation U candidate =
  GR.BianchiLovelockClosure.fieldEquation
    (GR.EinsteinContinuumClosure.laws (Weld.grTarget U candidate))

record EinsteinTensorVariationReceipt
    {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) : Set₁ where
  field
    -- Natural variational target: the common source variation equals the
    -- transported Einstein tensor on the same coarse-grained candidate.
    commonVariationEqualsEinsteinTensor :
      ∀ candidate regime →
      Weld.grRegime U regime →
      Variation.effectiveSourceVariation variation
        (Weld.coarseGrain U candidate regime) regime
      ≡
      Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
        (actualGREinsteinTensor U (Weld.coarseGrain U candidate regime))

open EinsteinTensorVariationReceipt public

------------------------------------------------------------------------
-- Compiler through the literal field equation G = T.
------------------------------------------------------------------------

einsteinTensorVariationBuildsGRIdentification :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) →
  EinsteinTensorVariationReceipt variation →
  Variation.EinsteinVariationIdentification variation
einsteinTensorVariationBuildsGRIdentification variation receipt = record
  { Variation.EinsteinVariationIdentification.variationEqualsEinsteinSource =
      λ candidate regime grAtRegime →
        let
          selected = Weld.coarseGrain U candidate regime
          fieldEquationShared =
            cong
              (Weld.grStressToShared U selected)
              (actualGRFieldEquation U selected)
          variationToEinstein =
            commonVariationEqualsEinsteinTensor
              receipt candidate regime grAtRegime
        in
        trans
          (sym fieldEquationShared)
          (sym variationToEinstein)
  }

------------------------------------------------------------------------
-- Boundary: G = T is already in the literal GR target; deriving G from the
-- common action remains the actual variational/continuum theorem.
------------------------------------------------------------------------

record EinsteinVariationBoundary : Set where
  constructor einsteinVariationBoundary
  field
    fieldEquationAloneDerivesCommonAction : Bool
    fieldEquationAloneDerivesCommonActionIsFalse :
      fieldEquationAloneDerivesCommonAction ≡ false

    commonVariationEqualsEinsteinTensorIsStillPhysicalTheorem : Bool
    commonVariationEqualsEinsteinTensorIsStillPhysicalTheoremIsTrue :
      commonVariationEqualsEinsteinTensorIsStillPhysicalTheorem ≡ true

    einsteinVariationPlusFieldEquationBuildsGRSourceIdentification : Bool
    einsteinVariationPlusFieldEquationBuildsGRSourceIdentificationIsTrue :
      einsteinVariationPlusFieldEquationBuildsGRSourceIdentification ≡ true

canonicalEinsteinVariationBoundary : EinsteinVariationBoundary
canonicalEinsteinVariationBoundary =
  einsteinVariationBoundary false refl true refl true refl

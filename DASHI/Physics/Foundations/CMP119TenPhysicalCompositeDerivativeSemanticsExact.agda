{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119TenPhysicalCompositeDerivativeSemanticsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.GRQFTCMP119CorrectedD1MaxCutExact as Corrected
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeFirstVariationRound145Exact as R145
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeD1ReductionRound152Exact as R152

------------------------------------------------------------------------
-- THE TEN FINITE D1 EXPRESSIONS ARE THE TEN PHYSICAL COMPOSITE DERIVATIVES
-- ONCE THE CORRECTED D1 SEMANTICS ARE SUPPLIED.
------------------------------------------------------------------------

physicalCompositeDerivative :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (presentData :
      Present10.SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical)
    (semantics :
      Corrected.CorrectedCMP119D1PhysicalSemantics
        (Present10.asPresentCutPhysicalSourceInputs presentData))
    (background :
      Source.Background
        (Carrier.source
          (Present.bc1Carrier
            (Present10.asPresentCutPhysicalSourceInputs presentData)))) →
  K.SymmetricTensorComponent4 →
  ℝ
physicalCompositeDerivative presentData semantics background component =
  let
    present = Present10.asPresentCutPhysicalSourceInputs presentData
    laws = Corrected.d1aBC2FirstVariationLinearity semantics
    family =
      R152.asRound145PhysicalCompositeFirstVariationFamily
        (Corrected.d1bPhysicalBackgroundTransportDerivative semantics)
  in
  R145.physicalComponentFirstVariation family
    (Finite.Component
      (Carrier.finiteAction (Present.bc1Carrier present)))
    background
    (Present10.symmetricSlotAsPresentCutFiniteTangent presentData component)

-- The consumer actually needs the global finite localized sum, not one local
-- component.  This theorem says the exact finite D1 sum used by the stress lane
-- is the sum of the literal physical composite derivatives.
tenSlotFiniteD1IsPhysicalCompositeSum :
  ∀ {History Cell cutoff trajectory split inputs source localization bc1Canonical}
    (presentData :
      Present10.SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical)
    (semantics :
      Corrected.CorrectedCMP119D1PhysicalSemantics
        (Present10.asPresentCutPhysicalSourceInputs presentData))
    (background :
      Source.Background
        (Carrier.source
          (Present.bc1Carrier
            (Present10.asPresentCutPhysicalSourceInputs presentData))))
    (component : K.SymmetricTensorComponent4) →
  let
    present = Present10.asPresentCutPhysicalSourceInputs presentData
    laws = Corrected.d1aBC2FirstVariationLinearity semantics
    tangent = Present10.symmetricSlotAsPresentCutFiniteTangent presentData component
    family =
      R152.asRound145PhysicalCompositeFirstVariationFamily
        (Corrected.d1bPhysicalBackgroundTransportDerivative semantics)
  in
  DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact.finiteLocalizedFirstVariation
    (Carrier.finiteAction (Present.bc1Carrier present))
    (DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact.asFirstVariationLinearity laws)
    background tangent
  ≡
  Finite.sumℝ
    (R145.physicalComponentFirstVariationValues family background tangent)
tenSlotFiniteD1IsPhysicalCompositeSum presentData semantics background component =
  let
    family =
      R152.asRound145PhysicalCompositeFirstVariationFamily
        (Corrected.d1bPhysicalBackgroundTransportDerivative semantics)
  in
  R145.finiteLocalizedD1IsPhysicalCompositeD1Sum
    family background
    (Present10.symmetricSlotAsPresentCutFiniteTangent presentData component)

oldD1bIsNotReintroducedByTenSlotEvaluation : Bool
oldD1bIsNotReintroducedByTenSlotEvaluation = false

oldD1bIsNotReintroducedByTenSlotEvaluationIsFalse :
  oldD1bIsNotReintroducedByTenSlotEvaluation ≡ false
oldD1bIsNotReintroducedByTenSlotEvaluationIsFalse = refl

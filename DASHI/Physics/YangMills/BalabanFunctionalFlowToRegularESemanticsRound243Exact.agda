{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFunctionalFlowToRegularESemanticsRound243Exact where

------------------------------------------------------------------------
-- ROUND243 / FUNCTION-VALUED SOURCE FLOW PAYS S_E1 + S_E2
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as R242
import DASHI.Physics.YangMills.BalabanPublishedFlowToRegularEProjectionRound241Exact as R241
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as R221
import DASHI.Physics.YangMills.BalabanRegularEPointwiseSemanticsRound239Exact as R239

functionalProjection :
  ∀ {trajectory split inputs} →
  R242.FunctionalRegularESourceFlowInputs
    {trajectory = trajectory} {split = split} inputs →
  R221.CMP119RegularESourceProjection inputs
functionalProjection source =
  R241.asRegularESourceProjection (R242.asR218SourceNativeFlow source)

functionalPointwiseSemantics :
  ∀ {trajectory split inputs}
    (source : R242.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs) →
  R239.CMP119RegularEPointwiseSemantics (functionalProjection source)
functionalPointwiseSemantics source = record
  { R239.CMP119RegularEPointwiseSemantics.Background = R242.Background source
  ; R239.CMP119RegularEPointwiseSemantics.evaluateRegularE = λ regular → regular
  ; R239.CMP119RegularEPointwiseSemantics.IsLiteralRegularEEvaluation =
      λ regular evaluation → evaluation ≡ regular
  ; R239.CMP119RegularEPointwiseSemantics.selectedRegularEEvaluationIsLiteral =
      λ _ → refl
  }

selectedRegularEPointwiseMeaningIsLiteral :
  ∀ {trajectory split inputs}
    (source : R242.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  R239.evaluateRegularE (functionalPointwiseSemantics source)
    (R221.selectedRegularE (functionalProjection source) scale)
  ≡ R242.selectedRegularEFunction source scale
selectedRegularEPointwiseMeaningIsLiteral source scale = refl

functionalFlowToRegularESemanticsCompilerLevel : ProofLevel
functionalFlowToRegularESemanticsCompilerLevel = machineChecked

-- S_E1 and S_E2 are compiler consequences on this preferred representation.
-- The surviving source leaf is the literal function-valued CMP119 family.
literalFunctionalCMP119PublishedFlowLevel : ProofLevel
literalFunctionalCMP119PublishedFlowLevel = R242.literalFunctionalCMP119PublishedFlowLevel

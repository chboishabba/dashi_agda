{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanMarkedStressLiteralDerivativeRound111Exact where

------------------------------------------------------------------------
-- ROUND111: COMPLETED MARKED STRESS FUNCTIONAL IS THE LITERAL SOURCE DERIVATIVE
--
-- Round85 already proves that the nuclear field functional of a completed marked
-- source is its literal source derivative evaluated at the completed composite.
-- Round109 identifies the completed stress composite with the literal Clay
-- `stressTensor Y G`.  Therefore no additional completion-to-derivative theorem
-- is physical: congruence + transitivity give it automatically.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

completedMarkedStressFunctionalIsLiteralClayStressDerivative :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (completion : R109.LiteralSchwingerStressMarkedCompletion Y group) →
  let sources = R109.completedSources completion
      fields = StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields sources
      stressField = StressMarked.stressField fields
      stressData = StressMarked.stressData sources
  in
  Marked.fieldFunctional stressField
  ≡ Marked.sourceDerivative stressData (Top.stressTensor Y group)
completedMarkedStressFunctionalIsLiteralClayStressDerivative completion =
  let
    sources = R109.completedSources completion
    fields = StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields sources
    stressField = StressMarked.stressField fields
    stressData = StressMarked.stressData sources

    functionalIsCompletedDerivative =
      Marked.fieldFunctionalIsLiteralSourceDerivative stressField

    completedTensorIsLiteral =
      R109.literalStressIsCompletedMarkedStress completion

    derivativeAtLiteral =
      cong (Marked.sourceDerivative stressData) completedTensorIsLiteral
  in
  trans functionalIsCompletedDerivative derivativeAtLiteral

markedStressLiteralDerivativeCompilerLevel : ProofLevel
markedStressLiteralDerivativeCompilerLevel = machineChecked

-- Remaining physical seam is upstream: identify the CMP119 stress insertion and
-- its Cauchy completion with this already-completed marked source derivative.
cmp119StressCompletionIsMarkedSourceDerivativeLevel : ProofLevel
cmp119StressCompletionIsMarkedSourceDerivativeLevel = conditional

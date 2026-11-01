module DASHI.Physics.QFT.SU2LevelFlowFormalReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- SU(2) level-flow formal candidate receipt.
--
-- This receipt records the candidate statement that a p3-lane SU(2)_3
-- sector may flow to an effective SU(2)_1 weak-sector candidate after two
-- heavy generations are integrated out.  It is formal bookkeeping only:
-- no exact SU(2)_L gauge construction, exact Standard Model match, or
-- G_DHR ~= G_SM promotion is introduced.

data SU2LevelFlowStatus : Set where
  candidateAfterIntegratingOutTwoHeavyGenerations :
    SU2LevelFlowStatus

data SU2LevelFlowStep : Set where
  startWithP3SU2LevelThree :
    SU2LevelFlowStep

  integrateOutTwoHeavyGenerations :
    SU2LevelFlowStep

  retainEffectiveSU2LevelOneCandidate :
    SU2LevelFlowStep

canonicalSU2LevelFlowSteps :
  List SU2LevelFlowStep
canonicalSU2LevelFlowSteps =
  startWithP3SU2LevelThree
  ∷ integrateOutTwoHeavyGenerations
  ∷ retainEffectiveSU2LevelOneCandidate
  ∷ []

p3SU2BareLevel :
  Nat
p3SU2BareLevel =
  3

heavyGenerationsIntegratedOut :
  Nat
heavyGenerationsIntegratedOut =
  2

effectiveSU2WeakLevelCandidate :
  Nat
effectiveSU2WeakLevelCandidate =
  1

levelFlowFormulaLabel :
  String
levelFlowFormulaLabel =
  "candidate level-flow bookkeeping: k_eff = k_p3 - number-of-heavy-generations = 3 - 2 = 1"

p3SU2LevelThreeLabel :
  String
p3SU2LevelThreeLabel =
  "p3 starts as an SU(2)_3 candidate lane"

heavyGenerationBoundaryLabel :
  String
heavyGenerationBoundaryLabel =
  "two heavier generations are treated as integrated-out formal degrees of freedom"

effectiveSU2LevelOneLabel :
  String
effectiveSU2LevelOneLabel =
  "the remaining effective weak-sector candidate is SU(2)_1"

candidateOnlyBoundaryLabel :
  String
candidateOnlyBoundaryLabel =
  "candidate level-flow receipt only; exact gauge, Standard Model, and G_DHR ~= G_SM flags remain false"

canonicalSU2LevelFlowBoundary :
  List String
canonicalSU2LevelFlowBoundary =
  p3SU2LevelThreeLabel
  ∷ heavyGenerationBoundaryLabel
  ∷ levelFlowFormulaLabel
  ∷ effectiveSU2LevelOneLabel
  ∷ candidateOnlyBoundaryLabel
  ∷ []

record SU2LevelFlowFormalReceipt : Set where
  field
    status :
      SU2LevelFlowStatus

    statusIsCandidateAfterTwoHeavyGenerations :
      status ≡ candidateAfterIntegratingOutTwoHeavyGenerations

    flowSteps :
      List SU2LevelFlowStep

    flowStepsAreCanonical :
      flowSteps ≡ canonicalSU2LevelFlowSteps

    p3StartingLevel :
      Nat

    p3StartingLevelIsThree :
      p3StartingLevel ≡ p3SU2BareLevel

    integratedOutHeavyGenerationCount :
      Nat

    integratedOutHeavyGenerationCountIsTwo :
      integratedOutHeavyGenerationCount ≡ heavyGenerationsIntegratedOut

    effectiveWeakLevel :
      Nat

    effectiveWeakLevelIsOne :
      effectiveWeakLevel ≡ effectiveSU2WeakLevelCandidate

    p3SU2LevelThreeCandidate :
      Bool

    p3SU2LevelThreeCandidateIsTrue :
      p3SU2LevelThreeCandidate ≡ true

    twoHeavyGenerationsIntegratedOutCandidate :
      Bool

    twoHeavyGenerationsIntegratedOutCandidateIsTrue :
      twoHeavyGenerationsIntegratedOutCandidate ≡ true

    su2LevelOneCandidate :
      Bool

    su2LevelOneCandidateIsTrue :
      su2LevelOneCandidate ≡ true

    levelFlowFormula :
      String

    levelFlowFormulaIsCanonical :
      levelFlowFormula ≡ levelFlowFormulaLabel

    p3SU2LevelThreeBoundary :
      String

    p3SU2LevelThreeBoundaryIsCanonical :
      p3SU2LevelThreeBoundary ≡ p3SU2LevelThreeLabel

    heavyGenerationBoundary :
      String

    heavyGenerationBoundaryIsCanonical :
      heavyGenerationBoundary ≡ heavyGenerationBoundaryLabel

    effectiveSU2LevelOneBoundary :
      String

    effectiveSU2LevelOneBoundaryIsCanonical :
      effectiveSU2LevelOneBoundary ≡ effectiveSU2LevelOneLabel

    exactGaugePromotion :
      Bool

    exactGaugePromotionIsFalse :
      exactGaugePromotion ≡ false

    exactSU2LPromotion :
      Bool

    exactSU2LPromotionIsFalse :
      exactSU2LPromotion ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    candidateOnlyBoundary :
      String

    candidateOnlyBoundaryIsCanonical :
      candidateOnlyBoundary ≡ candidateOnlyBoundaryLabel

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalSU2LevelFlowBoundary

open SU2LevelFlowFormalReceipt public

canonicalSU2LevelFlowFormalReceipt :
  SU2LevelFlowFormalReceipt
canonicalSU2LevelFlowFormalReceipt =
  record
    { status =
        candidateAfterIntegratingOutTwoHeavyGenerations
    ; statusIsCandidateAfterTwoHeavyGenerations =
        refl
    ; flowSteps =
        canonicalSU2LevelFlowSteps
    ; flowStepsAreCanonical =
        refl
    ; p3StartingLevel =
        p3SU2BareLevel
    ; p3StartingLevelIsThree =
        refl
    ; integratedOutHeavyGenerationCount =
        heavyGenerationsIntegratedOut
    ; integratedOutHeavyGenerationCountIsTwo =
        refl
    ; effectiveWeakLevel =
        effectiveSU2WeakLevelCandidate
    ; effectiveWeakLevelIsOne =
        refl
    ; p3SU2LevelThreeCandidate =
        true
    ; p3SU2LevelThreeCandidateIsTrue =
        refl
    ; twoHeavyGenerationsIntegratedOutCandidate =
        true
    ; twoHeavyGenerationsIntegratedOutCandidateIsTrue =
        refl
    ; su2LevelOneCandidate =
        true
    ; su2LevelOneCandidateIsTrue =
        refl
    ; levelFlowFormula =
        levelFlowFormulaLabel
    ; levelFlowFormulaIsCanonical =
        refl
    ; p3SU2LevelThreeBoundary =
        p3SU2LevelThreeLabel
    ; p3SU2LevelThreeBoundaryIsCanonical =
        refl
    ; heavyGenerationBoundary =
        heavyGenerationBoundaryLabel
    ; heavyGenerationBoundaryIsCanonical =
        refl
    ; effectiveSU2LevelOneBoundary =
        effectiveSU2LevelOneLabel
    ; effectiveSU2LevelOneBoundaryIsCanonical =
        refl
    ; exactGaugePromotion =
        false
    ; exactGaugePromotionIsFalse =
        refl
    ; exactSU2LPromotion =
        false
    ; exactSU2LPromotionIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; candidateOnlyBoundary =
        candidateOnlyBoundaryLabel
    ; candidateOnlyBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        canonicalSU2LevelFlowBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

su2LevelFlowStartsAtP3LevelThree :
  p3StartingLevel canonicalSU2LevelFlowFormalReceipt
  ≡
  3
su2LevelFlowStartsAtP3LevelThree =
  refl

su2LevelFlowIntegratesOutTwoHeavyGenerations :
  integratedOutHeavyGenerationCount canonicalSU2LevelFlowFormalReceipt
  ≡
  2
su2LevelFlowIntegratesOutTwoHeavyGenerations =
  refl

su2LevelFlowEndsAtLevelOneCandidate :
  effectiveWeakLevel canonicalSU2LevelFlowFormalReceipt
  ≡
  1
su2LevelFlowEndsAtLevelOneCandidate =
  refl

su2LevelFlowExactGaugePromotionFalse :
  exactGaugePromotion canonicalSU2LevelFlowFormalReceipt
  ≡
  false
su2LevelFlowExactGaugePromotionFalse =
  refl

su2LevelFlowExactSMFalse :
  exactStandardModelPromotion canonicalSU2LevelFlowFormalReceipt
  ≡
  false
su2LevelFlowExactSMFalse =
  refl

su2LevelFlowExactGDHRGSMFalse :
  exactGDHREqualsGSMPromotion canonicalSU2LevelFlowFormalReceipt
  ≡
  false
su2LevelFlowExactGDHRGSMFalse =
  refl

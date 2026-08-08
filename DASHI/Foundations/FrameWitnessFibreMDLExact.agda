module DASHI.Foundations.FrameWitnessFibreMDLExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.ActionMDLSeparation as ActionMDL
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.DialecticSheetFrameSelectorExact as Selector

------------------------------------------------------------------------
-- A Stage-3 witness is a frame together with positive evaluations for P, Q,
-- and S and a proof that S is actually synthesised from P and Q in that frame.
-- The witness fibre retains every admissible frame before any MDL policy picks
-- one representative.
------------------------------------------------------------------------

data CandidateFrame : Set where
  compactFrame expansiveFrame counterFrame : CandidateFrame

data CandidateCondition : Set where
  conditionP conditionQ synthesisS : CandidateCondition

candidateEvaluate :
  CandidateFrame → CandidateCondition → BT.BalancedDigit
candidateEvaluate compactFrame conditionP = BT.pos
candidateEvaluate compactFrame conditionQ = BT.pos
candidateEvaluate compactFrame synthesisS = BT.pos
candidateEvaluate expansiveFrame conditionP = BT.pos
candidateEvaluate expansiveFrame conditionQ = BT.pos
candidateEvaluate expansiveFrame synthesisS = BT.pos
candidateEvaluate counterFrame conditionP = BT.pos
candidateEvaluate counterFrame conditionQ = BT.pos
candidateEvaluate counterFrame synthesisS = BT.neg

data CandidateSynthesis :
  CandidateFrame →
  CandidateCondition → CandidateCondition → CandidateCondition → Set where
  compactSynthesis :
    CandidateSynthesis compactFrame conditionP conditionQ synthesisS
  expansiveSynthesis :
    CandidateSynthesis expansiveFrame conditionP conditionQ synthesisS

candidateSemantics :
  Selector.FrameSemantics CandidateFrame CandidateCondition
candidateSemantics = record
  { Selector.evaluate = candidateEvaluate
  ; Selector.synthesises = CandidateSynthesis
  }

ClosesThreeAt : CandidateFrame → Set
ClosesThreeAt frame =
  candidateEvaluate frame conditionP ≡ BT.pos
  × candidateEvaluate frame conditionQ ≡ BT.pos
  × candidateEvaluate frame synthesisS ≡ BT.pos
  × CandidateSynthesis frame conditionP conditionQ synthesisS

Stage3WitnessFibre : Set
Stage3WitnessFibre = Σ CandidateFrame ClosesThreeAt

compactClosure : ClosesThreeAt compactFrame
compactClosure = refl , refl , refl , compactSynthesis

expansiveClosure : ClosesThreeAt expansiveFrame
expansiveClosure = refl , refl , refl , expansiveSynthesis

compactWitness : Stage3WitnessFibre
compactWitness = compactFrame , compactClosure

expansiveWitness : Stage3WitnessFibre
expansiveWitness = expansiveFrame , expansiveClosure

allAdmissibleWitnesses : List Stage3WitnessFibre
allAdmissibleWitnesses = compactWitness ∷ expansiveWitness ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = 1 + listCount xs

admissibleWitnessCountIsTwo : listCount allAdmissibleWitnesses ≡ 2
admissibleWitnessCountIsTwo = refl

counterFrameDoesNotClose : ClosesThreeAt counterFrame → ⊥
counterFrameDoesNotClose (_ , _ , () , _)

------------------------------------------------------------------------
-- Conversion to the repository's existing dependent FrameWitness record.
------------------------------------------------------------------------

compactDependentWitness :
  Selector.FrameWitness
    candidateSemantics conditionP conditionQ synthesisS
compactDependentWitness =
  Selector.frameWitness compactFrame refl refl refl compactSynthesis

expansiveDependentWitness :
  Selector.FrameWitness
    candidateSemantics conditionP conditionQ synthesisS
expansiveDependentWitness =
  Selector.frameWitness expansiveFrame refl refl refl expansiveSynthesis

------------------------------------------------------------------------
-- Exact finite MDL policy.  Costs retain the five requested components:
-- description length, contradiction, overreach, omission, and residual cost.
-- The ActionMDLSeparation interface supplies the actual minimality contract.
------------------------------------------------------------------------

record FrameCost : Set where
  constructor frameCost
  field
    descriptionLength contradiction overreach omission residualCost : Nat

open FrameCost public

totalFrameCost : FrameCost → Nat
totalFrameCost cost =
  descriptionLength cost
  + contradiction cost
  + overreach cost
  + omission cost
  + residualCost cost

frameCostOf : CandidateFrame → FrameCost
frameCostOf compactFrame = frameCost 1 0 0 0 1
frameCostOf expansiveFrame = frameCost 2 1 2 0 2
frameCostOf counterFrame = frameCost 1 3 0 2 3

compactTotalCostIsTwo : totalFrameCost (frameCostOf compactFrame) ≡ 2
compactTotalCostIsTwo = refl

expansiveTotalCostIsSeven :
  totalFrameCost (frameCostOf expansiveFrame) ≡ 7
expansiveTotalCostIsSeven = refl

counterTotalCostIsNine : totalFrameCost (frameCostOf counterFrame) ≡ 9
counterTotalCostIsNine = refl

frameDescriptionLength : ActionMDL.DescriptionLength CandidateFrame ⊤
frameDescriptionLength = record
  { ActionMDL.sideLength = λ frame →
      descriptionLength (frameCostOf frame)
      + contradiction (frameCostOf frame)
      + overreach (frameCostOf frame)
      + omission (frameCostOf frame)
  ; ActionMDL.residualLength = λ frame _ → residualCost (frameCostOf frame)
  }

selectCompact : ⊤ → CandidateFrame
selectCompact tt = compactFrame

compactIsMinimal :
  (dataPoint : ⊤) →
  (frame : CandidateFrame) →
  ActionMDL.totalLength frameDescriptionLength (selectCompact dataPoint) dataPoint
  ≤ ActionMDL.totalLength frameDescriptionLength frame dataPoint
compactIsMinimal tt compactFrame = s≤s (s≤s z≤n)
compactIsMinimal tt expansiveFrame = s≤s (s≤s z≤n)
compactIsMinimal tt counterFrame = s≤s (s≤s z≤n)

canonicalFrameMDLSelection :
  ActionMDL.MDLSelection CandidateFrame ⊤ frameDescriptionLength
canonicalFrameMDLSelection = record
  { ActionMDL.selected = selectCompact
  ; ActionMDL.minimal = compactIsMinimal
  }

selectedFrameIsCompact :
  ActionMDL.MDLSelection.selected canonicalFrameMDLSelection tt
  ≡ compactFrame
selectedFrameIsCompact = refl

------------------------------------------------------------------------
-- The selector operates after witness construction.  It does not erase the
-- witness fibre and does not turn existence under one frame into universality.
------------------------------------------------------------------------

record WitnessFibreMDLBoundary : Set where
  constructor witnessFibreMDLBoundary
  field
    allAdmissibleWitnessesRetained : Bool
    allAdmissibleWitnessesRetainedIsTrue :
      allAdmissibleWitnessesRetained ≡ true
    finiteMDLMinimiserConstructed : Bool
    finiteMDLMinimiserConstructedIsTrue :
      finiteMDLMinimiserConstructed ≡ true
    oneClosingFrameMakesEveryFrameClose : Bool
    oneClosingFrameMakesEveryFrameCloseIsFalse :
      oneClosingFrameMakesEveryFrameClose ≡ false
    lowestCostFrameIsUniversallyTrue : Bool
    lowestCostFrameIsUniversallyTrueIsFalse :
      lowestCostFrameIsUniversallyTrue ≡ false
    finiteNaturalCostIsMachineIndependentKolmogorovComplexity : Bool
    finiteNaturalCostIsMachineIndependentKolmogorovComplexityIsFalse :
      finiteNaturalCostIsMachineIndependentKolmogorovComplexity ≡ false

canonicalWitnessFibreMDLBoundary : WitnessFibreMDLBoundary
canonicalWitnessFibreMDLBoundary =
  witnessFibreMDLBoundary
    true refl
    true refl
    false refl
    false refl
    false refl

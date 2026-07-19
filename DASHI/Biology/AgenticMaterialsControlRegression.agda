module DASHI.Biology.AgenticMaterialsControlRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Biology.AgenticMaterialsControlCore

------------------------------------------------------------------------
-- A finite wound-repair toy model.

-- damaged2 -> damaged1 -> viable0, while viable0 is fixed.
data TissueState : Set where
  viable0 damaged1 damaged2 : TissueState

data TissueAction : Set where
  hold repairOne repairTwo : TissueAction

data TissueDefect : Set where
  d0 d1 d2 : TissueDefect

data BetterDefect : TissueDefect → TissueDefect → Set where
  zeroFixed : BetterDefect d0 d0
  oneToZero : BetterDefect d0 d1
  twoToOne : BetterDefect d1 d2

observeTissue : TissueState → TissueState
observeTissue x = x

repairPolicy : TissueState → TissueAction
repairPolicy viable0 = hold
repairPolicy damaged1 = repairOne
repairPolicy damaged2 = repairTwo

actuateTissue : TissueAction → TissueState → TissueState
actuateTissue hold viable0 = viable0
actuateTissue hold damaged1 = damaged1
actuateTissue hold damaged2 = damaged2
actuateTissue repairOne viable0 = viable0
actuateTissue repairOne damaged1 = viable0
actuateTissue repairOne damaged2 = damaged1
actuateTissue repairTwo viable0 = viable0
actuateTissue repairTwo damaged1 = viable0
actuateTissue repairTwo damaged2 = damaged1

tissueDefect : TissueState → TissueDefect
tissueDefect viable0 = d0
tissueDefect damaged1 = d1
tissueDefect damaged2 = d2

canonicalOpenBookkeeping : OpenSystemBookkeeping
canonicalOpenBookkeeping =
  record
    { EnergyCarrier = Bool
    ; EntropyCarrier = Bool
    ; intake = true
    ; exportedWaste = true
    ; localOrderMaintained = true
    ; localOrderMaintainedIsTrue = refl
    ; globalEntropyDecreaseClaimed = false
    ; globalEntropyDecreaseClaimedIsFalse = refl
    }

canonicalTissueMaterial : AgenticMaterial
canonicalTissueMaterial =
  record
    { State = TissueState
    ; Observation = TissueState
    ; Action = TissueAction
    ; Defect = TissueDefect
    ; observe = observeTissue
    ; policy = repairPolicy
    ; actuate = actuateTissue
    ; defect = tissueDefect
    ; target = viable0
    ; better = BetterDefect
    ; targetHasNoCorrectiveMotion = refl
    ; correctionImproves = correctionAtTarget
    ; offTargetCorrectionImproves = correctionImproves
    ; thermodynamics = canonicalOpenBookkeeping
    }
  where
    correctionAtTarget :
      (x : TissueState) →
      x ≡ viable0 →
      actuateTissue (repairPolicy (observeTissue x)) x ≡ viable0
    correctionAtTarget viable0 refl = refl

    correctionImproves :
      (x : TissueState) →
      (x ≡ viable0 → Bool) →
      BetterDefect
        (tissueDefect
          (actuateTissue (repairPolicy (observeTissue x)) x))
        (tissueDefect x)
    correctionImproves viable0 offTarget = zeroFixed
    correctionImproves damaged1 offTarget = oneToZero
    correctionImproves damaged2 offTarget = twoToOne

canonicalTissueTargetFixed :
  closedLoopStep canonicalTissueMaterial viable0 ≡ viable0
canonicalTissueTargetFixed =
  closedLoopTargetFixed canonicalTissueMaterial

canonicalDamagedOneImproves :
  BetterDefect
    (tissueDefect (closedLoopStep canonicalTissueMaterial damaged1))
    (tissueDefect damaged1)
canonicalDamagedOneImproves =
  closedLoopCorrectionImproves
    canonicalTissueMaterial
    damaged1
    (λ ())

canonicalDamagedTwoImproves :
  BetterDefect
    (tissueDefect (closedLoopStep canonicalTissueMaterial damaged2))
    (tissueDefect damaged2)
canonicalDamagedTwoImproves =
  closedLoopCorrectionImproves
    canonicalTissueMaterial
    damaged2
    (λ ())

canonicalNoGlobalEntropyDecreaseClaim :
  globalEntropyDecreaseClaimed
    (thermodynamics canonicalTissueMaterial) ≡ false
canonicalNoGlobalEntropyDecreaseClaim =
  agenticMaterialDoesNotClaimGlobalEntropyDecrease
    canonicalTissueMaterial

------------------------------------------------------------------------
-- A prion-like templating witness remains outside the agency gate.

data FoldState : Set where
  native misfolded : FoldState

prionTemplate : FoldState → FoldState → FoldState
prionTemplate native x = x
prionTemplate misfolded native = misfolded
prionTemplate misfolded misfolded = misfolded

canonicalPrionLikePropagation : TemplatedPropagation
canonicalPrionLikePropagation =
  record
    { Carrier = FoldState
    ; propagate = prionTemplate
    ; selfAmplifying = true
    ; selfAmplifyingIsTrue = refl
    }

canonicalPrionLikeBoundary :
  PrionLikeBoundary canonicalPrionLikePropagation
canonicalPrionLikeBoundary =
  record
    { observationChannelAbsent = true
    ; observationChannelAbsentIsTrue = refl
    ; targetDefectAbsent = true
    ; targetDefectAbsentIsTrue = refl
    ; correctiveFeedbackAbsent = true
    ; correctiveFeedbackAbsentIsTrue = refl
    ; agencyPromoted = false
    ; agencyPromotedIsFalse = refl
    }

canonicalPrionLikePropagationNotAgency :
  agencyPromoted canonicalPrionLikeBoundary ≡ false
canonicalPrionLikePropagationNotAgency =
  prionLikePropagationIsNotAgency canonicalPrionLikeBoundary

module DASHI.Physics.QFT.QuarkLeptonCMUnitGroupReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.ConductorLevelCorrespondenceReceipt as Conductor
import DASHI.Physics.QFT.LeptonSectorGapReceipt as Lepton
import DASHI.Physics.QFT.TrialitySymmetryReceipt as Triality

------------------------------------------------------------------------
-- Quark/lepton CM unit-group receipt.
--
-- Failed hypothesis recorded here:
-- unit-group order alone separates quark and lepton lanes.  The obstruction
-- is D=-7: the active p5/quark-candidate lane has CM units Z/2, the same
-- unit-group order as the inspected lepton-lane candidates away from D=-3
-- and D=-4.  Therefore the conductor/discriminant distinction is needed, and
-- exact quark/lepton separation remains open.

data QuarkLeptonLaneKind : Set where
  quarkCandidateLane :
    QuarkLeptonLaneKind

  leptonCandidateLane :
    QuarkLeptonLaneKind

data CMUnitGroupLabel : Set where
  unitGroupZ4 :
    CMUnitGroupLabel

  unitGroupZ6 :
    CMUnitGroupLabel

  unitGroupZ2 :
    CMUnitGroupLabel

cmUnitGroupOrder :
  CMUnitGroupLabel →
  Nat
cmUnitGroupOrder unitGroupZ4 =
  4
cmUnitGroupOrder unitGroupZ6 =
  6
cmUnitGroupOrder unitGroupZ2 =
  2

data UnitGroupSeparationHypothesisStatus : Set where
  failedByDMinusSevenZ2Collision :
    UnitGroupSeparationHypothesisStatus

data QuarkLeptonSeparationStatus : Set where
  separationOpenNeedsConductorDiscriminantData :
    QuarkLeptonSeparationStatus

data UnitGroupOrderBlocker : Set where
  dMinusSevenHasZ2LikeLeptonLanes :
    UnitGroupOrderBlocker

  unitGroupOrderForgetsConductor :
    UnitGroupOrderBlocker

  unitGroupOrderForgetsDiscriminant :
    UnitGroupOrderBlocker

  exactQuarkRepresentationTableMissing :
    UnitGroupOrderBlocker

  exactLeptonRepresentationTableMissing :
    UnitGroupOrderBlocker

  exactDHRSMQuarkLeptonFunctorMissing :
    UnitGroupOrderBlocker

canonicalUnitGroupOrderBlockers :
  List UnitGroupOrderBlocker
canonicalUnitGroupOrderBlockers =
  dMinusSevenHasZ2LikeLeptonLanes
  ∷ unitGroupOrderForgetsConductor
  ∷ unitGroupOrderForgetsDiscriminant
  ∷ exactQuarkRepresentationTableMissing
  ∷ exactLeptonRepresentationTableMissing
  ∷ exactDHRSMQuarkLeptonFunctorMissing
  ∷ []

unitGroupOrderAloneFailedHypothesisLabel : String
unitGroupOrderAloneFailedHypothesisLabel =
  "Failed hypothesis: unit-group order alone separates quark and lepton lanes; D=-7 has Z/2 like lepton lanes"

conductorDiscriminantNeededLabel : String
conductorDiscriminantNeededLabel =
  "Conductor/discriminant distinction is needed before quark/lepton separation can be claimed"

quarkLeptonSeparationOpenLabel : String
quarkLeptonSeparationOpenLabel =
  "Exact quark/lepton separation remains open; no exact quark, lepton, SM, or G_DHR ~= G_SM promotion is made"

record CMUnitLaneObservation : Set where
  field
    laneKind :
      QuarkLeptonLaneKind

    discriminant :
      Lepton.ClassNumberOneDiscriminant

    discriminantLabel :
      String

    discriminantLabelIsCanonical :
      discriminantLabel
      ≡
      Lepton.classNumberOneDiscriminantLabel discriminant

    conductor :
      Nat

    unitGroup :
      CMUnitGroupLabel

    unitGroupOrder :
      Nat

    unitGroupOrderIsCanonical :
      unitGroupOrder ≡ cmUnitGroupOrder unitGroup

    observation :
      String

open CMUnitLaneObservation public

dMinusSevenQuarkCandidateZ2Observation :
  CMUnitLaneObservation
dMinusSevenQuarkCandidateZ2Observation =
  record
    { laneKind =
        quarkCandidateLane
    ; discriminant =
        Lepton.D-7
    ; discriminantLabel =
        "D=-7"
    ; discriminantLabelIsCanonical =
        refl
    ; conductor =
        7
    ; unitGroup =
        unitGroupZ2
    ; unitGroupOrder =
        2
    ; unitGroupOrderIsCanonical =
        refl
    ; observation =
        "D=-7 is the active p5/quark-candidate lane and has CM unit group Z/2"
    }

dMinusEightLeptonCandidateZ2Observation :
  CMUnitLaneObservation
dMinusEightLeptonCandidateZ2Observation =
  record
    { laneKind =
        leptonCandidateLane
    ; discriminant =
        Lepton.D-8
    ; discriminantLabel =
        "D=-8"
    ; discriminantLabelIsCanonical =
        refl
    ; conductor =
        8
    ; unitGroup =
        unitGroupZ2
    ; unitGroupOrder =
        2
    ; unitGroupOrderIsCanonical =
        refl
    ; observation =
        "D=-8 is only a lepton-lane candidate here, has modular/character level 8, and also has CM unit group Z/2"
    }

dMinusElevenLeptonCandidateZ2Observation :
  CMUnitLaneObservation
dMinusElevenLeptonCandidateZ2Observation =
  record
    { laneKind =
        leptonCandidateLane
    ; discriminant =
        Lepton.D-11
    ; discriminantLabel =
        "D=-11"
    ; discriminantLabelIsCanonical =
        refl
    ; conductor =
        11
    ; unitGroup =
        unitGroupZ2
    ; unitGroupOrder =
        2
    ; unitGroupOrderIsCanonical =
        refl
    ; observation =
        "D=-11 is only a lepton-lane candidate here and has CM unit group Z/2"
    }

dMinusTwelveLeptonCandidateZ2Observation :
  CMUnitLaneObservation
dMinusTwelveLeptonCandidateZ2Observation =
  record
    { laneKind =
        leptonCandidateLane
    ; discriminant =
        Lepton.D-12
    ; discriminantLabel =
        "D=-12"
    ; discriminantLabelIsCanonical =
        refl
    ; conductor =
        12
    ; unitGroup =
        unitGroupZ2
    ; unitGroupOrder =
        2
    ; unitGroupOrderIsCanonical =
        refl
    ; observation =
        "D=-12 is only a lepton-lane candidate here and has CM unit group Z/2"
    }

canonicalZ2CollisionObservations :
  List CMUnitLaneObservation
canonicalZ2CollisionObservations =
  dMinusSevenQuarkCandidateZ2Observation
  ∷ dMinusEightLeptonCandidateZ2Observation
  ∷ dMinusElevenLeptonCandidateZ2Observation
  ∷ dMinusTwelveLeptonCandidateZ2Observation
  ∷ []

data QuarkLeptonCMUnitPromotionFlag : Set where

quarkLeptonCMUnitPromotionFlagImpossibleHere :
  QuarkLeptonCMUnitPromotionFlag →
  ⊥
quarkLeptonCMUnitPromotionFlagImpossibleHere ()

record QuarkLeptonCMUnitGroupReceipt : Setω where
  field
    conductorLevelReceipt :
      Conductor.ConductorLevelCorrespondenceReceipt

    leptonSectorGapReceipt :
      Lepton.LeptonSectorGapReceipt

    trialitySymmetryReceipt :
      Triality.TrialitySymmetryReceipt

    failedHypothesisStatus :
      UnitGroupSeparationHypothesisStatus

    failedHypothesisStatusIsDMinusSevenCollision :
      failedHypothesisStatus ≡ failedByDMinusSevenZ2Collision

    failedHypothesisStatement :
      String

    failedHypothesisStatementIsCanonical :
      failedHypothesisStatement ≡ unitGroupOrderAloneFailedHypothesisLabel

    p5TrialityUnitOrder :
      Nat

    p5TrialityUnitOrderIsTwo :
      p5TrialityUnitOrder ≡ Triality.cmUnitOrder Triality.p5CMUnitLane

    dMinusSevenObservation :
      CMUnitLaneObservation

    dMinusSevenObservationIsCanonical :
      dMinusSevenObservation ≡ dMinusSevenQuarkCandidateZ2Observation

    dMinusSevenConductorIsSeven :
      conductor dMinusSevenObservation ≡ 7

    dMinusSevenUnitOrderIsTwo :
      unitGroupOrder dMinusSevenObservation ≡ 2

    dMinusElevenObservation :
      CMUnitLaneObservation

    dMinusElevenObservationIsCanonical :
      dMinusElevenObservation ≡ dMinusElevenLeptonCandidateZ2Observation

    dMinusElevenUnitOrderIsTwo :
      unitGroupOrder dMinusElevenObservation ≡ 2

    z2CollisionObservations :
      List CMUnitLaneObservation

    z2CollisionObservationsAreCanonical :
      z2CollisionObservations ≡ canonicalZ2CollisionObservations

    dMinusSevenHasZ2LikeLeptonLane :
      Bool

    dMinusSevenHasZ2LikeLeptonLaneIsTrue :
      dMinusSevenHasZ2LikeLeptonLane ≡ true

    unitGroupOrderAloneSeparatesQuarkLepton :
      Bool

    unitGroupOrderAloneSeparatesQuarkLeptonIsFalse :
      unitGroupOrderAloneSeparatesQuarkLepton ≡ false

    conductorDiscriminantDistinctionNeeded :
      Bool

    conductorDiscriminantDistinctionNeededIsTrue :
      conductorDiscriminantDistinctionNeeded ≡ true

    conductorDiscriminantStatement :
      String

    conductorDiscriminantStatementIsCanonical :
      conductorDiscriminantStatement ≡ conductorDiscriminantNeededLabel

    quarkLeptonSeparationStatus :
      QuarkLeptonSeparationStatus

    quarkLeptonSeparationStatusIsOpen :
      quarkLeptonSeparationStatus
      ≡
      separationOpenNeedsConductorDiscriminantData

    exactQuarkPromotion :
      Bool

    exactQuarkPromotionIsFalse :
      exactQuarkPromotion ≡ false

    exactLeptonPromotion :
      Bool

    exactLeptonPromotionIsFalse :
      exactLeptonPromotion ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    promotionFlags :
      List QuarkLeptonCMUnitPromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    blockers :
      List UnitGroupOrderBlocker

    blockersAreCanonical :
      blockers ≡ canonicalUnitGroupOrderBlockers

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ quarkLeptonSeparationOpenLabel

    auditTrail :
      List String

open QuarkLeptonCMUnitGroupReceipt public

canonicalQuarkLeptonCMUnitGroupReceipt :
  QuarkLeptonCMUnitGroupReceipt
canonicalQuarkLeptonCMUnitGroupReceipt =
  record
    { conductorLevelReceipt =
        Conductor.canonicalConductorLevelCorrespondenceReceipt
    ; leptonSectorGapReceipt =
        Lepton.canonicalLeptonSectorGapReceipt
    ; trialitySymmetryReceipt =
        Triality.canonicalTrialitySymmetryReceipt
    ; failedHypothesisStatus =
        failedByDMinusSevenZ2Collision
    ; failedHypothesisStatusIsDMinusSevenCollision =
        refl
    ; failedHypothesisStatement =
        unitGroupOrderAloneFailedHypothesisLabel
    ; failedHypothesisStatementIsCanonical =
        refl
    ; p5TrialityUnitOrder =
        2
    ; p5TrialityUnitOrderIsTwo =
        refl
    ; dMinusSevenObservation =
        dMinusSevenQuarkCandidateZ2Observation
    ; dMinusSevenObservationIsCanonical =
        refl
    ; dMinusSevenConductorIsSeven =
        refl
    ; dMinusSevenUnitOrderIsTwo =
        refl
    ; dMinusElevenObservation =
        dMinusElevenLeptonCandidateZ2Observation
    ; dMinusElevenObservationIsCanonical =
        refl
    ; dMinusElevenUnitOrderIsTwo =
        refl
    ; z2CollisionObservations =
        canonicalZ2CollisionObservations
    ; z2CollisionObservationsAreCanonical =
        refl
    ; dMinusSevenHasZ2LikeLeptonLane =
        true
    ; dMinusSevenHasZ2LikeLeptonLaneIsTrue =
        refl
    ; unitGroupOrderAloneSeparatesQuarkLepton =
        false
    ; unitGroupOrderAloneSeparatesQuarkLeptonIsFalse =
        refl
    ; conductorDiscriminantDistinctionNeeded =
        true
    ; conductorDiscriminantDistinctionNeededIsTrue =
        refl
    ; conductorDiscriminantStatement =
        conductorDiscriminantNeededLabel
    ; conductorDiscriminantStatementIsCanonical =
        refl
    ; quarkLeptonSeparationStatus =
        separationOpenNeedsConductorDiscriminantData
    ; quarkLeptonSeparationStatusIsOpen =
        refl
    ; exactQuarkPromotion =
        false
    ; exactQuarkPromotionIsFalse =
        refl
    ; exactLeptonPromotion =
        false
    ; exactLeptonPromotionIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; blockers =
        canonicalUnitGroupOrderBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        quarkLeptonSeparationOpenLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; auditTrail =
        unitGroupOrderAloneFailedHypothesisLabel
        ∷ "D=-7/p5 conductor is 7, but its CM unit-group order is only 2"
        ∷ "D=-8, D=-11, and D=-12 lepton-lane candidates also have CM unit-group order 2"
        ∷ conductorDiscriminantNeededLabel
        ∷ quarkLeptonSeparationOpenLabel
        ∷ []
    }

quarkLeptonUnitOrderAloneDoesNotSeparate :
  unitGroupOrderAloneSeparatesQuarkLepton
    canonicalQuarkLeptonCMUnitGroupReceipt
  ≡
  false
quarkLeptonUnitOrderAloneDoesNotSeparate =
  refl

quarkLeptonConductorDiscriminantNeeded :
  conductorDiscriminantDistinctionNeeded
    canonicalQuarkLeptonCMUnitGroupReceipt
  ≡
  true
quarkLeptonConductorDiscriminantNeeded =
  refl

quarkLeptonExactQuarkPromotionFalse :
  exactQuarkPromotion canonicalQuarkLeptonCMUnitGroupReceipt
  ≡
  false
quarkLeptonExactQuarkPromotionFalse =
  refl

quarkLeptonExactLeptonPromotionFalse :
  exactLeptonPromotion canonicalQuarkLeptonCMUnitGroupReceipt
  ≡
  false
quarkLeptonExactLeptonPromotionFalse =
  refl

quarkLeptonExactSMPromotionFalse :
  exactStandardModelPromotion canonicalQuarkLeptonCMUnitGroupReceipt
  ≡
  false
quarkLeptonExactSMPromotionFalse =
  refl

quarkLeptonExactGDHRGSMPromotionFalse :
  exactGDHREqualsGSMPromotion canonicalQuarkLeptonCMUnitGroupReceipt
  ≡
  false
quarkLeptonExactGDHRGSMPromotionFalse =
  refl

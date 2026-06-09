module DASHI.Physics.QFT.SMGaugeGroupCandidateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.EWSBFromCSHiggsReceipt as EWSB
import DASHI.Physics.QFT.KacMoodyLevelReceipt as KM
import DASHI.Physics.QFT.SMGaugeBosonsFromCSBoundaryReceipt as Bosons
import DASHI.Physics.QFT.SU3ColourFrom3LanesFusionReceipt as SU3
import DASHI.Physics.QFT.U1YFromCMCharacterReceipt as U1Y

------------------------------------------------------------------------
-- Aggregate Standard Model gauge-group candidate map.
--
-- This receipt aggregates the current U(1)_Y, SU(2)_L, and SU(3)_c candidate
-- evidence.  All three gauge-factor rows are marked true as candidates.  The
-- exact physical gauge group, DHR compact gauge group identification,
-- Standard Model promotion, and terminal promotion are all explicitly false.

data SMGaugeFactor : Set where
  U1YFactor :
    SMGaugeFactor

  SU2LFactor :
    SMGaugeFactor

  SU3cFactor :
    SMGaugeFactor

data GaugeCandidateSource : Set where
  cmCharacterSource :
    GaugeCandidateSource

  cswzwBoundarySource :
    GaugeCandidateSource

  threeLaneColourSource :
    GaugeCandidateSource

data GaugeCandidateStatus : Set where
  candidateOnly :
    GaugeCandidateStatus

data ExactGaugeGroupStatus : Set where
  exactPhysicalGaugeGroupOpen :
    ExactGaugeGroupStatus

record GaugeGroupCandidateRow : Set where
  field
    factor :
      SMGaugeFactor

    source :
      GaugeCandidateSource

    status :
      GaugeCandidateStatus

    candidateFlag :
      Bool

    candidateFlagIsTrue :
      candidateFlag ≡ true

    exactPhysicalFactorPromoted :
      Bool

    exactPhysicalFactorPromotedIsFalse :
      exactPhysicalFactorPromoted ≡ false

    rowBoundary :
      String

open GaugeGroupCandidateRow public

u1YCandidateBoundary : String
u1YCandidateBoundary =
  "U(1)_Y is a finite CM-character candidate; continuous embedding remains open"

su2LCandidateBoundary : String
su2LCandidateBoundary =
  "SU(2)_L is a CS/WZW weak-current candidate; exact physical weak gauge factor remains open"

su3cCandidateBoundary : String
su3cCandidateBoundary =
  "SU(3)_c is a colour-sector candidate; exact continuous colour gauge factor remains open"

u1YGaugeGroupCandidateRow :
  GaugeGroupCandidateRow
u1YGaugeGroupCandidateRow =
  record
    { factor =
        U1YFactor
    ; source =
        cmCharacterSource
    ; status =
        candidateOnly
    ; candidateFlag =
        true
    ; candidateFlagIsTrue =
        refl
    ; exactPhysicalFactorPromoted =
        false
    ; exactPhysicalFactorPromotedIsFalse =
        refl
    ; rowBoundary =
        u1YCandidateBoundary
    }

su2LGaugeGroupCandidateRow :
  GaugeGroupCandidateRow
su2LGaugeGroupCandidateRow =
  record
    { factor =
        SU2LFactor
    ; source =
        cswzwBoundarySource
    ; status =
        candidateOnly
    ; candidateFlag =
        true
    ; candidateFlagIsTrue =
        refl
    ; exactPhysicalFactorPromoted =
        false
    ; exactPhysicalFactorPromotedIsFalse =
        refl
    ; rowBoundary =
        su2LCandidateBoundary
    }

su3cGaugeGroupCandidateRow :
  GaugeGroupCandidateRow
su3cGaugeGroupCandidateRow =
  record
    { factor =
        SU3cFactor
    ; source =
        threeLaneColourSource
    ; status =
        candidateOnly
    ; candidateFlag =
        true
    ; candidateFlagIsTrue =
        refl
    ; exactPhysicalFactorPromoted =
        false
    ; exactPhysicalFactorPromotedIsFalse =
        refl
    ; rowBoundary =
        su3cCandidateBoundary
    }

canonicalGaugeGroupCandidateRows :
  List GaugeGroupCandidateRow
canonicalGaugeGroupCandidateRows =
  u1YGaugeGroupCandidateRow
  ∷ su2LGaugeGroupCandidateRow
  ∷ su3cGaugeGroupCandidateRow
  ∷ []

record SMGaugeGroupCandidateReceipt : Setω where
  field
    u1YReceipt :
      U1Y.U1YFromCMCharacterReceipt

    u1YExistingCandidateIsTrue :
      U1Y.U1YFromCMCharacterReceipt.discreteCharacterCandidate u1YReceipt
      ≡
      true

    su2KacMoodyLevelReading :
      KM.LevelReading

    su2KacMoodyLevelReadingIsCanonical :
      su2KacMoodyLevelReading ≡ KM.smWeakSU2KacMoodyLevel1Candidate

    gaugeBosonReceipt :
      Bosons.SMGaugeBosonsFromCSBoundaryReceipt

    su2WeakModesCandidateIsTrue :
      Bosons.SMGaugeBosonsFromCSBoundaryReceipt.wModesCandidate
        gaugeBosonReceipt
      ≡
      true

    su3Receipt :
      SU3.SU3ColourFrom3LanesFusionReceipt

    su3ExistingCandidateIsTrue :
      SU3.SU3ColourFrom3LanesFusionReceipt.su3ColourFromLaneFusionCandidate
        su3Receipt
      ≡
      true

    ewsbReceipt :
      EWSB.EWSBFromCSHiggsReceipt

    ewsbCandidateIsTrue :
      EWSB.EWSBFromCSHiggsReceipt.ewSymmetryBreakingCandidate ewsbReceipt
      ≡
      true

    rows :
      List GaugeGroupCandidateRow

    rowsAreCanonical :
      rows ≡ canonicalGaugeGroupCandidateRows

    u1YCandidate :
      Bool

    u1YCandidateIsTrue :
      u1YCandidate ≡ true

    su2LCandidate :
      Bool

    su2LCandidateIsTrue :
      su2LCandidate ≡ true

    su3cCandidate :
      Bool

    su3cCandidateIsTrue :
      su3cCandidate ≡ true

    allGaugeFactorsCandidate :
      Bool

    allGaugeFactorsCandidateIsTrue :
      allGaugeFactorsCandidate ≡ true

    exactGaugeGroupStatus :
      ExactGaugeGroupStatus

    exactGaugeGroupStatusIsOpen :
      exactGaugeGroupStatus ≡ exactPhysicalGaugeGroupOpen

    exactPhysicalGaugeGroup :
      Bool

    exactPhysicalGaugeGroupIsFalse :
      exactPhysicalGaugeGroup ≡ false

    exactGDHRGaugeGroup :
      Bool

    exactGDHRGaugeGroupIsFalse :
      exactGDHRGaugeGroup ≡ false

    exactGDHREqualsGSM :
      Bool

    exactGDHREqualsGSMIsFalse :
      exactGDHREqualsGSM ≡ false

    exactStandardModel :
      Bool

    exactStandardModelIsFalse :
      exactStandardModel ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    receiptBoundary :
      List String

open SMGaugeGroupCandidateReceipt public

canonicalSMGaugeGroupCandidateReceipt :
  SMGaugeGroupCandidateReceipt
canonicalSMGaugeGroupCandidateReceipt =
  record
    { u1YReceipt =
        U1Y.canonicalU1YFromCMCharacterReceipt
    ; u1YExistingCandidateIsTrue =
        refl
    ; su2KacMoodyLevelReading =
        KM.smWeakSU2KacMoodyLevel1Candidate
    ; su2KacMoodyLevelReadingIsCanonical =
        refl
    ; gaugeBosonReceipt =
        Bosons.canonicalSMGaugeBosonsFromCSBoundaryReceipt
    ; su2WeakModesCandidateIsTrue =
        refl
    ; su3Receipt =
        SU3.canonicalSU3ColourFrom3LanesFusionReceipt
    ; su3ExistingCandidateIsTrue =
        refl
    ; ewsbReceipt =
        EWSB.canonicalEWSBFromCSHiggsReceipt
    ; ewsbCandidateIsTrue =
        refl
    ; rows =
        canonicalGaugeGroupCandidateRows
    ; rowsAreCanonical =
        refl
    ; u1YCandidate =
        true
    ; u1YCandidateIsTrue =
        refl
    ; su2LCandidate =
        true
    ; su2LCandidateIsTrue =
        refl
    ; su3cCandidate =
        true
    ; su3cCandidateIsTrue =
        refl
    ; allGaugeFactorsCandidate =
        true
    ; allGaugeFactorsCandidateIsTrue =
        refl
    ; exactGaugeGroupStatus =
        exactPhysicalGaugeGroupOpen
    ; exactGaugeGroupStatusIsOpen =
        refl
    ; exactPhysicalGaugeGroup =
        false
    ; exactPhysicalGaugeGroupIsFalse =
        refl
    ; exactGDHRGaugeGroup =
        false
    ; exactGDHRGaugeGroupIsFalse =
        refl
    ; exactGDHREqualsGSM =
        false
    ; exactGDHREqualsGSMIsFalse =
        refl
    ; exactStandardModel =
        false
    ; exactStandardModelIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; receiptBoundary =
        "U1Y, SU2L, and SU3c are all recorded as candidate gauge factors"
        ∷ "The aggregate map is candidate-only and does not identify the exact physical gauge group"
        ∷ "G_DHR reconstruction, G_DHR ~= G_SM, exact Standard Model, and terminal promotions remain false"
        ∷ []
    }

smGaugeGroupU1YCandidateTrue :
  u1YCandidate canonicalSMGaugeGroupCandidateReceipt
  ≡
  true
smGaugeGroupU1YCandidateTrue =
  refl

smGaugeGroupSU2LCandidateTrue :
  su2LCandidate canonicalSMGaugeGroupCandidateReceipt
  ≡
  true
smGaugeGroupSU2LCandidateTrue =
  refl

smGaugeGroupSU3cCandidateTrue :
  su3cCandidate canonicalSMGaugeGroupCandidateReceipt
  ≡
  true
smGaugeGroupSU3cCandidateTrue =
  refl

smGaugeGroupExactPhysicalFalse :
  exactPhysicalGaugeGroup canonicalSMGaugeGroupCandidateReceipt
  ≡
  false
smGaugeGroupExactPhysicalFalse =
  refl

smGaugeGroupExactGDHRFalse :
  exactGDHRGaugeGroup canonicalSMGaugeGroupCandidateReceipt
  ≡
  false
smGaugeGroupExactGDHRFalse =
  refl

smGaugeGroupExactSMFalse :
  exactStandardModel canonicalSMGaugeGroupCandidateReceipt
  ≡
  false
smGaugeGroupExactSMFalse =
  refl

smGaugeGroupTerminalFalse :
  terminalPromotion canonicalSMGaugeGroupCandidateReceipt
  ≡
  false
smGaugeGroupTerminalFalse =
  refl

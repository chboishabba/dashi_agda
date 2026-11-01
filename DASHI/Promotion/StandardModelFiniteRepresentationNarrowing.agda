module DASHI.Promotion.StandardModelFiniteRepresentationNarrowing where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM
import DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger as PrimeLane
import DASHI.Physics.QFT.SMFermionCountReceipt as FermionCount
import DASHI.Physics.QFT.SMGaugeGroupCandidateReceipt as GaugeGroup
import DASHI.Physics.QFT.SMGaugeGroupFromCS3LanesReceipt as CS3
import DASHI.Physics.QFT.U1YFromConductorReceipt as U1Conductor
import DASHI.Promotion.Gate3StandardModelClayEvidenceReducer as Reducer
import DASHI.Promotion.StandardModelTerminalObligations as SMT

------------------------------------------------------------------------
-- Finite Standard Model representation narrowing.
--
-- This module records the strongest current SM-facing claim that remains
-- honest: finite gauge-name and p2/p3/p5 representation-content bookkeeping.
-- It explicitly does not promote a continuous Standard Model construction.

data NarrowGaugeName : Set where
  narrowU1Y :
    NarrowGaugeName

  narrowSU2L :
    NarrowGaugeName

  narrowSU3c :
    NarrowGaugeName

narrowGaugeNameLabel :
  NarrowGaugeName →
  String
narrowGaugeNameLabel narrowU1Y =
  "U1Y"
narrowGaugeNameLabel narrowSU2L =
  "SU2L"
narrowGaugeNameLabel narrowSU3c =
  "SU3c"

data NarrowPrimeSurface : Set where
  narrowP2Surface :
    NarrowPrimeSurface

  narrowP3Surface :
    NarrowPrimeSurface

  narrowP5Surface :
    NarrowPrimeSurface

narrowPrimeSurfaceLabel :
  NarrowPrimeSurface →
  String
narrowPrimeSurfaceLabel narrowP2Surface =
  "p2"
narrowPrimeSurfaceLabel narrowP3Surface =
  "p3"
narrowPrimeSurfaceLabel narrowP5Surface =
  "p5"

record FiniteGaugeNameRow : Set where
  field
    gaugeName :
      NarrowGaugeName

    primeSurface :
      NarrowPrimeSurface

    candidateFactor :
      GaugeGroup.SMGaugeFactor

    primeLaneGaugeFactor :
      PrimeLane.PrimeLaneSMGaugeFactor

    gaugeLabel :
      String

    gaugeLabelIsCanonical :
      gaugeLabel ≡ narrowGaugeNameLabel gaugeName

    primeLabel :
      String

    primeLabelIsCanonical :
      primeLabel ≡ narrowPrimeSurfaceLabel primeSurface

    finiteCandidateOnly :
      Bool

    finiteCandidateOnlyIsTrue :
      finiteCandidateOnly ≡ true

    exactPhysicalGaugeFactorPromoted :
      Bool

    exactPhysicalGaugeFactorPromotedIsFalse :
      exactPhysicalGaugeFactorPromoted ≡ false

    rowBoundary :
      String

open FiniteGaugeNameRow public

u1YP2FiniteGaugeNameRow :
  FiniteGaugeNameRow
u1YP2FiniteGaugeNameRow =
  record
    { gaugeName =
        narrowU1Y
    ; primeSurface =
        narrowP2Surface
    ; candidateFactor =
        GaugeGroup.U1YFactor
    ; primeLaneGaugeFactor =
        PrimeLane.U1Y
    ; gaugeLabel =
        "U1Y"
    ; gaugeLabelIsCanonical =
        refl
    ; primeLabel =
        "p2"
    ; primeLabelIsCanonical =
        refl
    ; finiteCandidateOnly =
        true
    ; finiteCandidateOnlyIsTrue =
        refl
    ; exactPhysicalGaugeFactorPromoted =
        false
    ; exactPhysicalGaugeFactorPromotedIsFalse =
        refl
    ; rowBoundary =
        "finite U1Y name row tied to p2; continuous hypercharge gauge group remains open"
    }

su2LP3FiniteGaugeNameRow :
  FiniteGaugeNameRow
su2LP3FiniteGaugeNameRow =
  record
    { gaugeName =
        narrowSU2L
    ; primeSurface =
        narrowP3Surface
    ; candidateFactor =
        GaugeGroup.SU2LFactor
    ; primeLaneGaugeFactor =
        PrimeLane.SU2L
    ; gaugeLabel =
        "SU2L"
    ; gaugeLabelIsCanonical =
        refl
    ; primeLabel =
        "p3"
    ; primeLabelIsCanonical =
        refl
    ; finiteCandidateOnly =
        true
    ; finiteCandidateOnlyIsTrue =
        refl
    ; exactPhysicalGaugeFactorPromoted =
        false
    ; exactPhysicalGaugeFactorPromotedIsFalse =
        refl
    ; rowBoundary =
        "finite SU2L name row tied to p3; exact weak-sector reconstruction remains open"
    }

su3cP5FiniteGaugeNameRow :
  FiniteGaugeNameRow
su3cP5FiniteGaugeNameRow =
  record
    { gaugeName =
        narrowSU3c
    ; primeSurface =
        narrowP5Surface
    ; candidateFactor =
        GaugeGroup.SU3cFactor
    ; primeLaneGaugeFactor =
        PrimeLane.SU3c
    ; gaugeLabel =
        "SU3c"
    ; gaugeLabelIsCanonical =
        refl
    ; primeLabel =
        "p5"
    ; primeLabelIsCanonical =
        refl
    ; finiteCandidateOnly =
        true
    ; finiteCandidateOnlyIsTrue =
        refl
    ; exactPhysicalGaugeFactorPromoted =
        false
    ; exactPhysicalGaugeFactorPromotedIsFalse =
        refl
    ; rowBoundary =
        "finite SU3c name row tied to p5; continuous colour gauge group remains open"
    }

canonicalFiniteGaugeNameRows :
  List FiniteGaugeNameRow
canonicalFiniteGaugeNameRows =
  u1YP2FiniteGaugeNameRow
  ∷ su2LP3FiniteGaugeNameRow
  ∷ su3cP5FiniteGaugeNameRow
  ∷ []

data OneGenerationRepresentationTarget : Set where
  quarkLeftDoubletTarget :
    OneGenerationRepresentationTarget

  upRightSingletTarget :
    OneGenerationRepresentationTarget

  downRightSingletTarget :
    OneGenerationRepresentationTarget

  leptonLeftDoubletTarget :
    OneGenerationRepresentationTarget

  electronRightSingletTarget :
    OneGenerationRepresentationTarget

oneGenerationTargetLabel :
  OneGenerationRepresentationTarget →
  String
oneGenerationTargetLabel quarkLeftDoubletTarget =
  "Q_L : (3,2) with Y=1/6"
oneGenerationTargetLabel upRightSingletTarget =
  "u_R : (3,1) with Y=2/3"
oneGenerationTargetLabel downRightSingletTarget =
  "d_R : (3,1) with Y=-1/3"
oneGenerationTargetLabel leptonLeftDoubletTarget =
  "L_L : (1,2) with Y=-1/2"
oneGenerationTargetLabel electronRightSingletTarget =
  "e_R : (1,1) with Y=-1"

data TargetCoverageStatus : Set where
  finiteHyperchargeRowAvailable :
    TargetCoverageStatus

  doubletPackedButMemberSplitOpen :
    TargetCoverageStatus

  missingFiniteHyperchargeRow :
    TargetCoverageStatus

record OneGenerationRepresentationRow : Set where
  field
    target :
      OneGenerationRepresentationTarget

    targetLabel :
      String

    targetLabelIsCanonical :
      targetLabel ≡ oneGenerationTargetLabel target

    colourDimension :
      Nat

    weakDimension :
      Nat

    hyperchargeConvention :
      String

    coverageStatus :
      TargetCoverageStatus

    finiteTargetOnly :
      Bool

    finiteTargetOnlyIsTrue :
      finiteTargetOnly ≡ true

    physicalRepresentationTheorem :
      Bool

    physicalRepresentationTheoremIsFalse :
      physicalRepresentationTheorem ≡ false

    targetBoundary :
      String

open OneGenerationRepresentationRow public

qLRepresentationTargetRow :
  OneGenerationRepresentationRow
qLRepresentationTargetRow =
  record
    { target =
        quarkLeftDoubletTarget
    ; targetLabel =
        "Q_L : (3,2) with Y=1/6"
    ; targetLabelIsCanonical =
        refl
    ; colourDimension =
        3
    ; weakDimension =
        2
    ; hyperchargeConvention =
        "Q = T3 + Y"
    ; coverageStatus =
        finiteHyperchargeRowAvailable
    ; finiteTargetOnly =
        true
    ; finiteTargetOnlyIsTrue =
        refl
    ; physicalRepresentationTheorem =
        false
    ; physicalRepresentationTheoremIsFalse =
        refl
    ; targetBoundary =
        "Q_L hypercharge is present as a signed-sixth Z6 row; the (3,2) physical representation theorem is not proved"
    }

uRRepresentationTargetRow :
  OneGenerationRepresentationRow
uRRepresentationTargetRow =
  record
    { target =
        upRightSingletTarget
    ; targetLabel =
        "u_R : (3,1) with Y=2/3"
    ; targetLabelIsCanonical =
        refl
    ; colourDimension =
        3
    ; weakDimension =
        1
    ; hyperchargeConvention =
        "Q = T3 + Y"
    ; coverageStatus =
        finiteHyperchargeRowAvailable
    ; finiteTargetOnly =
        true
    ; finiteTargetOnlyIsTrue =
        refl
    ; physicalRepresentationTheorem =
        false
    ; physicalRepresentationTheoremIsFalse =
        refl
    ; targetBoundary =
        "u_R hypercharge is present as a signed-sixth Z6 row; right-handed singlet reconstruction is not proved"
    }

dRRepresentationTargetRow :
  OneGenerationRepresentationRow
dRRepresentationTargetRow =
  record
    { target =
        downRightSingletTarget
    ; targetLabel =
        "d_R : (3,1) with Y=-1/3"
    ; targetLabelIsCanonical =
        refl
    ; colourDimension =
        3
    ; weakDimension =
        1
    ; hyperchargeConvention =
        "Q = T3 + Y"
    ; coverageStatus =
        finiteHyperchargeRowAvailable
    ; finiteTargetOnly =
        true
    ; finiteTargetOnlyIsTrue =
        refl
    ; physicalRepresentationTheorem =
        false
    ; physicalRepresentationTheoremIsFalse =
        refl
    ; targetBoundary =
        "d_R hypercharge is present as a signed-sixth Z6 row; right-handed singlet reconstruction is not proved"
    }

lLRepresentationTargetRow :
  OneGenerationRepresentationRow
lLRepresentationTargetRow =
  record
    { target =
        leptonLeftDoubletTarget
    ; targetLabel =
        "L_L : (1,2) with Y=-1/2"
    ; targetLabelIsCanonical =
        refl
    ; colourDimension =
        1
    ; weakDimension =
        2
    ; hyperchargeConvention =
        "Q = T3 + Y"
    ; coverageStatus =
        doubletPackedButMemberSplitOpen
    ; finiteTargetOnly =
        true
    ; finiteTargetOnlyIsTrue =
        refl
    ; physicalRepresentationTheorem =
        false
    ; physicalRepresentationTheoremIsFalse =
        refl
    ; targetBoundary =
        "e_L and nu_L are present as finite rows, but the lepton doublet representation and member split are not constructed"
    }

eRRepresentationTargetRow :
  OneGenerationRepresentationRow
eRRepresentationTargetRow =
  record
    { target =
        electronRightSingletTarget
    ; targetLabel =
        "e_R : (1,1) with Y=-1"
    ; targetLabelIsCanonical =
        refl
    ; colourDimension =
        1
    ; weakDimension =
        1
    ; hyperchargeConvention =
        "Q = T3 + Y"
    ; coverageStatus =
        missingFiniteHyperchargeRow
    ; finiteTargetOnly =
        true
    ; finiteTargetOnlyIsTrue =
        refl
    ; physicalRepresentationTheorem =
        false
    ; physicalRepresentationTheoremIsFalse =
        refl
    ; targetBoundary =
        "e_R is a one-generation target, but the current conductor receipt has no distinct e_R=-1 row"
    }

canonicalOneGenerationRepresentationRows :
  List OneGenerationRepresentationRow
canonicalOneGenerationRepresentationRows =
  qLRepresentationTargetRow
  ∷ uRRepresentationTargetRow
  ∷ dRRepresentationTargetRow
  ∷ lLRepresentationTargetRow
  ∷ eRRepresentationTargetRow
  ∷ []

data NarrowingBlocker : Set where
  continuousU1EmbeddingBlocker :
    NarrowingBlocker

  continuousSU2BridgeBlocker :
    NarrowingBlocker

  continuousSU3BridgeBlocker :
    NarrowingBlocker

  hyperchargeConventionBridgeBlocker :
    NarrowingBlocker

  pdgAuthorityBlocker :
    NarrowingBlocker

  empiricalObservableBridgeBlocker :
    NarrowingBlocker

  exactFermionCountBlocker :
    NarrowingBlocker

  broadStandardModelPromotionBlocker :
    NarrowingBlocker

canonicalContinuousBridgeBlockers :
  List NarrowingBlocker
canonicalContinuousBridgeBlockers =
  continuousU1EmbeddingBlocker
  ∷ continuousSU2BridgeBlocker
  ∷ continuousSU3BridgeBlocker
  ∷ hyperchargeConventionBridgeBlocker
  ∷ []

canonicalEmpiricalAuthorityBlockers :
  List NarrowingBlocker
canonicalEmpiricalAuthorityBlockers =
  pdgAuthorityBlocker
  ∷ empiricalObservableBridgeBlocker
  ∷ []

canonicalBroadPromotionBlockers :
  List NarrowingBlocker
canonicalBroadPromotionBlockers =
  exactFermionCountBlocker
  ∷ broadStandardModelPromotionBlocker
  ∷ []

listCount :
  {A : Set} →
  List A →
  Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

record StandardModelFiniteRepresentationNarrowingReceipt : Setω where
  field
    standardModelTerminalReceipt :
      SMT.StandardModelTerminalPromotionObligationReceipt

    gate3SMClayReducer :
      Reducer.Gate3StandardModelClayEvidenceReducer

    gaugeGroupCandidateReceipt :
      GaugeGroup.SMGaugeGroupCandidateReceipt

    gaugeGroupFromCS3LanesReceipt :
      CS3.SMGaugeGroupFromCS3LanesReceipt

    primeLaneCompatibilityReceipt :
      PrimeLane.FinitePrimeLaneDHRSMNaturalityReceipt

    primeLaneExactMatchBlockerReceipt :
      PrimeLane.PrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt

    u1YConductorReceipt :
      U1Conductor.U1YFromConductorReceipt

    fermionCountReceipt :
      FermionCount.SMFermionCountReceipt

    exactSMMatchBlockerReceipt :
      ExactSM.ExactSMMatchBlockerReceipt

    finiteGaugeNameRows :
      List FiniteGaugeNameRow

    finiteGaugeNameRowsAreCanonical :
      finiteGaugeNameRows ≡ canonicalFiniteGaugeNameRows

    finiteGaugeNameRowCount :
      Nat

    finiteGaugeNameRowCountIsThree :
      finiteGaugeNameRowCount ≡ 3

    primeSurfaceRowCount :
      Nat

    primeSurfaceRowCountIsThree :
      primeSurfaceRowCount ≡ 3

    oneGenerationRepresentationRows :
      List OneGenerationRepresentationRow

    oneGenerationRepresentationRowsAreCanonical :
      oneGenerationRepresentationRows
      ≡
      canonicalOneGenerationRepresentationRows

    oneGenerationRepresentationTargetCount :
      Nat

    oneGenerationRepresentationTargetCountIsFive :
      oneGenerationRepresentationTargetCount ≡ 5

    conductorHyperchargeAssignmentCount :
      Nat

    conductorHyperchargeAssignmentCountIsFive :
      conductorHyperchargeAssignmentCount ≡ 5

    hyperchargeConvention :
      String

    hyperchargeConventionIsCanonical :
      hyperchargeConvention ≡ "Q = T3 + Y"

    finiteHyperchargeConventionRecorded :
      Bool

    finiteHyperchargeConventionRecordedIsTrue :
      finiteHyperchargeConventionRecorded ≡ true

    continuousBridgeBlockers :
      List NarrowingBlocker

    continuousBridgeBlockersAreCanonical :
      continuousBridgeBlockers ≡ canonicalContinuousBridgeBlockers

    continuousBridgeBlockerCount :
      Nat

    continuousBridgeBlockerCountIsFour :
      continuousBridgeBlockerCount ≡ 4

    empiricalAuthorityBlockers :
      List NarrowingBlocker

    empiricalAuthorityBlockersAreCanonical :
      empiricalAuthorityBlockers ≡ canonicalEmpiricalAuthorityBlockers

    empiricalAuthorityBlockerCount :
      Nat

    empiricalAuthorityBlockerCountIsTwo :
      empiricalAuthorityBlockerCount ≡ 2

    broadPromotionBlockers :
      List NarrowingBlocker

    broadPromotionBlockersAreCanonical :
      broadPromotionBlockers ≡ canonicalBroadPromotionBlockers

    broadPromotionBlockerCount :
      Nat

    broadPromotionBlockerCountIsTwo :
      broadPromotionBlockerCount ≡ 2

    totalNarrowingBlockerCount :
      Nat

    totalNarrowingBlockerCountIsEight :
      totalNarrowingBlockerCount ≡ 8

    finiteRepresentationContentNarrowed :
      Bool

    finiteRepresentationContentNarrowedIsTrue :
      finiteRepresentationContentNarrowed ≡ true

    exactPhysicalRepresentationContentPromoted :
      Bool

    exactPhysicalRepresentationContentPromotedIsFalse :
      exactPhysicalRepresentationContentPromoted ≡ false

    broadStandardModelPromoted :
      Bool

    broadStandardModelPromotedIsFalse :
      broadStandardModelPromoted ≡ false

    falseBroadStandardModelPromotion :
      Bool

    falseBroadStandardModelPromotionIsFalse :
      falseBroadStandardModelPromotion ≡ false

    narrowingBoundary :
      List String

open StandardModelFiniteRepresentationNarrowingReceipt public

canonicalStandardModelFiniteRepresentationNarrowingReceipt :
  StandardModelFiniteRepresentationNarrowingReceipt
canonicalStandardModelFiniteRepresentationNarrowingReceipt =
  record
    { standardModelTerminalReceipt =
        SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; gate3SMClayReducer =
        Reducer.canonicalGate3StandardModelClayEvidenceReducer
    ; gaugeGroupCandidateReceipt =
        GaugeGroup.canonicalSMGaugeGroupCandidateReceipt
    ; gaugeGroupFromCS3LanesReceipt =
        CS3.canonicalSMGaugeGroupFromCS3LanesReceipt
    ; primeLaneCompatibilityReceipt =
        PrimeLane.canonicalFinitePrimeLaneDHRSMNaturalityReceipt
    ; primeLaneExactMatchBlockerReceipt =
        PrimeLane.canonicalPrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt
    ; u1YConductorReceipt =
        U1Conductor.canonicalU1YFromConductorReceipt
    ; fermionCountReceipt =
        FermionCount.canonicalSMFermionCountReceipt
    ; exactSMMatchBlockerReceipt =
        ExactSM.canonicalExactSMMatchBlockerReceipt
    ; finiteGaugeNameRows =
        canonicalFiniteGaugeNameRows
    ; finiteGaugeNameRowsAreCanonical =
        refl
    ; finiteGaugeNameRowCount =
        listCount canonicalFiniteGaugeNameRows
    ; finiteGaugeNameRowCountIsThree =
        refl
    ; primeSurfaceRowCount =
        listCount canonicalFiniteGaugeNameRows
    ; primeSurfaceRowCountIsThree =
        refl
    ; oneGenerationRepresentationRows =
        canonicalOneGenerationRepresentationRows
    ; oneGenerationRepresentationRowsAreCanonical =
        refl
    ; oneGenerationRepresentationTargetCount =
        listCount canonicalOneGenerationRepresentationRows
    ; oneGenerationRepresentationTargetCountIsFive =
        refl
    ; conductorHyperchargeAssignmentCount =
        listCount U1Conductor.canonicalHyperchargeZ6CharacterAssignments
    ; conductorHyperchargeAssignmentCountIsFive =
        refl
    ; hyperchargeConvention =
        "Q = T3 + Y"
    ; hyperchargeConventionIsCanonical =
        refl
    ; finiteHyperchargeConventionRecorded =
        true
    ; finiteHyperchargeConventionRecordedIsTrue =
        refl
    ; continuousBridgeBlockers =
        canonicalContinuousBridgeBlockers
    ; continuousBridgeBlockersAreCanonical =
        refl
    ; continuousBridgeBlockerCount =
        listCount canonicalContinuousBridgeBlockers
    ; continuousBridgeBlockerCountIsFour =
        refl
    ; empiricalAuthorityBlockers =
        canonicalEmpiricalAuthorityBlockers
    ; empiricalAuthorityBlockersAreCanonical =
        refl
    ; empiricalAuthorityBlockerCount =
        listCount canonicalEmpiricalAuthorityBlockers
    ; empiricalAuthorityBlockerCountIsTwo =
        refl
    ; broadPromotionBlockers =
        canonicalBroadPromotionBlockers
    ; broadPromotionBlockersAreCanonical =
        refl
    ; broadPromotionBlockerCount =
        listCount canonicalBroadPromotionBlockers
    ; broadPromotionBlockerCountIsTwo =
        refl
    ; totalNarrowingBlockerCount =
        8
    ; totalNarrowingBlockerCountIsEight =
        refl
    ; finiteRepresentationContentNarrowed =
        true
    ; finiteRepresentationContentNarrowedIsTrue =
        refl
    ; exactPhysicalRepresentationContentPromoted =
        false
    ; exactPhysicalRepresentationContentPromotedIsFalse =
        refl
    ; broadStandardModelPromoted =
        false
    ; broadStandardModelPromotedIsFalse =
        refl
    ; falseBroadStandardModelPromotion =
        false
    ; falseBroadStandardModelPromotionIsFalse =
        refl
    ; narrowingBoundary =
        "Narrowed claim: finite U1Y/SU2L/SU3c name rows and p2/p3/p5 surface rows are recorded"
        ∷ "One-generation representation targets are listed as finite targets only, with five target rows"
        ∷ "The conductor receipt supplies five signed-sixth hypercharge rows under Q = T3 + Y"
        ∷ "Continuous U1/SU2/SU3 bridges, PDG/empirical authority, and exact fermion-count promotion remain blocked"
        ∷ "Broad Standard Model promotion and false broad promotion are both false"
        ∷ []
    }

finiteGaugeNameMappingCountIsThree :
  finiteGaugeNameRowCount
    canonicalStandardModelFiniteRepresentationNarrowingReceipt
  ≡
  3
finiteGaugeNameMappingCountIsThree =
  refl

oneGenerationTargetCountIsFive :
  oneGenerationRepresentationTargetCount
    canonicalStandardModelFiniteRepresentationNarrowingReceipt
  ≡
  5
oneGenerationTargetCountIsFive =
  refl

standardModelFiniteRepresentationNarrowingIsNotBroadSMPromotion :
  broadStandardModelPromoted
    canonicalStandardModelFiniteRepresentationNarrowingReceipt
  ≡
  false
standardModelFiniteRepresentationNarrowingIsNotBroadSMPromotion =
  refl

standardModelFiniteRepresentationNarrowingFalseBroadPromotionBlocked :
  falseBroadStandardModelPromotion
    canonicalStandardModelFiniteRepresentationNarrowingReceipt
  ≡
  false
standardModelFiniteRepresentationNarrowingFalseBroadPromotionBlocked =
  refl

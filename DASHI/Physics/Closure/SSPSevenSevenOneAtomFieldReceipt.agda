module DASHI.Physics.Closure.SSPSevenSevenOneAtomFieldReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import MonsterOntos using
  ( SSP
  ; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31
  ; p41; p47; p59; p71
  )

------------------------------------------------------------------------
-- 15SSP as 7 + 7 + 1 atom-field receipt.
--
-- This receipt records an interpretation surface only:
-- two mirrored seven-lane Hecke/transport septets carry the paired
-- geometric transport coordinates, while the remaining SSP lane is reserved
-- as the spare/sign/time-reaction control label.  The sign label is recorded
-- as a ternary xor-like reaction-direction/time-label candidate, not as a
-- theorem and not as a promoted physics claim.

data SSPSevenSevenOneStatus : Set where
  sspSevenSevenOneAtomFieldInterpretationRecorded :
    SSPSevenSevenOneStatus

data MirrorSide : Set where
  leftMirrorSide :
    MirrorSide

  rightMirrorSide :
    MirrorSide

data TransportCoordinate : Set where
  positionCoordinate :
    TransportCoordinate

  scaleCoordinate :
    TransportCoordinate

  amplitudeCoordinate :
    TransportCoordinate

  orientationCoordinate :
    TransportCoordinate

  anisotropyCoordinate :
    TransportCoordinate

  phaseCoordinate :
    TransportCoordinate

  twistCoordinate :
    TransportCoordinate

data AtomField : Set where
  positionField :
    AtomField

  scaleField :
    AtomField

  amplitudeField :
    AtomField

  orientationField :
    AtomField

  anisotropyField :
    AtomField

  phaseField :
    AtomField

  twistField :
    AtomField

  signField :
    AtomField

canonicalAtomFields :
  List AtomField
canonicalAtomFields =
  positionField
  ∷ scaleField
  ∷ amplitudeField
  ∷ orientationField
  ∷ anisotropyField
  ∷ phaseField
  ∷ twistField
  ∷ signField
  ∷ []

canonicalTransportCoordinates :
  List TransportCoordinate
canonicalTransportCoordinates =
  positionCoordinate
  ∷ scaleCoordinate
  ∷ amplitudeCoordinate
  ∷ orientationCoordinate
  ∷ anisotropyCoordinate
  ∷ phaseCoordinate
  ∷ twistCoordinate
  ∷ []

data ReactionDirection : Set where
  reactionNegative :
    ReactionDirection

  reactionNeutral :
    ReactionDirection

  reactionPositive :
    ReactionDirection

data SignControlLabelRole : Set where
  ternaryXorLikeReactionDirectionTimeLabelCandidate :
    SignControlLabelRole

data AtomFieldCountReading : Set where
  eightFieldsWithSignSeparatedAsControl :
    AtomFieldCountReading

data SSPPartitionReading : Set where
  fifteenAsSevenPlusSevenPlusOne :
    SSPPartitionReading

data FifteenVariableInterpretationReading : Set where
  fifteenVariablesAsAmplitudePositionPhaseDynamicSignTime :
    FifteenVariableInterpretationReading

data SeptetVariableRole : Set where
  amplitudePositionMirrorVariable :
    SeptetVariableRole

  phaseDynamicMirrorVariable :
    SeptetVariableRole

  signTimeLaneVariable :
    SeptetVariableRole

data LanePairingReading : Set where
  pairedHeckeTransportCoordinatesAcrossMirrors :
    LanePairingReading

data SeptetMirrorReading : Set where
  twoMirroredHeckeSeptetsRecorded :
    SeptetMirrorReading

data SpareLaneReading : Set where
  spareLaneIsSignTimeXorControlCandidate :
    SpareLaneReading

data HeckeMirrorSelfDualReading : Set where
  heckeMirrorSelfDualCandidateBookkeepingOnly :
    HeckeMirrorSelfDualReading

record MirroredTransportLane : Set where
  field
    coordinate :
      TransportCoordinate

    leftLane :
      SSP

    rightLane :
      SSP

    sidePair :
      MirrorSide × MirrorSide

open MirroredTransportLane public

positionLanePair : MirroredTransportLane
positionLanePair =
  record
    { coordinate = positionCoordinate
    ; leftLane = p2
    ; rightLane = p19
    ; sidePair = leftMirrorSide , rightMirrorSide
    }

scaleLanePair : MirroredTransportLane
scaleLanePair =
  record
    { coordinate = scaleCoordinate
    ; leftLane = p3
    ; rightLane = p23
    ; sidePair = leftMirrorSide , rightMirrorSide
    }

amplitudeLanePair : MirroredTransportLane
amplitudeLanePair =
  record
    { coordinate = amplitudeCoordinate
    ; leftLane = p5
    ; rightLane = p29
    ; sidePair = leftMirrorSide , rightMirrorSide
    }

orientationLanePair : MirroredTransportLane
orientationLanePair =
  record
    { coordinate = orientationCoordinate
    ; leftLane = p7
    ; rightLane = p31
    ; sidePair = leftMirrorSide , rightMirrorSide
    }

anisotropyLanePair : MirroredTransportLane
anisotropyLanePair =
  record
    { coordinate = anisotropyCoordinate
    ; leftLane = p11
    ; rightLane = p41
    ; sidePair = leftMirrorSide , rightMirrorSide
    }

phaseLanePair : MirroredTransportLane
phaseLanePair =
  record
    { coordinate = phaseCoordinate
    ; leftLane = p13
    ; rightLane = p47
    ; sidePair = leftMirrorSide , rightMirrorSide
    }

twistLanePair : MirroredTransportLane
twistLanePair =
  record
    { coordinate = twistCoordinate
    ; leftLane = p17
    ; rightLane = p59
    ; sidePair = leftMirrorSide , rightMirrorSide
    }

canonicalLeftHeckeSeptet :
  List SSP
canonicalLeftHeckeSeptet =
  p2 ∷ p3 ∷ p5 ∷ p7 ∷ p11 ∷ p13 ∷ p17 ∷ []

canonicalRightHeckeSeptet :
  List SSP
canonicalRightHeckeSeptet =
  p19 ∷ p23 ∷ p29 ∷ p31 ∷ p41 ∷ p47 ∷ p59 ∷ []

canonicalSpareSignTimeReactionLane :
  SSP
canonicalSpareSignTimeReactionLane =
  p71

canonicalAmplitudePositionMirrorSeptet :
  List SSP
canonicalAmplitudePositionMirrorSeptet =
  canonicalLeftHeckeSeptet

canonicalPhaseDynamicMirrorSeptet :
  List SSP
canonicalPhaseDynamicMirrorSeptet =
  canonicalRightHeckeSeptet

canonicalMirroredTransportLanePairs :
  List MirroredTransportLane
canonicalMirroredTransportLanePairs =
  positionLanePair
  ∷ scaleLanePair
  ∷ amplitudeLanePair
  ∷ orientationLanePair
  ∷ anisotropyLanePair
  ∷ phaseLanePair
  ∷ twistLanePair
  ∷ []

data SSPSevenSevenOnePromotion : Set where

sspSevenSevenOnePromotionImpossibleHere :
  SSPSevenSevenOnePromotion →
  ⊥
sspSevenSevenOnePromotionImpossibleHere ()

data SSPSevenSevenOneNonClaim : Set where
  noSignReactionTheorem :
    SSPSevenSevenOneNonClaim

  noTimeDirectionTheorem :
    SSPSevenSevenOneNonClaim

  noXorDynamicsTheorem :
    SSPSevenSevenOneNonClaim

  noHeckeTransportEquivalenceTheorem :
    SSPSevenSevenOneNonClaim

  noHeckeMirrorTheorem :
    SSPSevenSevenOneNonClaim

  noSelfDualityTheorem :
    SSPSevenSevenOneNonClaim

  noContinuumPhysicsPromotion :
    SSPSevenSevenOneNonClaim

  noClayPromotion :
    SSPSevenSevenOneNonClaim

canonicalNonClaims :
  List SSPSevenSevenOneNonClaim
canonicalNonClaims =
  noSignReactionTheorem
  ∷ noTimeDirectionTheorem
  ∷ noXorDynamicsTheorem
  ∷ noHeckeTransportEquivalenceTheorem
  ∷ noHeckeMirrorTheorem
  ∷ noSelfDualityTheorem
  ∷ noContinuumPhysicsPromotion
  ∷ noClayPromotion
  ∷ []

sevenSevenOneSummary :
  String
sevenSevenOneSummary =
  "15SSP is recorded as 7+7+1: mirrored Hecke/transport septets plus one spare sign/time-reaction control label."

atomFieldSummary :
  String
atomFieldSummary =
  "The eight atom fields are position, scale, amplitude, orientation, anisotropy, phase, twist, and sign; sign is separated as the +1 control label."

signCandidateSummary :
  String
signCandidateSummary =
  "The sign lane is only a ternary xor-like reaction-direction/time-label candidate, not a theorem."

septetMirrorSummary :
  String
septetMirrorSummary =
  "The two seven-lane SSP blocks are recorded as mirrored Hecke septets only, paired coordinate-by-coordinate."

spareLaneSummary :
  String
spareLaneSummary =
  "The remaining p71 lane is recorded as a sign/time/XOR spare-control candidate only."

fifteenVariableSummary :
  String
fifteenVariableSummary =
  "The newer 15-variable reading is first septet amplitude/position mirror, second septet phase/dynamic mirror, and p71 sign/time lane."

earlierSevenCoordinateBoundarySummary :
  String
earlierSevenCoordinateBoundarySummary =
  "The older seven transport-coordinate reading remains as paired coordinate bookkeeping and is not identified with the newer 15-variable reading."

heckeMirrorSelfDualSummary :
  String
heckeMirrorSelfDualSummary =
  "Hecke mirror and self-dual language is recorded only as candidate bookkeeping unless a local theorem is supplied."

record SSPSevenSevenOneAtomFieldReceipt : Set where
  field
    status :
      SSPSevenSevenOneStatus

    statusIsCanonical :
      status ≡ sspSevenSevenOneAtomFieldInterpretationRecorded

    sspPartitionReading :
      SSPPartitionReading

    sspPartitionReadingIsSevenSevenOne :
      sspPartitionReading ≡ fifteenAsSevenPlusSevenPlusOne

    fifteenVariableInterpretation :
      FifteenVariableInterpretationReading

    fifteenVariableInterpretationIsCanonical :
      fifteenVariableInterpretation
      ≡
      fifteenVariablesAsAmplitudePositionPhaseDynamicSignTime

    totalSSPLaneCount :
      Nat

    totalSSPLaneCountIsFifteen :
      totalSSPLaneCount ≡ 15

    leftHeckeSeptet :
      List SSP

    leftHeckeSeptetIsCanonical :
      leftHeckeSeptet ≡ canonicalLeftHeckeSeptet

    leftHeckeSeptetCount :
      Nat

    leftHeckeSeptetCountIsSeven :
      leftHeckeSeptetCount ≡ 7

    firstSevenVariableRole :
      SeptetVariableRole

    firstSevenVariableRoleIsAmplitudePositionMirror :
      firstSevenVariableRole ≡ amplitudePositionMirrorVariable

    amplitudePositionMirrorSeptet :
      List SSP

    amplitudePositionMirrorSeptetIsCanonical :
      amplitudePositionMirrorSeptet ≡ canonicalAmplitudePositionMirrorSeptet

    rightHeckeSeptet :
      List SSP

    rightHeckeSeptetIsCanonical :
      rightHeckeSeptet ≡ canonicalRightHeckeSeptet

    rightHeckeSeptetCount :
      Nat

    rightHeckeSeptetCountIsSeven :
      rightHeckeSeptetCount ≡ 7

    secondSevenVariableRole :
      SeptetVariableRole

    secondSevenVariableRoleIsPhaseDynamicMirror :
      secondSevenVariableRole ≡ phaseDynamicMirrorVariable

    phaseDynamicMirrorSeptet :
      List SSP

    phaseDynamicMirrorSeptetIsCanonical :
      phaseDynamicMirrorSeptet ≡ canonicalPhaseDynamicMirrorSeptet

    spareSignTimeReactionLane :
      SSP

    spareSignTimeReactionLaneIsCanonical :
      spareSignTimeReactionLane ≡ canonicalSpareSignTimeReactionLane

    spareLaneCount :
      Nat

    spareLaneCountIsOne :
      spareLaneCount ≡ 1

    signTimeLaneRole :
      SeptetVariableRole

    signTimeLaneRoleIsSignTime :
      signTimeLaneRole ≡ signTimeLaneVariable

    atomFieldCountReading :
      AtomFieldCountReading

    atomFieldCountReadingIsCanonical :
      atomFieldCountReading ≡ eightFieldsWithSignSeparatedAsControl

    atomFields :
      List AtomField

    atomFieldsAreCanonical :
      atomFields ≡ canonicalAtomFields

    atomFieldCount :
      Nat

    atomFieldCountIsEight :
      atomFieldCount ≡ 8

    mirroredTransportCoordinates :
      List TransportCoordinate

    mirroredTransportCoordinatesAreCanonical :
      mirroredTransportCoordinates ≡ canonicalTransportCoordinates

    mirroredTransportCoordinateCount :
      Nat

    mirroredTransportCoordinateCountIsSeven :
      mirroredTransportCoordinateCount ≡ 7

    lanePairingReading :
      LanePairingReading

    lanePairingReadingIsPaired :
      lanePairingReading ≡ pairedHeckeTransportCoordinatesAcrossMirrors

    septetMirrorReading :
      SeptetMirrorReading

    septetMirrorReadingIsCanonical :
      septetMirrorReading ≡ twoMirroredHeckeSeptetsRecorded

    heckeMirrorSelfDualReading :
      HeckeMirrorSelfDualReading

    heckeMirrorSelfDualReadingIsCandidate :
      heckeMirrorSelfDualReading
      ≡
      heckeMirrorSelfDualCandidateBookkeepingOnly

    mirroredLanePairs :
      List MirroredTransportLane

    mirroredLanePairsAreCanonical :
      mirroredLanePairs ≡ canonicalMirroredTransportLanePairs

    spareLaneReading :
      SpareLaneReading

    spareLaneReadingIsSignTimeXor :
      spareLaneReading ≡ spareLaneIsSignTimeXorControlCandidate

    signControlRole :
      SignControlLabelRole

    signControlRoleIsCandidate :
      signControlRole
      ≡
      ternaryXorLikeReactionDirectionTimeLabelCandidate

    candidateReactionDirections :
      List ReactionDirection

    candidateReactionDirectionsAreTernary :
      candidateReactionDirections
      ≡
      reactionNegative ∷ reactionNeutral ∷ reactionPositive ∷ []

    signReactionTheoremProved :
      Bool

    signReactionTheoremProvedIsFalse :
      signReactionTheoremProved ≡ false

    timeDirectionTheoremProved :
      Bool

    timeDirectionTheoremProvedIsFalse :
      timeDirectionTheoremProved ≡ false

    xorDynamicsTheoremProved :
      Bool

    xorDynamicsTheoremProvedIsFalse :
      xorDynamicsTheoremProved ≡ false

    heckeTransportEquivalencePromoted :
      Bool

    heckeTransportEquivalencePromotedIsFalse :
      heckeTransportEquivalencePromoted ≡ false

    heckeMirrorTheoremProved :
      Bool

    heckeMirrorTheoremProvedIsFalse :
      heckeMirrorTheoremProved ≡ false

    selfDualityTheoremProved :
      Bool

    selfDualityTheoremProvedIsFalse :
      selfDualityTheoremProved ≡ false

    physicsPromotionConstructed :
      Bool

    physicsPromotionConstructedIsFalse :
      physicsPromotionConstructed ≡ false

    promotionFlags :
      List SSPSevenSevenOnePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    nonClaims :
      List SSPSevenSevenOneNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalNonClaims

    sevenSevenOneReading :
      String

    sevenSevenOneReadingIsCanonical :
      sevenSevenOneReading ≡ sevenSevenOneSummary

    atomFieldReading :
      String

    atomFieldReadingIsCanonical :
      atomFieldReading ≡ atomFieldSummary

    signCandidateReading :
      String

    signCandidateReadingIsCanonical :
      signCandidateReading ≡ signCandidateSummary

    septetMirrorReadingText :
      String

    septetMirrorReadingTextIsCanonical :
      septetMirrorReadingText ≡ septetMirrorSummary

    spareLaneReadingText :
      String

    spareLaneReadingTextIsCanonical :
      spareLaneReadingText ≡ spareLaneSummary

    fifteenVariableReading :
      String

    fifteenVariableReadingIsCanonical :
      fifteenVariableReading ≡ fifteenVariableSummary

    earlierSevenCoordinateBoundaryReading :
      String

    earlierSevenCoordinateBoundaryReadingIsCanonical :
      earlierSevenCoordinateBoundaryReading
      ≡
      earlierSevenCoordinateBoundarySummary

    heckeMirrorSelfDualReadingText :
      String

    heckeMirrorSelfDualReadingTextIsCanonical :
      heckeMirrorSelfDualReadingText ≡ heckeMirrorSelfDualSummary

    receiptBoundary :
      List String

open SSPSevenSevenOneAtomFieldReceipt public

canonicalSSPSevenSevenOneAtomFieldReceipt :
  SSPSevenSevenOneAtomFieldReceipt
canonicalSSPSevenSevenOneAtomFieldReceipt =
  record
    { status =
        sspSevenSevenOneAtomFieldInterpretationRecorded
    ; statusIsCanonical =
        refl
    ; sspPartitionReading =
        fifteenAsSevenPlusSevenPlusOne
    ; sspPartitionReadingIsSevenSevenOne =
        refl
    ; fifteenVariableInterpretation =
        fifteenVariablesAsAmplitudePositionPhaseDynamicSignTime
    ; fifteenVariableInterpretationIsCanonical =
        refl
    ; totalSSPLaneCount =
        15
    ; totalSSPLaneCountIsFifteen =
        refl
    ; leftHeckeSeptet =
        canonicalLeftHeckeSeptet
    ; leftHeckeSeptetIsCanonical =
        refl
    ; leftHeckeSeptetCount =
        7
    ; leftHeckeSeptetCountIsSeven =
        refl
    ; firstSevenVariableRole =
        amplitudePositionMirrorVariable
    ; firstSevenVariableRoleIsAmplitudePositionMirror =
        refl
    ; amplitudePositionMirrorSeptet =
        canonicalAmplitudePositionMirrorSeptet
    ; amplitudePositionMirrorSeptetIsCanonical =
        refl
    ; rightHeckeSeptet =
        canonicalRightHeckeSeptet
    ; rightHeckeSeptetIsCanonical =
        refl
    ; rightHeckeSeptetCount =
        7
    ; rightHeckeSeptetCountIsSeven =
        refl
    ; secondSevenVariableRole =
        phaseDynamicMirrorVariable
    ; secondSevenVariableRoleIsPhaseDynamicMirror =
        refl
    ; phaseDynamicMirrorSeptet =
        canonicalPhaseDynamicMirrorSeptet
    ; phaseDynamicMirrorSeptetIsCanonical =
        refl
    ; spareSignTimeReactionLane =
        canonicalSpareSignTimeReactionLane
    ; spareSignTimeReactionLaneIsCanonical =
        refl
    ; spareLaneCount =
        1
    ; spareLaneCountIsOne =
        refl
    ; signTimeLaneRole =
        signTimeLaneVariable
    ; signTimeLaneRoleIsSignTime =
        refl
    ; atomFieldCountReading =
        eightFieldsWithSignSeparatedAsControl
    ; atomFieldCountReadingIsCanonical =
        refl
    ; atomFields =
        canonicalAtomFields
    ; atomFieldsAreCanonical =
        refl
    ; atomFieldCount =
        8
    ; atomFieldCountIsEight =
        refl
    ; mirroredTransportCoordinates =
        canonicalTransportCoordinates
    ; mirroredTransportCoordinatesAreCanonical =
        refl
    ; mirroredTransportCoordinateCount =
        7
    ; mirroredTransportCoordinateCountIsSeven =
        refl
    ; lanePairingReading =
        pairedHeckeTransportCoordinatesAcrossMirrors
    ; lanePairingReadingIsPaired =
        refl
    ; septetMirrorReading =
        twoMirroredHeckeSeptetsRecorded
    ; septetMirrorReadingIsCanonical =
        refl
    ; heckeMirrorSelfDualReading =
        heckeMirrorSelfDualCandidateBookkeepingOnly
    ; heckeMirrorSelfDualReadingIsCandidate =
        refl
    ; mirroredLanePairs =
        canonicalMirroredTransportLanePairs
    ; mirroredLanePairsAreCanonical =
        refl
    ; spareLaneReading =
        spareLaneIsSignTimeXorControlCandidate
    ; spareLaneReadingIsSignTimeXor =
        refl
    ; signControlRole =
        ternaryXorLikeReactionDirectionTimeLabelCandidate
    ; signControlRoleIsCandidate =
        refl
    ; candidateReactionDirections =
        reactionNegative ∷ reactionNeutral ∷ reactionPositive ∷ []
    ; candidateReactionDirectionsAreTernary =
        refl
    ; signReactionTheoremProved =
        false
    ; signReactionTheoremProvedIsFalse =
        refl
    ; timeDirectionTheoremProved =
        false
    ; timeDirectionTheoremProvedIsFalse =
        refl
    ; xorDynamicsTheoremProved =
        false
    ; xorDynamicsTheoremProvedIsFalse =
        refl
    ; heckeTransportEquivalencePromoted =
        false
    ; heckeTransportEquivalencePromotedIsFalse =
        refl
    ; heckeMirrorTheoremProved =
        false
    ; heckeMirrorTheoremProvedIsFalse =
        refl
    ; selfDualityTheoremProved =
        false
    ; selfDualityTheoremProvedIsFalse =
        refl
    ; physicsPromotionConstructed =
        false
    ; physicsPromotionConstructedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; nonClaims =
        canonicalNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; sevenSevenOneReading =
        sevenSevenOneSummary
    ; sevenSevenOneReadingIsCanonical =
        refl
    ; atomFieldReading =
        atomFieldSummary
    ; atomFieldReadingIsCanonical =
        refl
    ; signCandidateReading =
        signCandidateSummary
    ; signCandidateReadingIsCanonical =
        refl
    ; septetMirrorReadingText =
        septetMirrorSummary
    ; septetMirrorReadingTextIsCanonical =
        refl
    ; spareLaneReadingText =
        spareLaneSummary
    ; spareLaneReadingTextIsCanonical =
        refl
    ; fifteenVariableReading =
        fifteenVariableSummary
    ; fifteenVariableReadingIsCanonical =
        refl
    ; earlierSevenCoordinateBoundaryReading =
        earlierSevenCoordinateBoundarySummary
    ; earlierSevenCoordinateBoundaryReadingIsCanonical =
        refl
    ; heckeMirrorSelfDualReadingText =
        heckeMirrorSelfDualSummary
    ; heckeMirrorSelfDualReadingTextIsCanonical =
        refl
    ; receiptBoundary =
        "Records 15SSP as 7+7+1 with two mirrored Hecke septets and p71 as spare control"
        ∷ "The left septet is p2,p3,p5,p7,p11,p13,p17 and the right septet is p19,p23,p29,p31,p41,p47,p59"
        ∷ "The newer 15-variable interpretation reads the first septet as amplitude/position mirror variables"
        ∷ "The newer 15-variable interpretation reads the second septet as phase/dynamic mirror variables"
        ∷ "The p71 spare is the sign/time lane, with XOR/reaction language kept candidate-only"
        ∷ "Pairs the seven mirrored lanes with position, scale, amplitude, orientation, anisotropy, phase, and twist"
        ∷ "The earlier seven transport-coordinate reading remains separate bookkeeping and is not upgraded into the 15-variable claim"
        ∷ "Separates sign/time/XOR control from the seven transport coordinates as the +1 spare label at p71"
        ∷ "Records sign as a ternary xor-like reaction-direction/time-label candidate only"
        ∷ "Hecke mirror and self-dual claims remain candidate bookkeeping; no local theorem is supplied here"
        ∷ "This is atom-field bookkeeping over the SSP carrier, not a physical field theorem"
        ∷ "Keeps sign reaction, time direction, xor dynamics, Hecke mirror, self-duality, Hecke-transport equivalence, and physics promotions false"
        ∷ []
    }

canonicalSSPSevenSevenOneKeepsPromotionsFalse :
  physicsPromotionConstructed canonicalSSPSevenSevenOneAtomFieldReceipt
  ≡
  false
canonicalSSPSevenSevenOneKeepsPromotionsFalse =
  refl

canonicalSSPSevenSevenOneHasNoPromotionFlags :
  promotionFlags canonicalSSPSevenSevenOneAtomFieldReceipt ≡ []
canonicalSSPSevenSevenOneHasNoPromotionFlags =
  refl

canonicalSSPSevenSevenOneSignIsOnlyCandidate :
  signReactionTheoremProved canonicalSSPSevenSevenOneAtomFieldReceipt
  ≡
  false
canonicalSSPSevenSevenOneSignIsOnlyCandidate =
  refl

module DASHI.Physics.QFT.U1YFromConductorReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.FiniteDHRAbelianReconstructionReceipt as FiniteDHR
import DASHI.Physics.QFT.FinitePrimeLaneTensorFusionReceipts as Fusion

------------------------------------------------------------------------
-- U(1)_Y from conductor receipt.
--
-- This receipt records the finite p3-lane CM-unit-character bookkeeping:
-- the p3 lane contributes Z/6 characters, so the displayed hypercharge
-- labels are recorded as signed multiples of 1/6 with a Z/6 representative.
-- It is only a candidate receipt.  It does not construct the continuous
-- U(1)_Y embedding and does not promote an exact Standard Model match.

data U1YFromP3LaneCMUnitStatus : Set where
  candidate :
    U1YFromP3LaneCMUnitStatus

data HyperchargeParticleLabel : Set where
  Q-L :
    HyperchargeParticleLabel

  u-R :
    HyperchargeParticleLabel

  d-R :
    HyperchargeParticleLabel

  e-L :
    HyperchargeParticleLabel

  nu-L :
    HyperchargeParticleLabel

data SignedSixthMultiple : Set where
  plusOneSixth :
    SignedSixthMultiple

  plusFourSixths :
    SignedSixthMultiple

  minusTwoSixths :
    SignedSixthMultiple

  minusThreeSixths :
    SignedSixthMultiple

signedSixthMultipleToZ6Character :
  SignedSixthMultiple →
  FiniteDHR.Z6Character
signedSixthMultipleToZ6Character plusOneSixth =
  FiniteDHR.z6-1
signedSixthMultipleToZ6Character plusFourSixths =
  FiniteDHR.z6-4
signedSixthMultipleToZ6Character minusTwoSixths =
  FiniteDHR.z6-4
signedSixthMultipleToZ6Character minusThreeSixths =
  FiniteDHR.z6-3

signedSixthMultipleLabel :
  SignedSixthMultiple →
  String
signedSixthMultipleLabel plusOneSixth =
  "1/6"
signedSixthMultipleLabel plusFourSixths =
  "4/6=2/3"
signedSixthMultipleLabel minusTwoSixths =
  "-2/6=-1/3"
signedSixthMultipleLabel minusThreeSixths =
  "-3/6=-1/2"

record HyperchargeZ6CharacterAssignment : Set where
  field
    particle :
      HyperchargeParticleLabel

    hyperchargeAsSignedSixths :
      SignedSixthMultiple

    z6CharacterRepresentative :
      FiniteDHR.Z6Character

    z6CharacterRepresentativeIsSignedSixth :
      z6CharacterRepresentative
      ≡
      signedSixthMultipleToZ6Character hyperchargeAsSignedSixths

    displayLabel :
      String

open HyperchargeZ6CharacterAssignment public

Q-L=1/6-asZ6Character :
  HyperchargeZ6CharacterAssignment
Q-L=1/6-asZ6Character =
  record
    { particle =
        Q-L
    ; hyperchargeAsSignedSixths =
        plusOneSixth
    ; z6CharacterRepresentative =
        FiniteDHR.z6-1
    ; z6CharacterRepresentativeIsSignedSixth =
        refl
    ; displayLabel =
        "Q_L=1/6 as Z6 character multiple 1"
    }

u-R=2/3-asZ6Character :
  HyperchargeZ6CharacterAssignment
u-R=2/3-asZ6Character =
  record
    { particle =
        u-R
    ; hyperchargeAsSignedSixths =
        plusFourSixths
    ; z6CharacterRepresentative =
        FiniteDHR.z6-4
    ; z6CharacterRepresentativeIsSignedSixth =
        refl
    ; displayLabel =
        "u_R=2/3=4/6 as Z6 character multiple 4"
    }

d-R=-1/3-asZ6Character :
  HyperchargeZ6CharacterAssignment
d-R=-1/3-asZ6Character =
  record
    { particle =
        d-R
    ; hyperchargeAsSignedSixths =
        minusTwoSixths
    ; z6CharacterRepresentative =
        FiniteDHR.z6-4
    ; z6CharacterRepresentativeIsSignedSixth =
        refl
    ; displayLabel =
        "d_R=-1/3=-2/6 as Z6 character multiple -2"
    }

e-L=-1/2-asZ6Character :
  HyperchargeZ6CharacterAssignment
e-L=-1/2-asZ6Character =
  record
    { particle =
        e-L
    ; hyperchargeAsSignedSixths =
        minusThreeSixths
    ; z6CharacterRepresentative =
        FiniteDHR.z6-3
    ; z6CharacterRepresentativeIsSignedSixth =
        refl
    ; displayLabel =
        "e_L=-1/2=-3/6 as Z6 character multiple -3"
    }

nu-L=-1/2-asZ6Character :
  HyperchargeZ6CharacterAssignment
nu-L=-1/2-asZ6Character =
  record
    { particle =
        nu-L
    ; hyperchargeAsSignedSixths =
        minusThreeSixths
    ; z6CharacterRepresentative =
        FiniteDHR.z6-3
    ; z6CharacterRepresentativeIsSignedSixth =
        refl
    ; displayLabel =
        "nu_L=-1/2=-3/6 as Z6 character multiple -3"
    }

canonicalHyperchargeZ6CharacterAssignments :
  List HyperchargeZ6CharacterAssignment
canonicalHyperchargeZ6CharacterAssignments =
  Q-L=1/6-asZ6Character
  ∷ u-R=2/3-asZ6Character
  ∷ d-R=-1/3-asZ6Character
  ∷ e-L=-1/2-asZ6Character
  ∷ nu-L=-1/2-asZ6Character
  ∷ []

p3LaneZ6CharacterSourceLabel :
  String
p3LaneZ6CharacterSourceLabel =
  "p3 lane CM unit characters Z/6"

hyperchargeQuantisationExplanationLabel :
  String
hyperchargeQuantisationExplanationLabel =
  "Hypercharges are recorded as signed multiples of 1/6 represented by p3-lane Z/6 CM unit characters"

receiptBoundaryLabel :
  String
receiptBoundaryLabel =
  "Candidate finite Z/6 conductor receipt only; continuous U1 embedding and exact SM promotion remain false"

record U1YFromConductorReceipt : Setω where
  field
    finiteDHRAbelianReceipt :
      FiniteDHR.FiniteDHRAbelianReconstructionReceipt

    p3CMCharacter :
      FiniteDHR.FiniteCMCharacter

    p3CMCharacterIsCanonical :
      p3CMCharacter ≡ FiniteDHR.p3CMCharacter

    p3Z6Component :
      FiniteDHR.Z6Character

    p3Z6ComponentIsGenerator :
      p3Z6Component ≡ FiniteDHR.z6Component p3CMCharacter

    p3LaneCMUnitCharacters :
      String

    p3LaneCMUnitCharactersAreZ6 :
      p3LaneCMUnitCharacters ≡ Fusion.p3CMUnitCharacters
        Fusion.p2p3CharacterCountEnrichment

    p3LaneCMUnitCharacterCount :
      Nat

    p3LaneCMUnitCharacterCountIsSix :
      p3LaneCMUnitCharacterCount ≡ 6

    p3LaneZ6CharacterSource :
      String

    p3LaneZ6CharacterSourceIsCanonical :
      p3LaneZ6CharacterSource ≡ p3LaneZ6CharacterSourceLabel

    hyperchargeAssignments :
      List HyperchargeZ6CharacterAssignment

    hyperchargeAssignmentsAreCanonical :
      hyperchargeAssignments
      ≡
      canonicalHyperchargeZ6CharacterAssignments

    Q-LHypercharge :
      HyperchargeZ6CharacterAssignment

    Q-LHyperchargeIsOneSixth :
      Q-LHypercharge ≡ Q-L=1/6-asZ6Character

    u-RHypercharge :
      HyperchargeZ6CharacterAssignment

    u-RHyperchargeIsTwoThirds :
      u-RHypercharge ≡ u-R=2/3-asZ6Character

    d-RHypercharge :
      HyperchargeZ6CharacterAssignment

    d-RHyperchargeIsMinusOneThird :
      d-RHypercharge ≡ d-R=-1/3-asZ6Character

    e-LHypercharge :
      HyperchargeZ6CharacterAssignment

    e-LHyperchargeIsMinusOneHalf :
      e-LHypercharge ≡ e-L=-1/2-asZ6Character

    nu-LHypercharge :
      HyperchargeZ6CharacterAssignment

    nu-LHyperchargeIsMinusOneHalf :
      nu-LHypercharge ≡ nu-L=-1/2-asZ6Character

    u1yChargesAsZ6Characters :
      Bool

    u1yChargesAsZ6CharactersIsTrue :
      u1yChargesAsZ6Characters ≡ true

    hyperchargeQuantisationExplained :
      Bool

    hyperchargeQuantisationExplainedIsTrue :
      hyperchargeQuantisationExplained ≡ true

    hyperchargeQuantisationExplanation :
      String

    hyperchargeQuantisationExplanationIsCanonical :
      hyperchargeQuantisationExplanation
      ≡
      hyperchargeQuantisationExplanationLabel

    u1yFromP3LaneCMUnit :
      U1YFromP3LaneCMUnitStatus

    u1yFromP3LaneCMUnitIsCandidate :
      u1yFromP3LaneCMUnit ≡ candidate

    continuousU1Embedding :
      Bool

    continuousU1EmbeddingIsFalse :
      continuousU1Embedding ≡ false

    continuousU1EmbeddingConstructed :
      Bool

    continuousU1EmbeddingConstructedIsFalse :
      continuousU1EmbeddingConstructed ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryLabel

    auditTrail :
      List String

open U1YFromConductorReceipt public

canonicalU1YFromConductorReceipt :
  U1YFromConductorReceipt
canonicalU1YFromConductorReceipt =
  record
    { finiteDHRAbelianReceipt =
        FiniteDHR.canonicalFiniteDHRAbelianReconstructionReceipt
    ; p3CMCharacter =
        FiniteDHR.p3CMCharacter
    ; p3CMCharacterIsCanonical =
        refl
    ; p3Z6Component =
        FiniteDHR.z6-1
    ; p3Z6ComponentIsGenerator =
        refl
    ; p3LaneCMUnitCharacters =
        "Z/6"
    ; p3LaneCMUnitCharactersAreZ6 =
        refl
    ; p3LaneCMUnitCharacterCount =
        6
    ; p3LaneCMUnitCharacterCountIsSix =
        refl
    ; p3LaneZ6CharacterSource =
        p3LaneZ6CharacterSourceLabel
    ; p3LaneZ6CharacterSourceIsCanonical =
        refl
    ; hyperchargeAssignments =
        canonicalHyperchargeZ6CharacterAssignments
    ; hyperchargeAssignmentsAreCanonical =
        refl
    ; Q-LHypercharge =
        Q-L=1/6-asZ6Character
    ; Q-LHyperchargeIsOneSixth =
        refl
    ; u-RHypercharge =
        u-R=2/3-asZ6Character
    ; u-RHyperchargeIsTwoThirds =
        refl
    ; d-RHypercharge =
        d-R=-1/3-asZ6Character
    ; d-RHyperchargeIsMinusOneThird =
        refl
    ; e-LHypercharge =
        e-L=-1/2-asZ6Character
    ; e-LHyperchargeIsMinusOneHalf =
        refl
    ; nu-LHypercharge =
        nu-L=-1/2-asZ6Character
    ; nu-LHyperchargeIsMinusOneHalf =
        refl
    ; u1yChargesAsZ6Characters =
        true
    ; u1yChargesAsZ6CharactersIsTrue =
        refl
    ; hyperchargeQuantisationExplained =
        true
    ; hyperchargeQuantisationExplainedIsTrue =
        refl
    ; hyperchargeQuantisationExplanation =
        hyperchargeQuantisationExplanationLabel
    ; hyperchargeQuantisationExplanationIsCanonical =
        refl
    ; u1yFromP3LaneCMUnit =
        candidate
    ; u1yFromP3LaneCMUnitIsCandidate =
        refl
    ; continuousU1Embedding =
        false
    ; continuousU1EmbeddingIsFalse =
        refl
    ; continuousU1EmbeddingConstructed =
        false
    ; continuousU1EmbeddingConstructedIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; receiptBoundary =
        receiptBoundaryLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; auditTrail =
        "p3CMCharacter has Z/6 component z6-1"
        ∷ "The p3 lane CM unit characters are recorded upstream as Z/6"
        ∷ "Q_L=1/6, u_R=2/3, d_R=-1/3, e_L=-1/2, and nu_L=-1/2 are recorded as signed sixths"
        ∷ "u1yChargesAsZ6Characters=true and hyperchargeQuantisationExplained=true"
        ∷ "u1yFromP3LaneCMUnit=candidate"
        ∷ "continuous U1 embedding and exact Standard Model promotion are false"
        ∷ []
    }

u1yFromConductorChargesAsZ6Characters :
  u1yChargesAsZ6Characters canonicalU1YFromConductorReceipt
  ≡
  true
u1yFromConductorChargesAsZ6Characters =
  refl

u1yFromConductorQuantisationExplained :
  hyperchargeQuantisationExplained canonicalU1YFromConductorReceipt
  ≡
  true
u1yFromConductorQuantisationExplained =
  refl

u1yFromConductorP3LaneCandidate :
  u1yFromP3LaneCMUnit canonicalU1YFromConductorReceipt
  ≡
  candidate
u1yFromConductorP3LaneCandidate =
  refl

u1yFromConductorContinuousU1EmbeddingFalse :
  continuousU1Embedding canonicalU1YFromConductorReceipt
  ≡
  false
u1yFromConductorContinuousU1EmbeddingFalse =
  refl

u1yFromConductorExactSMPromotionFalse :
  exactStandardModelPromoted canonicalU1YFromConductorReceipt
  ≡
  false
u1yFromConductorExactSMPromotionFalse =
  refl

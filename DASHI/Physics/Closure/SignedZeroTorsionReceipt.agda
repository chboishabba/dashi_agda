module DASHI.Physics.Closure.SignedZeroTorsionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Signed zero torsion receipt.
--
-- This receipt records signed zero as atom/discourse bookkeeping:
--
-- * +0 and -0 share the same scalar neutral value;
-- * +0 records that the neutral was reached from the positive direction;
-- * -0 records that the neutral was reached from the negative direction;
-- * the distinction is carried by path torsion / helicity orientation, not
--   by a second scalar neutral value;
-- * later encounters may respond differently because opposite torsion or
--   helicity orientations can evolve differently.
--
-- This is not a Navier-Stokes helicity theorem, not a Yang-Mills or Clay
-- promotion, and not a terminal physics result.

data SignedZeroTorsionStatus : Set where
  signedZeroTorsionBookkeepingRecordedFailClosed :
    SignedZeroTorsionStatus

data ScalarNeutralValue : Set where
  neutralScalarZero :
    ScalarNeutralValue

data NeutralArrivalDirection : Set where
  arrivedFromPositiveDirection :
    NeutralArrivalDirection

  arrivedFromNegativeDirection :
    NeutralArrivalDirection

data TorsionOrientation : Set where
  positiveTorsionHelicityOrientation :
    TorsionOrientation

  negativeTorsionHelicityOrientation :
    TorsionOrientation

data SignedZeroLabel : Set where
  plusZeroLabel :
    SignedZeroLabel

  minusZeroLabel :
    SignedZeroLabel

data SignedZero : Set where
  signedZero :
    SignedZeroLabel →
    ScalarNeutralValue →
    NeutralArrivalDirection →
    TorsionOrientation →
    SignedZero

plusZero :
  SignedZero
plusZero =
  signedZero
    plusZeroLabel
    neutralScalarZero
    arrivedFromPositiveDirection
    positiveTorsionHelicityOrientation

minusZero :
  SignedZero
minusZero =
  signedZero
    minusZeroLabel
    neutralScalarZero
    arrivedFromNegativeDirection
    negativeTorsionHelicityOrientation

signedZeroScalarValue :
  SignedZero →
  ScalarNeutralValue
signedZeroScalarValue
  (signedZero _ scalarValue _ _) =
  scalarValue

signedZeroLabel :
  SignedZero →
  SignedZeroLabel
signedZeroLabel
  (signedZero label _ _ _) =
  label

signedZeroArrivalDirection :
  SignedZero →
  NeutralArrivalDirection
signedZeroArrivalDirection
  (signedZero _ _ arrivalDirection _) =
  arrivalDirection

signedZeroTorsionOrientation :
  SignedZero →
  TorsionOrientation
signedZeroTorsionOrientation
  (signedZero _ _ _ torsionOrientation) =
  torsionOrientation

data SignedZeroSemanticPiece : Set where
  plusZeroAndMinusZeroShareNeutralScalar :
    SignedZeroSemanticPiece

  plusZeroArrivesFromPositiveDirection :
    SignedZeroSemanticPiece

  minusZeroArrivesFromNegativeDirection :
    SignedZeroSemanticPiece

  distinctionStoredAsPathTorsionHelicity :
    SignedZeroSemanticPiece

  oppositeTorsionCanAffectLaterEncounters :
    SignedZeroSemanticPiece

canonicalSignedZeroSemanticPieces :
  List SignedZeroSemanticPiece
canonicalSignedZeroSemanticPieces =
  plusZeroAndMinusZeroShareNeutralScalar
  ∷ plusZeroArrivesFromPositiveDirection
  ∷ minusZeroArrivesFromNegativeDirection
  ∷ distinctionStoredAsPathTorsionHelicity
  ∷ oppositeTorsionCanAffectLaterEncounters
  ∷ []

data LaterEncounterResponse : Set where
  sameScalarNeutralSeen :
    LaterEncounterResponse

  positiveHelicityBranchCanEvolveDifferently :
    LaterEncounterResponse

  negativeHelicityBranchCanEvolveDifferently :
    LaterEncounterResponse

canonicalLaterEncounterResponses :
  List LaterEncounterResponse
canonicalLaterEncounterResponses =
  sameScalarNeutralSeen
  ∷ positiveHelicityBranchCanEvolveDifferently
  ∷ negativeHelicityBranchCanEvolveDifferently
  ∷ []

data SignedZeroNonClaim : Set where
  noNavierStokesHelicityTheorem :
    SignedZeroNonClaim

  noYangMillsMassGapClaim :
    SignedZeroNonClaim

  noClayPromotion :
    SignedZeroNonClaim

  noTerminalPromotion :
    SignedZeroNonClaim

canonicalSignedZeroNonClaims :
  List SignedZeroNonClaim
canonicalSignedZeroNonClaims =
  noNavierStokesHelicityTheorem
  ∷ noYangMillsMassGapClaim
  ∷ noClayPromotion
  ∷ noTerminalPromotion
  ∷ []

data SignedZeroPromotion : Set where

signedZeroPromotionImpossibleHere :
  SignedZeroPromotion →
  ⊥
signedZeroPromotionImpossibleHere ()

signedZeroScalarSummary :
  String
signedZeroScalarSummary =
  "+0 and -0 have the same neutral scalar value."

signedZeroTorsionSummary :
  String
signedZeroTorsionSummary =
  "+0 and -0 differ by arrival direction and path torsion/helicity orientation, not by scalar value."

signedZeroEncounterSummary :
  String
signedZeroEncounterSummary =
  "Signed zero can affect later encounters because opposite torsion/helicity orientations may evolve differently."

record SignedZeroTorsionReceipt : Setω where
  field
    status :
      SignedZeroTorsionStatus

    statusIsCanonical :
      status ≡ signedZeroTorsionBookkeepingRecordedFailClosed

    positiveZero :
      SignedZero

    positiveZeroIsCanonical :
      positiveZero ≡ plusZero

    negativeZero :
      SignedZero

    negativeZeroIsCanonical :
      negativeZero ≡ minusZero

    plusZeroScalar :
      ScalarNeutralValue

    plusZeroScalarIsNeutral :
      plusZeroScalar ≡ neutralScalarZero

    minusZeroScalar :
      ScalarNeutralValue

    minusZeroScalarIsNeutral :
      minusZeroScalar ≡ neutralScalarZero

    plusAndMinusZeroSameScalar :
      plusZeroScalar ≡ minusZeroScalar

    plusZeroArrival :
      NeutralArrivalDirection

    plusZeroArrivalIsPositive :
      plusZeroArrival ≡ arrivedFromPositiveDirection

    minusZeroArrival :
      NeutralArrivalDirection

    minusZeroArrivalIsNegative :
      minusZeroArrival ≡ arrivedFromNegativeDirection

    plusZeroTorsion :
      TorsionOrientation

    plusZeroTorsionIsPositive :
      plusZeroTorsion ≡ positiveTorsionHelicityOrientation

    minusZeroTorsion :
      TorsionOrientation

    minusZeroTorsionIsNegative :
      minusZeroTorsion ≡ negativeTorsionHelicityOrientation

    scalarDistinctionMade :
      Bool

    scalarDistinctionMadeIsFalse :
      scalarDistinctionMade ≡ false

    torsionHelicityDistinctionStored :
      Bool

    torsionHelicityDistinctionStoredIsTrue :
      torsionHelicityDistinctionStored ≡ true

    laterEncounterResponsesMayDiffer :
      Bool

    laterEncounterResponsesMayDifferIsTrue :
      laterEncounterResponsesMayDiffer ≡ true

    semanticPieces :
      List SignedZeroSemanticPiece

    semanticPiecesAreCanonical :
      semanticPieces ≡ canonicalSignedZeroSemanticPieces

    laterEncounterResponses :
      List LaterEncounterResponse

    laterEncounterResponsesAreCanonical :
      laterEncounterResponses ≡ canonicalLaterEncounterResponses

    nonClaims :
      List SignedZeroNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalSignedZeroNonClaims

    promotionFlags :
      List SignedZeroPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    noPromotion :
      SignedZeroPromotion →
      ⊥

    scalarSummary :
      String

    scalarSummaryIsCanonical :
      scalarSummary ≡ signedZeroScalarSummary

    torsionSummary :
      String

    torsionSummaryIsCanonical :
      torsionSummary ≡ signedZeroTorsionSummary

    encounterSummary :
      String

    encounterSummaryIsCanonical :
      encounterSummary ≡ signedZeroEncounterSummary

    receiptBoundary :
      List String

open SignedZeroTorsionReceipt public

canonicalSignedZeroTorsionReceipt :
  SignedZeroTorsionReceipt
canonicalSignedZeroTorsionReceipt =
  record
    { status =
        signedZeroTorsionBookkeepingRecordedFailClosed
    ; statusIsCanonical =
        refl
    ; positiveZero =
        plusZero
    ; positiveZeroIsCanonical =
        refl
    ; negativeZero =
        minusZero
    ; negativeZeroIsCanonical =
        refl
    ; plusZeroScalar =
        signedZeroScalarValue plusZero
    ; plusZeroScalarIsNeutral =
        refl
    ; minusZeroScalar =
        signedZeroScalarValue minusZero
    ; minusZeroScalarIsNeutral =
        refl
    ; plusAndMinusZeroSameScalar =
        refl
    ; plusZeroArrival =
        signedZeroArrivalDirection plusZero
    ; plusZeroArrivalIsPositive =
        refl
    ; minusZeroArrival =
        signedZeroArrivalDirection minusZero
    ; minusZeroArrivalIsNegative =
        refl
    ; plusZeroTorsion =
        signedZeroTorsionOrientation plusZero
    ; plusZeroTorsionIsPositive =
        refl
    ; minusZeroTorsion =
        signedZeroTorsionOrientation minusZero
    ; minusZeroTorsionIsNegative =
        refl
    ; scalarDistinctionMade =
        false
    ; scalarDistinctionMadeIsFalse =
        refl
    ; torsionHelicityDistinctionStored =
        true
    ; torsionHelicityDistinctionStoredIsTrue =
        refl
    ; laterEncounterResponsesMayDiffer =
        true
    ; laterEncounterResponsesMayDifferIsTrue =
        refl
    ; semanticPieces =
        canonicalSignedZeroSemanticPieces
    ; semanticPiecesAreCanonical =
        refl
    ; laterEncounterResponses =
        canonicalLaterEncounterResponses
    ; laterEncounterResponsesAreCanonical =
        refl
    ; nonClaims =
        canonicalSignedZeroNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; noPromotion =
        signedZeroPromotionImpossibleHere
    ; scalarSummary =
        signedZeroScalarSummary
    ; scalarSummaryIsCanonical =
        refl
    ; torsionSummary =
        signedZeroTorsionSummary
    ; torsionSummaryIsCanonical =
        refl
    ; encounterSummary =
        signedZeroEncounterSummary
    ; encounterSummaryIsCanonical =
        refl
    ; receiptBoundary =
        "This receipt records atom/discourse signed-zero bookkeeping only"
        ∷ "It stores +0/-0 as distinct path torsion/helicity labels over the same neutral scalar"
        ∷ "It proves no Navier-Stokes helicity theorem and makes no Clay promotion"
        ∷ []
    }

signedZeroNeutralValueShared :
  plusZeroScalar canonicalSignedZeroTorsionReceipt
  ≡
  minusZeroScalar canonicalSignedZeroTorsionReceipt
signedZeroNeutralValueShared =
  refl

signedZeroDistinctionIsNotScalar :
  scalarDistinctionMade canonicalSignedZeroTorsionReceipt ≡ false
signedZeroDistinctionIsNotScalar =
  refl

signedZeroDistinctionIsTorsionHelicity :
  torsionHelicityDistinctionStored canonicalSignedZeroTorsionReceipt ≡ true
signedZeroDistinctionIsTorsionHelicity =
  refl

signedZeroNoClayPromotion :
  promotionFlags canonicalSignedZeroTorsionReceipt ≡ []
signedZeroNoClayPromotion =
  refl

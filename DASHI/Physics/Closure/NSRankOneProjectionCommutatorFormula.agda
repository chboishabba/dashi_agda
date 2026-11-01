module DASHI.Physics.Closure.NSRankOneProjectionCommutatorFormula where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Corrected rank-one projection commutator formula for the NS pressure /
-- strain geometry lane.
--
-- This module records the finite algebraic shape only.  The scalar
-- witnesses are symbolic slots for cos alpha, sin alpha, cos^2 alpha, and
-- sin^2 alpha.  No analytic estimate, pressure control theorem, strain
-- decorrelation theorem, or Clay NS promotion is introduced.

data RankOneProjectionCommutatorStatus : Set where
  correctedRankOneProjectionCommutatorFormulaRecorded :
    RankOneProjectionCommutatorStatus

  pressureChannelPThetaRecorded :
    RankOneProjectionCommutatorStatus

  strainChannelPPlusRecorded :
    RankOneProjectionCommutatorStatus

  angleCosSinScalarWitnessesRecorded :
    RankOneProjectionCommutatorStatus

  frobeniusSquareTwoCos2Sin2Recorded :
    RankOneProjectionCommutatorStatus

  offDiagonalLeakageMeasureRecorded :
    RankOneProjectionCommutatorStatus

  noNSClayOrTerminalPromotion :
    RankOneProjectionCommutatorStatus

canonicalRankOneProjectionCommutatorStatus :
  List RankOneProjectionCommutatorStatus
canonicalRankOneProjectionCommutatorStatus =
  correctedRankOneProjectionCommutatorFormulaRecorded
  ∷ pressureChannelPThetaRecorded
  ∷ strainChannelPPlusRecorded
  ∷ angleCosSinScalarWitnessesRecorded
  ∷ frobeniusSquareTwoCos2Sin2Recorded
  ∷ offDiagonalLeakageMeasureRecorded
  ∷ noNSClayOrTerminalPromotion
  ∷ []

statusRowCount : Nat
statusRowCount =
  7

data NSProjectionChannel : Set where
  pressureChannelPtheta :
    NSProjectionChannel

  strainChannelPplus :
    NSProjectionChannel

canonicalProjectionChannels : List NSProjectionChannel
canonicalProjectionChannels =
  pressureChannelPtheta
  ∷ strainChannelPplus
  ∷ []

projectionChannelCount : Nat
projectionChannelCount =
  2

data RankOneProjection : Set where
  Ptheta :
    RankOneProjection

  Pplus :
    RankOneProjection

data ProjectionRole : Set where
  pressureHessianAngularDirection :
    ProjectionRole

  positiveStrainEigenDirection :
    ProjectionRole

projectionRole : RankOneProjection → ProjectionRole
projectionRole Ptheta =
  pressureHessianAngularDirection
projectionRole Pplus =
  positiveStrainEigenDirection

projectionRolePthetaIsPressure :
  projectionRole Ptheta ≡ pressureHessianAngularDirection
projectionRolePthetaIsPressure =
  refl

projectionRolePplusIsStrain :
  projectionRole Pplus ≡ positiveStrainEigenDirection
projectionRolePplusIsStrain =
  refl

data AngleScalarWitness : Set where
  cosAlpha :
    AngleScalarWitness

  sinAlpha :
    AngleScalarWitness

  cosSquaredAlpha :
    AngleScalarWitness

  sinSquaredAlpha :
    AngleScalarWitness

canonicalAngleScalarWitnesses : List AngleScalarWitness
canonicalAngleScalarWitnesses =
  cosAlpha
  ∷ sinAlpha
  ∷ cosSquaredAlpha
  ∷ sinSquaredAlpha
  ∷ []

angleScalarWitnessCount : Nat
angleScalarWitnessCount =
  4

data ScalarExpression : Set where
  twoCosSquaredAlphaSinSquaredAlpha :
    ScalarExpression

data MatrixEntrySlot : Set where
  thetaThetaEntry :
    MatrixEntrySlot

  thetaPlusEntry :
    MatrixEntrySlot

  plusThetaEntry :
    MatrixEntrySlot

  plusPlusEntry :
    MatrixEntrySlot

data CommutatorEntryStatus : Set where
  diagonalEntryCancels :
    CommutatorEntryStatus

  offDiagonalEntryCarriesLeakage :
    CommutatorEntryStatus

commutatorEntryStatus :
  MatrixEntrySlot →
  CommutatorEntryStatus
commutatorEntryStatus thetaThetaEntry =
  diagonalEntryCancels
commutatorEntryStatus thetaPlusEntry =
  offDiagonalEntryCarriesLeakage
commutatorEntryStatus plusThetaEntry =
  offDiagonalEntryCarriesLeakage
commutatorEntryStatus plusPlusEntry =
  diagonalEntryCancels

thetaThetaEntryCancels :
  commutatorEntryStatus thetaThetaEntry ≡ diagonalEntryCancels
thetaThetaEntryCancels =
  refl

thetaPlusEntryLeaks :
  commutatorEntryStatus thetaPlusEntry ≡ offDiagonalEntryCarriesLeakage
thetaPlusEntryLeaks =
  refl

plusThetaEntryLeaks :
  commutatorEntryStatus plusThetaEntry ≡ offDiagonalEntryCarriesLeakage
plusThetaEntryLeaks =
  refl

plusPlusEntryCancels :
  commutatorEntryStatus plusPlusEntry ≡ diagonalEntryCancels
plusPlusEntryCancels =
  refl

canonicalCommutatorEntrySlots : List MatrixEntrySlot
canonicalCommutatorEntrySlots =
  thetaThetaEntry
  ∷ thetaPlusEntry
  ∷ plusThetaEntry
  ∷ plusPlusEntry
  ∷ []

commutatorEntrySlotCount : Nat
commutatorEntrySlotCount =
  4

data LeakageMeasureRole : Set where
  offDiagonalProjectionMisalignment :
    LeakageMeasureRole

  pressureStrainChannelNoncommutation :
    LeakageMeasureRole

canonicalLeakageMeasureRoles : List LeakageMeasureRole
canonicalLeakageMeasureRoles =
  offDiagonalProjectionMisalignment
  ∷ pressureStrainChannelNoncommutation
  ∷ []

leakageMeasureRoleCount : Nat
leakageMeasureRoleCount =
  2

data RankOneProjectionCommutatorPromotion : Set where

rankOneProjectionCommutatorPromotionImpossibleHere :
  RankOneProjectionCommutatorPromotion →
  ⊥
rankOneProjectionCommutatorPromotionImpossibleHere ()

formulaName : String
formulaName =
  "RankOneProjectionCommutatorFormula"

correctedFormulaText : String
correctedFormulaText =
  "||[Ptheta,Pplus]||_F^2 = 2 cos^2(alpha) sin^2(alpha)"

offDiagonalLeakageText : String
offDiagonalLeakageText =
  "off-diagonal leakage is the pressure/strain channel noncommutation measured by 2 cos^2(alpha) sin^2(alpha)"

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "This is a corrected finite rank-one projection identity surface only; it does not prove pressure control, strain decorrelation, NS regularity, Clay NS, or terminal unification."

record NSRankOneProjectionCommutatorFormula : Setω where
  field
    status :
      List RankOneProjectionCommutatorStatus

    statusIsCanonical :
      status ≡ canonicalRankOneProjectionCommutatorStatus

    recordedStatusRowCount :
      Nat

    recordedStatusRowCountIsSeven :
      recordedStatusRowCount ≡ statusRowCount

    name :
      String

    nameIsCanonical :
      name ≡ formulaName

    pressureProjection :
      RankOneProjection

    pressureProjectionIsPtheta :
      pressureProjection ≡ Ptheta

    pressureChannel :
      NSProjectionChannel

    pressureChannelIsPtheta :
      pressureChannel ≡ pressureChannelPtheta

    strainProjection :
      RankOneProjection

    strainProjectionIsPplus :
      strainProjection ≡ Pplus

    strainChannel :
      NSProjectionChannel

    strainChannelIsPplus :
      strainChannel ≡ strainChannelPplus

    projectionChannels :
      List NSProjectionChannel

    projectionChannelsAreCanonical :
      projectionChannels ≡ canonicalProjectionChannels

    recordedProjectionChannelCount :
      Nat

    recordedProjectionChannelCountIsTwo :
      recordedProjectionChannelCount ≡ projectionChannelCount

    pressureProjectionRole :
      projectionRole pressureProjection ≡ pressureHessianAngularDirection

    strainProjectionRole :
      projectionRole strainProjection ≡ positiveStrainEigenDirection

    angleWitnesses :
      List AngleScalarWitness

    angleWitnessesAreCanonical :
      angleWitnesses ≡ canonicalAngleScalarWitnesses

    recordedAngleWitnessCount :
      Nat

    recordedAngleWitnessCountIsFour :
      recordedAngleWitnessCount ≡ angleScalarWitnessCount

    frobeniusSquareExpression :
      ScalarExpression

    frobeniusSquareExpressionIsTwoCos2Sin2 :
      frobeniusSquareExpression
      ≡
      twoCosSquaredAlphaSinSquaredAlpha

    formulaText :
      String

    formulaTextIsCanonical :
      formulaText ≡ correctedFormulaText

    coefficientNumerator :
      Nat

    coefficientNumeratorIsTwo :
      coefficientNumerator ≡ 2

    cosSquaredFactor :
      AngleScalarWitness

    cosSquaredFactorIsCosSquaredAlpha :
      cosSquaredFactor ≡ cosSquaredAlpha

    sinSquaredFactor :
      AngleScalarWitness

    sinSquaredFactorIsSinSquaredAlpha :
      sinSquaredFactor ≡ sinSquaredAlpha

    commutatorEntrySlots :
      List MatrixEntrySlot

    commutatorEntrySlotsAreCanonical :
      commutatorEntrySlots ≡ canonicalCommutatorEntrySlots

    recordedCommutatorEntrySlotCount :
      Nat

    recordedCommutatorEntrySlotCountIsFour :
      recordedCommutatorEntrySlotCount ≡ commutatorEntrySlotCount

    thetaThetaCancels :
      commutatorEntryStatus thetaThetaEntry ≡ diagonalEntryCancels

    thetaPlusLeaks :
      commutatorEntryStatus thetaPlusEntry
      ≡
      offDiagonalEntryCarriesLeakage

    plusThetaLeaks :
      commutatorEntryStatus plusThetaEntry
      ≡
      offDiagonalEntryCarriesLeakage

    plusPlusCancels :
      commutatorEntryStatus plusPlusEntry ≡ diagonalEntryCancels

    leakageMeasureRoles :
      List LeakageMeasureRole

    leakageMeasureRolesAreCanonical :
      leakageMeasureRoles ≡ canonicalLeakageMeasureRoles

    recordedLeakageMeasureRoleCount :
      Nat

    recordedLeakageMeasureRoleCountIsTwo :
      recordedLeakageMeasureRoleCount ≡ leakageMeasureRoleCount

    offDiagonalLeakageExpression :
      ScalarExpression

    offDiagonalLeakageExpressionIsTwoCos2Sin2 :
      offDiagonalLeakageExpression
      ≡
      twoCosSquaredAlphaSinSquaredAlpha

    offDiagonalLeakageLabel :
      String

    offDiagonalLeakageLabelIsCanonical :
      offDiagonalLeakageLabel ≡ offDiagonalLeakageText

    correctedFormulaRecorded :
      Bool

    correctedFormulaRecordedIsTrue :
      correctedFormulaRecorded ≡ true

    analyticPressureControlProved :
      Bool

    analyticPressureControlProvedIsFalse :
      analyticPressureControlProved ≡ false

    strainDecorrelationProved :
      Bool

    strainDecorrelationProvedIsFalse :
      strainDecorrelationProved ≡ false

    nsRegularityPromoted :
      Bool

    nsRegularityPromotedIsFalse :
      nsRegularityPromoted ≡ false

    navierStokesClayPromoted :
      Bool

    navierStokesClayPromotedIsFalse :
      navierStokesClayPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    promotionFlags :
      List RankOneProjectionCommutatorPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    nonPromotionBoundary :
      String

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary ≡ nonPromotionBoundaryText

    remainingObligations :
      List String

open NSRankOneProjectionCommutatorFormula public

canonicalNSRankOneProjectionCommutatorFormula :
  NSRankOneProjectionCommutatorFormula
canonicalNSRankOneProjectionCommutatorFormula =
  record
    { status =
        canonicalRankOneProjectionCommutatorStatus
    ; statusIsCanonical =
        refl
    ; recordedStatusRowCount =
        statusRowCount
    ; recordedStatusRowCountIsSeven =
        refl
    ; name =
        formulaName
    ; nameIsCanonical =
        refl
    ; pressureProjection =
        Ptheta
    ; pressureProjectionIsPtheta =
        refl
    ; pressureChannel =
        pressureChannelPtheta
    ; pressureChannelIsPtheta =
        refl
    ; strainProjection =
        Pplus
    ; strainProjectionIsPplus =
        refl
    ; strainChannel =
        strainChannelPplus
    ; strainChannelIsPplus =
        refl
    ; projectionChannels =
        canonicalProjectionChannels
    ; projectionChannelsAreCanonical =
        refl
    ; recordedProjectionChannelCount =
        projectionChannelCount
    ; recordedProjectionChannelCountIsTwo =
        refl
    ; pressureProjectionRole =
        refl
    ; strainProjectionRole =
        refl
    ; angleWitnesses =
        canonicalAngleScalarWitnesses
    ; angleWitnessesAreCanonical =
        refl
    ; recordedAngleWitnessCount =
        angleScalarWitnessCount
    ; recordedAngleWitnessCountIsFour =
        refl
    ; frobeniusSquareExpression =
        twoCosSquaredAlphaSinSquaredAlpha
    ; frobeniusSquareExpressionIsTwoCos2Sin2 =
        refl
    ; formulaText =
        correctedFormulaText
    ; formulaTextIsCanonical =
        refl
    ; coefficientNumerator =
        2
    ; coefficientNumeratorIsTwo =
        refl
    ; cosSquaredFactor =
        cosSquaredAlpha
    ; cosSquaredFactorIsCosSquaredAlpha =
        refl
    ; sinSquaredFactor =
        sinSquaredAlpha
    ; sinSquaredFactorIsSinSquaredAlpha =
        refl
    ; commutatorEntrySlots =
        canonicalCommutatorEntrySlots
    ; commutatorEntrySlotsAreCanonical =
        refl
    ; recordedCommutatorEntrySlotCount =
        commutatorEntrySlotCount
    ; recordedCommutatorEntrySlotCountIsFour =
        refl
    ; thetaThetaCancels =
        thetaThetaEntryCancels
    ; thetaPlusLeaks =
        thetaPlusEntryLeaks
    ; plusThetaLeaks =
        plusThetaEntryLeaks
    ; plusPlusCancels =
        plusPlusEntryCancels
    ; leakageMeasureRoles =
        canonicalLeakageMeasureRoles
    ; leakageMeasureRolesAreCanonical =
        refl
    ; recordedLeakageMeasureRoleCount =
        leakageMeasureRoleCount
    ; recordedLeakageMeasureRoleCountIsTwo =
        refl
    ; offDiagonalLeakageExpression =
        twoCosSquaredAlphaSinSquaredAlpha
    ; offDiagonalLeakageExpressionIsTwoCos2Sin2 =
        refl
    ; offDiagonalLeakageLabel =
        offDiagonalLeakageText
    ; offDiagonalLeakageLabelIsCanonical =
        refl
    ; correctedFormulaRecorded =
        true
    ; correctedFormulaRecordedIsTrue =
        refl
    ; analyticPressureControlProved =
        false
    ; analyticPressureControlProvedIsFalse =
        refl
    ; strainDecorrelationProved =
        false
    ; strainDecorrelationProvedIsFalse =
        refl
    ; nsRegularityPromoted =
        false
    ; nsRegularityPromotedIsFalse =
        refl
    ; navierStokesClayPromoted =
        false
    ; navierStokesClayPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; nonPromotionBoundary =
        nonPromotionBoundaryText
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; remainingObligations =
        "derive the rank-one identity from an accepted real two-plane projection algebra if needed by an analytic consumer"
        ∷ "connect the leakage expression to a pressure commutator estimate with quantified sign and size"
        ∷ "prove a strain decorrelation or pressure-control theorem before any NS regularity claim"
        ∷ "prove full mechanism exhaustion before any Clay NS promotion"
        ∷ []
    }

rankOneProjectionFormulaRecorded :
  correctedFormulaRecorded canonicalNSRankOneProjectionCommutatorFormula
  ≡
  true
rankOneProjectionFormulaRecorded =
  refl

rankOneProjectionFrobeniusExpressionIsCorrected :
  frobeniusSquareExpression canonicalNSRankOneProjectionCommutatorFormula
  ≡
  twoCosSquaredAlphaSinSquaredAlpha
rankOneProjectionFrobeniusExpressionIsCorrected =
  refl

rankOneProjectionOffDiagonalLeakageIsCorrected :
  offDiagonalLeakageExpression canonicalNSRankOneProjectionCommutatorFormula
  ≡
  twoCosSquaredAlphaSinSquaredAlpha
rankOneProjectionOffDiagonalLeakageIsCorrected =
  refl

rankOneProjectionKeepsNSClayFalse :
  navierStokesClayPromoted canonicalNSRankOneProjectionCommutatorFormula
  ≡
  false
rankOneProjectionKeepsNSClayFalse =
  refl

rankOneProjectionKeepsTerminalFalse :
  terminalPromotion canonicalNSRankOneProjectionCommutatorFormula
  ≡
  false
rankOneProjectionKeepsTerminalFalse =
  refl

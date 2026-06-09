module DASHI.Physics.Closure.YMFlatLimitBestCandidateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yang-Mills archimedean flat-limit best-candidate receipt.
--
-- This receipt records the current best candidate for the archimedean flat
-- limit: cusp degeneration of X_0(N) as N -> infinity.  Near cusps the
-- modular curve degenerates and the geometry becomes locally flat; Yang-Mills
-- restricted to the cusp region is therefore recorded as the locally
-- flat-space YM candidate.
--
-- The scale flag is deliberately formal/string-valued.  If the carrier mass
-- gap scale is Lambda_c and the cusp scale is N^{-1}, the flat regime requires
-- Lambda_c >> N^{-1}, equivalently N >> Lambda_c^{-1}.  Large N then gives a
-- flat spatial region of size N in q-coordinate, enough for the YM correlation
-- length Lambda_c^{-1}.  This is candidate-only and does not promote any
-- Clay, continuum, or terminal Yang-Mills claim.

data YMFlatLimitCandidateStatus : Set where
  candidate :
    YMFlatLimitCandidateStatus

data YMFlatLimitBestCandidateStatus : Set where
  archimedeanCuspDegenerationCandidateRecorded :
    YMFlatLimitBestCandidateStatus

data YMFlatLimitBestCandidateFact : Set where
  cuspDegenerationOfX0NAsNToInfinity :
    YMFlatLimitBestCandidateFact

  modularCurveDegeneratesNearCusps :
    YMFlatLimitBestCandidateFact

  cuspGeometryBecomesLocallyFlat :
    YMFlatLimitBestCandidateFact

  ymOnCuspRegionIsLocallyFlatSpaceYMCandidate :
    YMFlatLimitBestCandidateFact

  carrierMassGapScaleLambdaC :
    YMFlatLimitBestCandidateFact

  cuspScaleNInverse :
    YMFlatLimitBestCandidateFact

  requireLambdaCGreaterThanNInverse :
    YMFlatLimitBestCandidateFact

  equivalentLargeNCondition :
    YMFlatLimitBestCandidateFact

  qCoordinateFlatRegionSizeN :
    YMFlatLimitBestCandidateFact

  flatRegionContainsYMCorrelationLength :
    YMFlatLimitBestCandidateFact

canonicalYMFlatLimitBestCandidateFacts :
  List YMFlatLimitBestCandidateFact
canonicalYMFlatLimitBestCandidateFacts =
  cuspDegenerationOfX0NAsNToInfinity
  ∷ modularCurveDegeneratesNearCusps
  ∷ cuspGeometryBecomesLocallyFlat
  ∷ ymOnCuspRegionIsLocallyFlatSpaceYMCandidate
  ∷ carrierMassGapScaleLambdaC
  ∷ cuspScaleNInverse
  ∷ requireLambdaCGreaterThanNInverse
  ∷ equivalentLargeNCondition
  ∷ qCoordinateFlatRegionSizeN
  ∷ flatRegionContainsYMCorrelationLength
  ∷ []

data YMFlatLimitBestCandidateOpenObligation : Set where
  proveUniformCuspFlatness :
    YMFlatLimitBestCandidateOpenObligation

  constructArchimedeanContinuumYMFromCuspRegime :
    YMFlatLimitBestCandidateOpenObligation

  proveClayMassGapSurvivalInFlatCuspLimit :
    YMFlatLimitBestCandidateOpenObligation

canonicalYMFlatLimitBestCandidateOpenObligations :
  List YMFlatLimitBestCandidateOpenObligation
canonicalYMFlatLimitBestCandidateOpenObligations =
  proveUniformCuspFlatness
  ∷ constructArchimedeanContinuumYMFromCuspRegime
  ∷ proveClayMassGapSurvivalInFlatCuspLimit
  ∷ []

data YMFlatLimitBestCandidatePromotion : Set where

ymFlatLimitBestCandidatePromotionImpossibleHere :
  YMFlatLimitBestCandidatePromotion →
  ⊥
ymFlatLimitBestCandidatePromotionImpossibleHere ()

cuspDegenerationFlatLimitStatement :
  String
cuspDegenerationFlatLimitStatement =
  "Best current archimedean flat-limit candidate: cusp degeneration of X_0(N) as N -> infinity.  Near cusps the modular curve degenerates and geometry becomes locally flat, so YM on the cusp region is the locally flat-space YM candidate.  Flat-regime scale flag: Lambda_c >> N^{-1}, equivalently N >> Lambda_c^{-1}; large N gives a flat q-coordinate region of size N, enough for YM correlation length Lambda_c^{-1}."

record YMFlatLimitBestCandidateReceipt : Setω where
  field
    status :
      YMFlatLimitBestCandidateStatus

    cuspDegenerationAsFlatLimitMechanism :
      YMFlatLimitCandidateStatus

    cuspDegenerationAsFlatLimitMechanismIsCandidate :
      cuspDegenerationAsFlatLimitMechanism ≡ candidate

    ymInFlatCuspRegime :
      YMFlatLimitCandidateStatus

    ymInFlatCuspRegimeIsCandidate :
      ymInFlatCuspRegime ≡ candidate

    facts :
      List YMFlatLimitBestCandidateFact

    factsAreCanonical :
      facts ≡ canonicalYMFlatLimitBestCandidateFacts

    modularCurveFamily :
      String

    modularCurveFamilyIsX0N :
      modularCurveFamily ≡ "X_0(N)"

    archimedeanLimitParameter :
      String

    archimedeanLimitParameterIsNToInfinity :
      archimedeanLimitParameter ≡ "N -> infinity"

    localGeometryNearCusps :
      String

    localGeometryNearCuspsIsFlatCandidate :
      localGeometryNearCusps ≡ "locally flat near cusps"

    carrierMassGapScale :
      String

    carrierMassGapScaleIsLambdaC :
      carrierMassGapScale ≡ "Lambda_c"

    cuspScale :
      String

    cuspScaleIsNInverse :
      cuspScale ≡ "N^{-1}"

    conditionForFlatRegime :
      String

    conditionForFlatRegimeIsCanonical :
      conditionForFlatRegime ≡ "N >> LambdaC^{-1}"

    massGapDominatesCuspScale :
      Bool

    massGapDominatesCuspScaleIsTrue :
      massGapDominatesCuspScale ≡ true

    qCoordinateFlatRegionSize :
      String

    qCoordinateFlatRegionSizeIsN :
      qCoordinateFlatRegionSize ≡ "N"

    ymCorrelationLength :
      String

    ymCorrelationLengthIsLambdaCInverse :
      ymCorrelationLength ≡ "Lambda_c^{-1}"

    flatRegionContainsCorrelationLength :
      Bool

    flatRegionContainsCorrelationLengthIsTrue :
      flatRegionContainsCorrelationLength ≡ true

    uniformCuspFlatnessProved :
      Bool

    uniformCuspFlatnessProvedIsFalse :
      uniformCuspFlatnessProved ≡ false

    archimedeanContinuumYMConstructed :
      Bool

    archimedeanContinuumYMConstructedIsFalse :
      archimedeanContinuumYMConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    terminalYMPromoted :
      Bool

    terminalYMPromotedIsFalse :
      terminalYMPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    openObligations :
      List YMFlatLimitBestCandidateOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMFlatLimitBestCandidateOpenObligations

    statement :
      String

    statementIsCanonical :
      statement ≡ cuspDegenerationFlatLimitStatement

    promotionFlags :
      List YMFlatLimitBestCandidatePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMFlatLimitBestCandidateReceipt public

canonicalYMFlatLimitBestCandidateReceipt :
  YMFlatLimitBestCandidateReceipt
canonicalYMFlatLimitBestCandidateReceipt =
  record
    { status =
        archimedeanCuspDegenerationCandidateRecorded
    ; cuspDegenerationAsFlatLimitMechanism =
        candidate
    ; cuspDegenerationAsFlatLimitMechanismIsCandidate =
        refl
    ; ymInFlatCuspRegime =
        candidate
    ; ymInFlatCuspRegimeIsCandidate =
        refl
    ; facts =
        canonicalYMFlatLimitBestCandidateFacts
    ; factsAreCanonical =
        refl
    ; modularCurveFamily =
        "X_0(N)"
    ; modularCurveFamilyIsX0N =
        refl
    ; archimedeanLimitParameter =
        "N -> infinity"
    ; archimedeanLimitParameterIsNToInfinity =
        refl
    ; localGeometryNearCusps =
        "locally flat near cusps"
    ; localGeometryNearCuspsIsFlatCandidate =
        refl
    ; carrierMassGapScale =
        "Lambda_c"
    ; carrierMassGapScaleIsLambdaC =
        refl
    ; cuspScale =
        "N^{-1}"
    ; cuspScaleIsNInverse =
        refl
    ; conditionForFlatRegime =
        "N >> LambdaC^{-1}"
    ; conditionForFlatRegimeIsCanonical =
        refl
    ; massGapDominatesCuspScale =
        true
    ; massGapDominatesCuspScaleIsTrue =
        refl
    ; qCoordinateFlatRegionSize =
        "N"
    ; qCoordinateFlatRegionSizeIsN =
        refl
    ; ymCorrelationLength =
        "Lambda_c^{-1}"
    ; ymCorrelationLengthIsLambdaCInverse =
        refl
    ; flatRegionContainsCorrelationLength =
        true
    ; flatRegionContainsCorrelationLengthIsTrue =
        refl
    ; uniformCuspFlatnessProved =
        false
    ; uniformCuspFlatnessProvedIsFalse =
        refl
    ; archimedeanContinuumYMConstructed =
        false
    ; archimedeanContinuumYMConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; terminalYMPromoted =
        false
    ; terminalYMPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; openObligations =
        canonicalYMFlatLimitBestCandidateOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; statement =
        cuspDegenerationFlatLimitStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "cuspDegenerationAsFlatLimitMechanism = candidate"
        ∷ "conditionForFlatRegime = N >> LambdaC^{-1}"
        ∷ "ymInFlatCuspRegime = candidate"
        ∷ "Near cusps of X_0(N) as N -> infinity, modular-curve degeneration is recorded as locally flat"
        ∷ "Large N gives a q-coordinate flat region of size N, enough for YM correlation length Lambda_c^{-1}"
        ∷ "All Clay, continuum YM, terminal YM, and terminal Clay promotions remain false"
        ∷ []
    }

ymFlatLimitBestCandidateKeepsClayFalse :
  clayYangMillsPromoted canonicalYMFlatLimitBestCandidateReceipt
  ≡
  false
ymFlatLimitBestCandidateKeepsClayFalse =
  refl

ymFlatLimitBestCandidateKeepsContinuumYMFalse :
  continuumYangMillsPromoted canonicalYMFlatLimitBestCandidateReceipt
  ≡
  false
ymFlatLimitBestCandidateKeepsContinuumYMFalse =
  refl

ymFlatLimitBestCandidateKeepsTerminalYMFalse :
  terminalYMPromoted canonicalYMFlatLimitBestCandidateReceipt
  ≡
  false
ymFlatLimitBestCandidateKeepsTerminalYMFalse =
  refl

ymFlatLimitBestCandidateKeepsTerminalClayFalse :
  terminalClayClaimPromoted canonicalYMFlatLimitBestCandidateReceipt
  ≡
  false
ymFlatLimitBestCandidateKeepsTerminalClayFalse =
  refl

ymFlatLimitBestCandidateNoPromotion :
  YMFlatLimitBestCandidatePromotion →
  ⊥
ymFlatLimitBestCandidateNoPromotion =
  ymFlatLimitBestCandidatePromotionImpossibleHere

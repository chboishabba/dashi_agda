module DASHI.Physics.Closure.ShimuraTowerFlatLimitReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Local flat limit of the Shimura tower.
--
-- This receipt records only a local-flatness candidate for the Shimura
-- tower continuum picture.  Hyperbolic geometry has curvature fixed at -1,
-- so charts whose diameter is much smaller than the curvature radius are
-- recorded as locally Euclidean for Yang--Mills fields varying on those
-- scales.  This does not promote a Clay Yang--Mills proof or a terminal
-- Clay claim.

data ShimuraTowerFlatLimitStatus : Set where
  shimuraTowerLocalFlatnessCandidateRecordedNoClay :
    ShimuraTowerFlatLimitStatus

data ShimuraTowerFlatLimitCandidate : Set where
  candidate :
    ShimuraTowerFlatLimitCandidate

data ShimuraTowerFlatLimitPromotion : Set where

shimuraTowerFlatLimitPromotionImpossibleHere :
  ShimuraTowerFlatLimitPromotion →
  ⊥
shimuraTowerFlatLimitPromotionImpossibleHere ()

shimuraTowerFlatLimitStatement :
  String
shimuraTowerFlatLimitStatement =
  "The Shimura tower is recorded as a local flatness candidate: hyperbolic curvature is fixed at -1, diameter grows like log(N), CM spacing scales as inverse psi(N_i^k) and tends to zero, so fields varying on scales much smaller than the curvature radius see local Euclidean geometry."

shimuraTowerCurvatureStatement :
  String
shimuraTowerCurvatureStatement =
  "Hyperbolic geometry is locally flat on scales much smaller than its curvature radius; the tower curvature is fixed at -1."

shimuraTowerDiameterStatement :
  String
shimuraTowerDiameterStatement =
  "The Shimura tower diameter is recorded as growing like log(N)."

shimuraTowerCMSpacingStatement :
  String
shimuraTowerCMSpacingStatement =
  "CM spacing goes like inverse psi(N_i^k) and tends to zero in the tower limit."

shimuraTowerYMLocalEuclideanStatement :
  String
shimuraTowerYMLocalEuclideanStatement =
  "Yang--Mills fields varying on scales below the curvature radius see local Euclidean geometry."

shimuraTowerMassGapCandidateStatement :
  String
shimuraTowerMassGapCandidateStatement =
  "mass-gap-in-locally-flat-regime is recorded only as a candidate."

shimuraTowerCurvatureCorrectionStatement :
  String
shimuraTowerCurvatureCorrectionStatement =
  "Curvature corrections are recorded as subleading candidate corrections, not as a promotion."

record ShimuraTowerFlatLimitReceipt : Set where
  field
    status :
      ShimuraTowerFlatLimitStatus

    hyperbolicGeometryLocallyFlatBelowCurvatureRadius :
      Bool

    hyperbolicGeometryLocallyFlatBelowCurvatureRadiusIsTrue :
      hyperbolicGeometryLocallyFlatBelowCurvatureRadius ≡ true

    curvatureFixedMinusOne :
      Bool

    curvatureFixedMinusOneIsTrue :
      curvatureFixedMinusOne ≡ true

    curvatureValue :
      String

    curvatureValueIsMinusOne :
      curvatureValue ≡ "-1"

    diameterGrowthLaw :
      String

    diameterGrowthLawIsLogN :
      diameterGrowthLaw ≡ "log(N)"

    cmSpacingLaw :
      String

    cmSpacingLawIsInversePsi :
      cmSpacingLaw ≡ "1/psi(N_i^k)"

    cmSpacingTendsToZero :
      Bool

    cmSpacingTendsToZeroIsTrue :
      cmSpacingTendsToZero ≡ true

    ymFieldsBelowCurvatureRadiusSeeLocalEuclideanGeometry :
      Bool

    ymFieldsBelowCurvatureRadiusSeeLocalEuclideanGeometryIsTrue :
      ymFieldsBelowCurvatureRadiusSeeLocalEuclideanGeometry ≡ true

    localFlatnessForShimuraTower :
      ShimuraTowerFlatLimitCandidate

    localFlatnessForShimuraTowerIsCandidate :
      localFlatnessForShimuraTower ≡ candidate

    mass-gap-in-locally-flat-regime :
      ShimuraTowerFlatLimitCandidate

    mass-gap-in-locally-flat-regimeIsCandidate :
      mass-gap-in-locally-flat-regime ≡ candidate

    curvatureCorrectionsSubleading :
      ShimuraTowerFlatLimitCandidate

    curvatureCorrectionsSubleadingIsCandidate :
      curvatureCorrectionsSubleading ≡ candidate

    curvatureCorrectionsPromoted :
      Bool

    curvatureCorrectionsPromotedIsFalse :
      curvatureCorrectionsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    localFlatnessStatement :
      String

    localFlatnessStatementIsCanonical :
      localFlatnessStatement ≡ shimuraTowerFlatLimitStatement

    curvatureStatement :
      String

    curvatureStatementIsCanonical :
      curvatureStatement ≡ shimuraTowerCurvatureStatement

    diameterStatement :
      String

    diameterStatementIsCanonical :
      diameterStatement ≡ shimuraTowerDiameterStatement

    cmSpacingStatement :
      String

    cmSpacingStatementIsCanonical :
      cmSpacingStatement ≡ shimuraTowerCMSpacingStatement

    ymLocalEuclideanStatement :
      String

    ymLocalEuclideanStatementIsCanonical :
      ymLocalEuclideanStatement ≡ shimuraTowerYMLocalEuclideanStatement

    massGapCandidateStatement :
      String

    massGapCandidateStatementIsCanonical :
      massGapCandidateStatement ≡ shimuraTowerMassGapCandidateStatement

    curvatureCorrectionStatement :
      String

    curvatureCorrectionStatementIsCanonical :
      curvatureCorrectionStatement ≡ shimuraTowerCurvatureCorrectionStatement

    promotionFlags :
      List ShimuraTowerFlatLimitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ShimuraTowerFlatLimitReceipt public

canonicalShimuraTowerFlatLimitReceipt :
  ShimuraTowerFlatLimitReceipt
canonicalShimuraTowerFlatLimitReceipt =
  record
    { status =
        shimuraTowerLocalFlatnessCandidateRecordedNoClay
    ; hyperbolicGeometryLocallyFlatBelowCurvatureRadius =
        true
    ; hyperbolicGeometryLocallyFlatBelowCurvatureRadiusIsTrue =
        refl
    ; curvatureFixedMinusOne =
        true
    ; curvatureFixedMinusOneIsTrue =
        refl
    ; curvatureValue =
        "-1"
    ; curvatureValueIsMinusOne =
        refl
    ; diameterGrowthLaw =
        "log(N)"
    ; diameterGrowthLawIsLogN =
        refl
    ; cmSpacingLaw =
        "1/psi(N_i^k)"
    ; cmSpacingLawIsInversePsi =
        refl
    ; cmSpacingTendsToZero =
        true
    ; cmSpacingTendsToZeroIsTrue =
        refl
    ; ymFieldsBelowCurvatureRadiusSeeLocalEuclideanGeometry =
        true
    ; ymFieldsBelowCurvatureRadiusSeeLocalEuclideanGeometryIsTrue =
        refl
    ; localFlatnessForShimuraTower =
        candidate
    ; localFlatnessForShimuraTowerIsCandidate =
        refl
    ; mass-gap-in-locally-flat-regime =
        candidate
    ; mass-gap-in-locally-flat-regimeIsCandidate =
        refl
    ; curvatureCorrectionsSubleading =
        candidate
    ; curvatureCorrectionsSubleadingIsCandidate =
        refl
    ; curvatureCorrectionsPromoted =
        false
    ; curvatureCorrectionsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; localFlatnessStatement =
        shimuraTowerFlatLimitStatement
    ; localFlatnessStatementIsCanonical =
        refl
    ; curvatureStatement =
        shimuraTowerCurvatureStatement
    ; curvatureStatementIsCanonical =
        refl
    ; diameterStatement =
        shimuraTowerDiameterStatement
    ; diameterStatementIsCanonical =
        refl
    ; cmSpacingStatement =
        shimuraTowerCMSpacingStatement
    ; cmSpacingStatementIsCanonical =
        refl
    ; ymLocalEuclideanStatement =
        shimuraTowerYMLocalEuclideanStatement
    ; ymLocalEuclideanStatementIsCanonical =
        refl
    ; massGapCandidateStatement =
        shimuraTowerMassGapCandidateStatement
    ; massGapCandidateStatementIsCanonical =
        refl
    ; curvatureCorrectionStatement =
        shimuraTowerCurvatureCorrectionStatement
    ; curvatureCorrectionStatementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records only the local flatness candidate for the Shimura tower"
        ∷ "Hyperbolic curvature is fixed at -1, while diameter grows like log(N)"
        ∷ "CM spacing scales as 1/psi(N_i^k) and tends to zero"
        ∷ "Yang--Mills fields varying below the curvature radius see local Euclidean geometry"
        ∷ "mass-gap-in-locally-flat-regime remains candidate-valued"
        ∷ "Curvature corrections are subleading candidates, not promotions"
        ∷ "Clay Yang-Mills and terminal Clay promotions remain false"
        ∷ []
    }

shimuraTowerFlatLimitIsCandidate :
  localFlatnessForShimuraTower canonicalShimuraTowerFlatLimitReceipt
  ≡
  candidate
shimuraTowerFlatLimitIsCandidate =
  refl

shimuraTowerMassGapInLocallyFlatRegimeIsCandidate :
  mass-gap-in-locally-flat-regime canonicalShimuraTowerFlatLimitReceipt
  ≡
  candidate
shimuraTowerMassGapInLocallyFlatRegimeIsCandidate =
  refl

shimuraTowerCurvatureCorrectionsSubleadingCandidate :
  curvatureCorrectionsSubleading canonicalShimuraTowerFlatLimitReceipt
  ≡
  candidate
shimuraTowerCurvatureCorrectionsSubleadingCandidate =
  refl

shimuraTowerFlatLimitDoesNotPromoteCurvatureCorrections :
  curvatureCorrectionsPromoted canonicalShimuraTowerFlatLimitReceipt
  ≡
  false
shimuraTowerFlatLimitDoesNotPromoteCurvatureCorrections =
  refl

shimuraTowerFlatLimitKeepsClayFalse :
  clayYangMillsPromoted canonicalShimuraTowerFlatLimitReceipt
  ≡
  false
shimuraTowerFlatLimitKeepsClayFalse =
  refl

shimuraTowerFlatLimitKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalShimuraTowerFlatLimitReceipt
  ≡
  false
shimuraTowerFlatLimitKeepsTerminalFalse =
  refl

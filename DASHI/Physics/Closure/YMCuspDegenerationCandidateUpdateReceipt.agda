module DASHI.Physics.Closure.YMCuspDegenerationCandidateUpdateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yang-Mills cusp-degeneration candidate update receipt.
--
-- This receipt records the updated archimedean cusp-degeneration candidate:
-- take a cusp of X_0(N), let tau -> i infinity, and use
-- q = exp(2*pi*i*tau/N).  Near q = 0, field configurations supported in
-- |q| <= q_* << 1 see an approximately flat metric.  The flatness recorded
-- here is local flatness for high-energy/localized modes only; it is not a
-- global flatness theorem and does not close the cusp candidate.

data YMCuspDegenerationCandidateUpdateStatus : Set where
  cuspDegenerationLocalFlatnessUpdateRecorded :
    YMCuspDegenerationCandidateUpdateStatus

data YMCuspDegenerationUpdateFact : Set where
  cuspOfX0N :
    YMCuspDegenerationUpdateFact

  tauTendsToIInfinity :
    YMCuspDegenerationUpdateFact

  qCoordinateExpTwoPiITauOverN :
    YMCuspDegenerationUpdateFact

  nearQZero :
    YMCuspDegenerationUpdateFact

  fieldConfigurationsSupportedInSmallQDisk :
    YMCuspDegenerationUpdateFact

  approximatelyFlatMetricForLocalizedModes :
    YMCuspDegenerationUpdateFact

  localFlatnessOnly :
    YMCuspDegenerationUpdateFact

  globalFlatnessNotEstablished :
    YMCuspDegenerationUpdateFact

  cuspCandidateStillOpen :
    YMCuspDegenerationUpdateFact

canonicalYMCuspDegenerationUpdateFacts :
  List YMCuspDegenerationUpdateFact
canonicalYMCuspDegenerationUpdateFacts =
  cuspOfX0N
  ∷ tauTendsToIInfinity
  ∷ qCoordinateExpTwoPiITauOverN
  ∷ nearQZero
  ∷ fieldConfigurationsSupportedInSmallQDisk
  ∷ approximatelyFlatMetricForLocalizedModes
  ∷ localFlatnessOnly
  ∷ globalFlatnessNotEstablished
  ∷ cuspCandidateStillOpen
  ∷ []

data YMCuspDegenerationOpenObligation : Set where
  proveUniformLocalCuspFlatness :
    YMCuspDegenerationOpenObligation

  promoteLocalFlatnessToRequiredGlobalControl :
    YMCuspDegenerationOpenObligation

  constructContinuumYangMillsFromCuspDegeneration :
    YMCuspDegenerationOpenObligation

canonicalYMCuspDegenerationOpenObligations :
  List YMCuspDegenerationOpenObligation
canonicalYMCuspDegenerationOpenObligations =
  proveUniformLocalCuspFlatness
  ∷ promoteLocalFlatnessToRequiredGlobalControl
  ∷ constructContinuumYangMillsFromCuspDegeneration
  ∷ []

data YMCuspDegenerationPromotion : Set where

ymCuspDegenerationPromotionImpossibleHere :
  YMCuspDegenerationPromotion →
  ⊥
ymCuspDegenerationPromotionImpossibleHere ()

ymCuspDegenerationCandidateUpdateStatement :
  String
ymCuspDegenerationCandidateUpdateStatement =
  "Cusp degeneration update: at a cusp of X_0(N), tau -> i infinity and q = exp(2*pi*i*tau/N).  Near q = 0, field configurations supported |q| <= q_* << 1 see an approximately flat metric.  This records LOCAL flatness for high-energy/localized modes, not global flatness; the cusp candidate remains open."

record YMCuspDegenerationCandidateUpdateReceipt : Setω where
  field
    status :
      YMCuspDegenerationCandidateUpdateStatus

    statusIsCanonical :
      status ≡ cuspDegenerationLocalFlatnessUpdateRecorded

    modularCurve :
      String

    modularCurveIsX0N :
      modularCurve ≡ "X_0(N)"

    cusp :
      String

    cuspIsCuspOfX0N :
      cusp ≡ "cusp of X_0(N)"

    degenerationParameter :
      String

    degenerationParameterIsTauToIInfinity :
      degenerationParameter ≡ "tau -> i infinity"

    qCoordinate :
      String

    qCoordinateIsCanonical :
      qCoordinate ≡ "q = exp(2*pi*i*tau/N)"

    cuspRegion :
      String

    cuspRegionIsNearQZero :
      cuspRegion ≡ "near q = 0"

    fieldSupportRegion :
      String

    fieldSupportRegionIsSmallQDisk :
      fieldSupportRegion ≡ "|q| <= q_* << 1"

    approximatelyFlatMetricSeen :
      Bool

    approximatelyFlatMetricSeenIsTrue :
      approximatelyFlatMetricSeen ≡ true

    highEnergyLocalizedModesOnly :
      Bool

    highEnergyLocalizedModesOnlyIsTrue :
      highEnergyLocalizedModesOnly ≡ true

    cuspDegenerationGivesLocalFlatness :
      Bool

    cuspDegenerationGivesLocalFlatnessIsTrue :
      cuspDegenerationGivesLocalFlatness ≡ true

    globalFlatnessMissing :
      Bool

    globalFlatnessMissingIsTrue :
      globalFlatnessMissing ≡ true

    cuspCandidateRemainsOpen :
      Bool

    cuspCandidateRemainsOpenIsTrue :
      cuspCandidateRemainsOpen ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalYMPromoted :
      Bool

    terminalYMPromotedIsFalse :
      terminalYMPromoted ≡ false

    facts :
      List YMCuspDegenerationUpdateFact

    factsAreCanonical :
      facts ≡ canonicalYMCuspDegenerationUpdateFacts

    openObligations :
      List YMCuspDegenerationOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMCuspDegenerationOpenObligations

    statement :
      String

    statementIsCanonical :
      statement ≡ ymCuspDegenerationCandidateUpdateStatement

    promotionFlags :
      List YMCuspDegenerationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMCuspDegenerationCandidateUpdateReceipt public

canonicalYMCuspDegenerationCandidateUpdateReceipt :
  YMCuspDegenerationCandidateUpdateReceipt
canonicalYMCuspDegenerationCandidateUpdateReceipt =
  record
    { status =
        cuspDegenerationLocalFlatnessUpdateRecorded
    ; statusIsCanonical =
        refl
    ; modularCurve =
        "X_0(N)"
    ; modularCurveIsX0N =
        refl
    ; cusp =
        "cusp of X_0(N)"
    ; cuspIsCuspOfX0N =
        refl
    ; degenerationParameter =
        "tau -> i infinity"
    ; degenerationParameterIsTauToIInfinity =
        refl
    ; qCoordinate =
        "q = exp(2*pi*i*tau/N)"
    ; qCoordinateIsCanonical =
        refl
    ; cuspRegion =
        "near q = 0"
    ; cuspRegionIsNearQZero =
        refl
    ; fieldSupportRegion =
        "|q| <= q_* << 1"
    ; fieldSupportRegionIsSmallQDisk =
        refl
    ; approximatelyFlatMetricSeen =
        true
    ; approximatelyFlatMetricSeenIsTrue =
        refl
    ; highEnergyLocalizedModesOnly =
        true
    ; highEnergyLocalizedModesOnlyIsTrue =
        refl
    ; cuspDegenerationGivesLocalFlatness =
        true
    ; cuspDegenerationGivesLocalFlatnessIsTrue =
        refl
    ; globalFlatnessMissing =
        true
    ; globalFlatnessMissingIsTrue =
        refl
    ; cuspCandidateRemainsOpen =
        true
    ; cuspCandidateRemainsOpenIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalYMPromoted =
        false
    ; terminalYMPromotedIsFalse =
        refl
    ; facts =
        canonicalYMCuspDegenerationUpdateFacts
    ; factsAreCanonical =
        refl
    ; openObligations =
        canonicalYMCuspDegenerationOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; statement =
        ymCuspDegenerationCandidateUpdateStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records cusp degeneration of X_0(N) with tau -> i infinity"
        ∷ "Uses q = exp(2*pi*i*tau/N) near q = 0"
        ∷ "Field configurations supported |q| <= q_* << 1 see an approximately flat metric"
        ∷ "The flatness flag is local and applies to high-energy/localized modes"
        ∷ "Global flatness is missing and the cusp candidate remains open"
        ∷ "No Clay Yang-Mills or terminal Yang-Mills promotion is introduced"
        ∷ []
    }

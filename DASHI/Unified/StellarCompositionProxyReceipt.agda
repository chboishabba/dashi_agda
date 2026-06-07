module DASHI.Unified.StellarCompositionProxyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Staged stellar simulator receipt.
--
-- This receipt records the first executable stellar-composition simulator
-- lane as a bounded proxy surface only.  It is intentionally fail-closed:
-- script and output paths may be recorded, but carrier-internal stellar
-- evolution and solar instability claims remain unpromoted until the
-- canonical stellar physics authorities and validation receipts are present.

data StellarCompositionProxyStatus : Set where
  boundedStellarCompositionProxySurfaceRecorded :
    StellarCompositionProxyStatus

data StellarCompositionProxyBlocker : Set where
  missingCarrierDerivedMatterForceLaw :
    StellarCompositionProxyBlocker

  missingEOSAuthority :
    StellarCompositionProxyBlocker

  missingOpacityAuthority :
    StellarCompositionProxyBlocker

  missingReactionNetworkAuthority :
    StellarCompositionProxyBlocker

  missingHydrostaticSolverAuthority :
    StellarCompositionProxyBlocker

  missingEmpiricalValidationReceipt :
    StellarCompositionProxyBlocker

canonicalStellarCompositionProxyBlockers :
  List StellarCompositionProxyBlocker
canonicalStellarCompositionProxyBlockers =
  missingCarrierDerivedMatterForceLaw
  ∷ missingEOSAuthority
  ∷ missingOpacityAuthority
  ∷ missingReactionNetworkAuthority
  ∷ missingHydrostaticSolverAuthority
  ∷ missingEmpiricalValidationReceipt
  ∷ []

data StellarCompositionProxyPromotion : Set where

stellarCompositionProxyPromotionImpossibleHere :
  StellarCompositionProxyPromotion →
  ⊥
stellarCompositionProxyPromotionImpossibleHere ()

diagnosticScriptPathText : String
diagnosticScriptPathText =
  "scripts/run_stellar_composition_proxy_diagnostic.py"

diagnosticOutputPathText : String
diagnosticOutputPathText =
  "scripts/data/outputs/stellar_composition_proxy_diagnostic.{json,csv,md}"

receiptBoundaryText : String
receiptBoundaryText =
  "The staged stellar simulator lane records an executable bounded composition proxy only.  Carrier-derived matter/force law, EOS authority, opacity authority, reaction-network authority, hydrostatic solver authority, and empirical validation receipt remain blockers before any internal stellar-evolution or solar-instability claim can be promoted."

record StellarCompositionProxyReceipt : Setω where
  field
    status :
      StellarCompositionProxyStatus

    statusIsCanonical :
      status ≡ boundedStellarCompositionProxySurfaceRecorded

    diagnosticScriptPath :
      String

    diagnosticScriptPathIsCanonical :
      diagnosticScriptPath ≡ diagnosticScriptPathText

    diagnosticOutputPath :
      String

    diagnosticOutputPathIsCanonical :
      diagnosticOutputPath ≡ diagnosticOutputPathText

    carrierInternalPrediction :
      Bool

    carrierInternalPredictionIsFalse :
      carrierInternalPrediction ≡ false

    stellarEvolutionPromoted :
      Bool

    stellarEvolutionPromotedIsFalse :
      stellarEvolutionPromoted ≡ false

    solarInstabilityClaimPromoted :
      Bool

    solarInstabilityClaimPromotedIsFalse :
      solarInstabilityClaimPromoted ≡ false

    externalBaselineOrProxyOnly :
      Bool

    externalBaselineOrProxyOnlyIsTrue :
      externalBaselineOrProxyOnly ≡ true

    blockers :
      List StellarCompositionProxyBlocker

    blockersAreCanonical :
      blockers ≡ canonicalStellarCompositionProxyBlockers

    firstBlocker :
      StellarCompositionProxyBlocker

    firstBlockerIsMissingCarrierDerivedMatterForceLaw :
      firstBlocker ≡ missingCarrierDerivedMatterForceLaw

    eosAuthorityBlocker :
      StellarCompositionProxyBlocker

    eosAuthorityBlockerIsMissingEOSAuthority :
      eosAuthorityBlocker ≡ missingEOSAuthority

    opacityAuthorityBlocker :
      StellarCompositionProxyBlocker

    opacityAuthorityBlockerIsMissingOpacityAuthority :
      opacityAuthorityBlocker ≡ missingOpacityAuthority

    reactionNetworkAuthorityBlocker :
      StellarCompositionProxyBlocker

    reactionNetworkAuthorityBlockerIsMissingReactionNetworkAuthority :
      reactionNetworkAuthorityBlocker ≡ missingReactionNetworkAuthority

    hydrostaticSolverAuthorityBlocker :
      StellarCompositionProxyBlocker

    hydrostaticSolverAuthorityBlockerIsMissingHydrostaticSolverAuthority :
      hydrostaticSolverAuthorityBlocker ≡ missingHydrostaticSolverAuthority

    empiricalValidationBlocker :
      StellarCompositionProxyBlocker

    empiricalValidationBlockerIsMissingEmpiricalValidationReceipt :
      empiricalValidationBlocker ≡ missingEmpiricalValidationReceipt

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ receiptBoundaryText

    promotions :
      List StellarCompositionProxyPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      StellarCompositionProxyPromotion →
      ⊥

open StellarCompositionProxyReceipt public

canonicalStellarCompositionProxyReceipt :
  StellarCompositionProxyReceipt
canonicalStellarCompositionProxyReceipt =
  record
    { status =
        boundedStellarCompositionProxySurfaceRecorded
    ; statusIsCanonical =
        refl
    ; diagnosticScriptPath =
        diagnosticScriptPathText
    ; diagnosticScriptPathIsCanonical =
        refl
    ; diagnosticOutputPath =
        diagnosticOutputPathText
    ; diagnosticOutputPathIsCanonical =
        refl
    ; carrierInternalPrediction =
        false
    ; carrierInternalPredictionIsFalse =
        refl
    ; stellarEvolutionPromoted =
        false
    ; stellarEvolutionPromotedIsFalse =
        refl
    ; solarInstabilityClaimPromoted =
        false
    ; solarInstabilityClaimPromotedIsFalse =
        refl
    ; externalBaselineOrProxyOnly =
        true
    ; externalBaselineOrProxyOnlyIsTrue =
        refl
    ; blockers =
        canonicalStellarCompositionProxyBlockers
    ; blockersAreCanonical =
        refl
    ; firstBlocker =
        missingCarrierDerivedMatterForceLaw
    ; firstBlockerIsMissingCarrierDerivedMatterForceLaw =
        refl
    ; eosAuthorityBlocker =
        missingEOSAuthority
    ; eosAuthorityBlockerIsMissingEOSAuthority =
        refl
    ; opacityAuthorityBlocker =
        missingOpacityAuthority
    ; opacityAuthorityBlockerIsMissingOpacityAuthority =
        refl
    ; reactionNetworkAuthorityBlocker =
        missingReactionNetworkAuthority
    ; reactionNetworkAuthorityBlockerIsMissingReactionNetworkAuthority =
        refl
    ; hydrostaticSolverAuthorityBlocker =
        missingHydrostaticSolverAuthority
    ; hydrostaticSolverAuthorityBlockerIsMissingHydrostaticSolverAuthority =
        refl
    ; empiricalValidationBlocker =
        missingEmpiricalValidationReceipt
    ; empiricalValidationBlockerIsMissingEmpiricalValidationReceipt =
        refl
    ; boundary =
        receiptBoundaryText
    ; boundaryIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        stellarCompositionProxyPromotionImpossibleHere
    }

canonicalStellarCompositionProxyCarrierInternalPredictionBlocked :
  carrierInternalPrediction canonicalStellarCompositionProxyReceipt ≡ false
canonicalStellarCompositionProxyCarrierInternalPredictionBlocked =
  refl

canonicalStellarCompositionProxyStellarEvolutionBlocked :
  stellarEvolutionPromoted canonicalStellarCompositionProxyReceipt ≡ false
canonicalStellarCompositionProxyStellarEvolutionBlocked =
  refl

canonicalStellarCompositionProxySolarInstabilityClaimBlocked :
  solarInstabilityClaimPromoted canonicalStellarCompositionProxyReceipt ≡ false
canonicalStellarCompositionProxySolarInstabilityClaimBlocked =
  refl

canonicalStellarCompositionProxyExternalBaselineOrProxyOnly :
  externalBaselineOrProxyOnly canonicalStellarCompositionProxyReceipt ≡ true
canonicalStellarCompositionProxyExternalBaselineOrProxyOnly =
  refl

canonicalStellarCompositionProxyBlockersAreCanonical :
  blockers canonicalStellarCompositionProxyReceipt
  ≡
  canonicalStellarCompositionProxyBlockers
canonicalStellarCompositionProxyBlockersAreCanonical =
  refl

stellarCompositionProxyCarrierDerivedMatterForceLawBlocker :
  firstBlocker canonicalStellarCompositionProxyReceipt
  ≡
  missingCarrierDerivedMatterForceLaw
stellarCompositionProxyCarrierDerivedMatterForceLawBlocker =
  refl

stellarCompositionProxyEOSAuthorityBlocker :
  eosAuthorityBlocker canonicalStellarCompositionProxyReceipt
  ≡
  missingEOSAuthority
stellarCompositionProxyEOSAuthorityBlocker =
  refl

stellarCompositionProxyOpacityAuthorityBlocker :
  opacityAuthorityBlocker canonicalStellarCompositionProxyReceipt
  ≡
  missingOpacityAuthority
stellarCompositionProxyOpacityAuthorityBlocker =
  refl

stellarCompositionProxyReactionNetworkAuthorityBlocker :
  reactionNetworkAuthorityBlocker canonicalStellarCompositionProxyReceipt
  ≡
  missingReactionNetworkAuthority
stellarCompositionProxyReactionNetworkAuthorityBlocker =
  refl

stellarCompositionProxyHydrostaticSolverAuthorityBlocker :
  hydrostaticSolverAuthorityBlocker canonicalStellarCompositionProxyReceipt
  ≡
  missingHydrostaticSolverAuthority
stellarCompositionProxyHydrostaticSolverAuthorityBlocker =
  refl

stellarCompositionProxyEmpiricalValidationBlocker :
  empiricalValidationBlocker canonicalStellarCompositionProxyReceipt
  ≡
  missingEmpiricalValidationReceipt
stellarCompositionProxyEmpiricalValidationBlocker =
  refl

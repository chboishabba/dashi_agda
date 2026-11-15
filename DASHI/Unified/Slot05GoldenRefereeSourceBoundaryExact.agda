{-# OPTIONS --safe #-}
module DASHI.Unified.Slot05GoldenRefereeSourceBoundaryExact where

-- Slot 05/20 pinned-source audit, 2026-11-02.
-- Historical input revision: dashi_agda@624200192339.
-- This module is a safe, postulate-free *audit-classification carrier*.
-- It does not prove the five audited modules or their transitive imports
-- typecheck with --safe. Source inspection != kernel acceptance.
-- Original proof ownership stays with each imported owner (not imported here).
-- Source claims are retained separately from external empirical authority.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record SourcePin : Set where
  constructor sourcePin
  field
    repository : String
    revision : String

pinnedSource : SourcePin
pinnedSource = sourcePin "chboishabba/dashi_agda" "624200192339"

data ClaimClass : Set where
  finiteSourceReceipt : ClaimClass
  requestedContinuumAuthority : ClaimClass
  requestedPhysicalAuthority : ClaimClass
  assertedTerminalPromotion : ClaimClass

record PromotionBoundary : Set where
  constructor promotionBoundary
  field
    oneFrameExplainsEverything : Bool
    oneFrameExplainsEverythingIsFalse :
      oneFrameExplainsEverything ≡ false
    finiteDiagnosticClaimsContinuum : Bool
    finiteDiagnosticClaimsContinuumIsFalse :
      finiteDiagnosticClaimsContinuum ≡ false
    finiteDiagnosticClaimsPhysicalValidation : Bool
    finiteDiagnosticClaimsPhysicalValidationIsFalse :
      finiteDiagnosticClaimsPhysicalValidation ≡ false
    finiteDiagnosticClaimsTerminal : Bool
    finiteDiagnosticClaimsTerminalIsFalse :
      finiteDiagnosticClaimsTerminal ≡ false

canonicalPromotionBoundary : PromotionBoundary
canonicalPromotionBoundary =
  promotionBoundary false refl false refl false refl false refl

-- These are proof terms ONLY about the canonical audit values. They
-- do not assert that a continuum/empirical witness has been supplied.
noSingleFramePromotion :
  oneFrameExplainsEverything canonicalPromotionBoundary ≡ false
noSingleFramePromotion =
  oneFrameExplainsEverythingIsFalse canonicalPromotionBoundary

noContinuumPromotion :
  finiteDiagnosticClaimsContinuum canonicalPromotionBoundary ≡ false
noContinuumPromotion =
  finiteDiagnosticClaimsContinuumIsFalse canonicalPromotionBoundary

noPhysicalPromotion :
  finiteDiagnosticClaimsPhysicalValidation canonicalPromotionBoundary ≡ false
noPhysicalPromotion =
  finiteDiagnosticClaimsPhysicalValidationIsFalse canonicalPromotionBoundary

noTerminalPromotion :
  finiteDiagnosticClaimsTerminal canonicalPromotionBoundary ≡ false
noTerminalPromotion =
  finiteDiagnosticClaimsTerminalIsFalse canonicalPromotionBoundary

data VerificationKind : Set where
  sourceTextInspected : VerificationKind
  transitiveSafeTypecheckAccepted : VerificationKind
  explicitContinuumWitnessAccepted : VerificationKind
  independentPhysicalObservationAccepted : VerificationKind

record RefereeReceipt : Set where
  constructor refereeReceipt
  field
    pinned : SourcePin
    localSourceInspected : Bool
    fiveModulesCarrySafeOptionAtPin : Bool
    transitiveSafeTypecheckExecuted : Bool
    zeroPostulateClosureKernelConfirmed : Bool
    zeroMetasKernelConfirmed : Bool
    noTerminatingPragmasSourceObserved : Bool
    continuumAndPhysicalAuthoritySupplied : Bool

canonicalRefereeReceipt : RefereeReceipt
canonicalRefereeReceipt =
  refereeReceipt pinnedSource true false false false false true false

receiptCannotClaimKernelSuccess :
  transitiveSafeTypecheckExecuted canonicalRefereeReceipt ≡ false
receiptCannotClaimKernelSuccess = refl

receiptRequiresSourceOwnerProofs :
  zeroPostulateClosureKernelConfirmed canonicalRefereeReceipt ≡ false
receiptRequiresSourceOwnerProofs = refl

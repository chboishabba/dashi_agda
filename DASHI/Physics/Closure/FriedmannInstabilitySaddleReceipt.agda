module DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ContractedBianchiMatterClosure as BianchiMatter
import DASHI.Physics.Closure.WaldGRAuthorityReceipt as Wald

------------------------------------------------------------------------
-- Temple-Alexander-Vogler Friedmann instability authority boundary.
--
-- This receipt records Proc. R. Soc. A 482:20250912 as an external Gate 4
-- authority for the instability/saddle-point statement about pressureless
-- Friedmann spacetimes in the Einstein-Euler self-similar ODE system.  It
-- consumes the current contracted-Bianchi matter closure surface and the Wald
-- continuum-GR authority receipt, but it does not derive cosmology inside
-- DASHI and does not promote any dark-energy or LCDM conclusion.

data FriedmannInstabilityAuthorityStatus : Set where
  friedmannInstabilityAuthorityRecordedFailClosed :
    FriedmannInstabilityAuthorityStatus

data FriedmannInstabilityAuthorityScope : Set where
  einsteinEulerSelfSimilarSystemScope :
    FriedmannInstabilityAuthorityScope
  pressurelessFriedmannRadialPerturbationScope :
    FriedmannInstabilityAuthorityScope
  criticalFriedmannSaddleRestPointScope :
    FriedmannInstabilityAuthorityScope
  underdensePerturbationMinkowskiDirectionScope :
    FriedmannInstabilityAuthorityScope
  contractedBianchiGate4ConsumptionScope :
    FriedmannInstabilityAuthorityScope

canonicalFriedmannInstabilityAuthorityScopes :
  List FriedmannInstabilityAuthorityScope
canonicalFriedmannInstabilityAuthorityScopes =
  einsteinEulerSelfSimilarSystemScope
  ∷ pressurelessFriedmannRadialPerturbationScope
  ∷ criticalFriedmannSaddleRestPointScope
  ∷ underdensePerturbationMinkowskiDirectionScope
  ∷ contractedBianchiGate4ConsumptionScope
  ∷ []

data FriedmannInstabilityPromotionBlocker : Set where
  missingEinsteinEulerCarrierODEDerivation :
    FriedmannInstabilityPromotionBlocker
  missingSelfSimilarXiCarrierIdentificationProof :
    FriedmannInstabilityPromotionBlocker
  missingContinuumExistenceTheoryCompletion :
    FriedmannInstabilityPromotionBlocker
  missingCarrierPhasePortraitTransportMap :
    FriedmannInstabilityPromotionBlocker
  missingObservationalCosmologyModelComparison :
    FriedmannInstabilityPromotionBlocker

canonicalFriedmannInstabilityPromotionBlockers :
  List FriedmannInstabilityPromotionBlocker
canonicalFriedmannInstabilityPromotionBlockers =
  missingEinsteinEulerCarrierODEDerivation
  ∷ missingSelfSimilarXiCarrierIdentificationProof
  ∷ missingContinuumExistenceTheoryCompletion
  ∷ missingCarrierPhasePortraitTransportMap
  ∷ missingObservationalCosmologyModelComparison
  ∷ []

record FriedmannInstabilitySaddleReceipt : Setω where
  field
    status :
      FriedmannInstabilityAuthorityStatus

    authorityTitle :
      String

    authorityTitleIsTemple2026 :
      authorityTitle
      ≡
      "The instability of critical and underdense Friedmann spacetimes at the Big Bang as an alternative to dark energy"

    authorityAuthors :
      String

    authorityAuthorsAreCanonical :
      authorityAuthors
      ≡
      "C. Alexander, B. Temple, and Z. Vogler"

    authorityJournal :
      String

    authorityJournalIsRoyalSocietyA :
      authorityJournal
      ≡
      "Proceedings of the Royal Society A 482:20250912"

    authorityYear :
      String

    authorityYearIs2026 :
      authorityYear ≡ "2026"

    authorityDOI :
      String

    authorityDOIIsCanonical :
      authorityDOI ≡ "10.1098/rspa.2025.0912"

    localPDFSHA256 :
      String

    localPDFSHA256IsBound :
      localPDFSHA256
      ≡
      "a105917e23d118c6c41004292c2ecb2a32f042dec738ccd2c380253e0eace6cf"

    theoremBoundaryText :
      String

    theoremBoundaryTextIsCanonical :
      theoremBoundaryText
      ≡
      "Temple-Alexander-Vogler 2026: pressureless Friedmann spacetimes are unstable to radial perturbation in Einstein-Euler self-similar variables xi = r/t, with the critical Friedmann spacetime an unstable saddle rest point"

    authorityScopes :
      List FriedmannInstabilityAuthorityScope

    authorityScopesAreCanonical :
      authorityScopes ≡ canonicalFriedmannInstabilityAuthorityScopes

    internalPrecondition :
      BianchiMatter.ContractedBianchiMatterClosureReceipt

    internalPreconditionClosurePromotedIsFalse :
      BianchiMatter.ContractedBianchiMatterClosureReceipt.closurePromoted
        internalPrecondition
      ≡
      false

    waldContinuumAuthorityBoundary :
      Wald.WaldGRAuthorityReceipt

    waldContinuumSourcedEinsteinStillFailClosed :
      Wald.WaldGRAuthorityReceipt.continuumSourcedEinsteinPromoted
        waldContinuumAuthorityBoundary
      ≡
      false

    selfSimilarVariable :
      String

    selfSimilarVariableIsXi :
      selfSimilarVariable ≡ "xi = r/t"

    friedmannUnstableSaddlePoint :
      Bool

    friedmannUnstableSaddlePointIsAuthorityBacked :
      friedmannUnstableSaddlePoint ≡ true

    carrierXiIdentificationProved :
      Bool

    carrierXiIdentificationProvedIsFalse :
      carrierXiIdentificationProved ≡ false

    darkEnergyRemoved :
      Bool

    darkEnergyRemovedIsFalse :
      darkEnergyRemoved ≡ false

    LCDMFalsified :
      Bool

    LCDMFalsifiedIsFalse :
      LCDMFalsified ≡ false

    cosmologyPromoted :
      Bool

    cosmologyPromotedIsFalse :
      cosmologyPromoted ≡ false

    promotionBlockers :
      List FriedmannInstabilityPromotionBlocker

    promotionBlockersAreCanonical :
      promotionBlockers
      ≡
      canonicalFriedmannInstabilityPromotionBlockers

    receiptBoundary :
      List String

open FriedmannInstabilitySaddleReceipt public

canonicalFriedmannInstabilitySaddleReceipt :
  FriedmannInstabilitySaddleReceipt
canonicalFriedmannInstabilitySaddleReceipt =
  record
    { status =
        friedmannInstabilityAuthorityRecordedFailClosed
    ; authorityTitle =
        "The instability of critical and underdense Friedmann spacetimes at the Big Bang as an alternative to dark energy"
    ; authorityTitleIsTemple2026 =
        refl
    ; authorityAuthors =
        "C. Alexander, B. Temple, and Z. Vogler"
    ; authorityAuthorsAreCanonical =
        refl
    ; authorityJournal =
        "Proceedings of the Royal Society A 482:20250912"
    ; authorityJournalIsRoyalSocietyA =
        refl
    ; authorityYear =
        "2026"
    ; authorityYearIs2026 =
        refl
    ; authorityDOI =
        "10.1098/rspa.2025.0912"
    ; authorityDOIIsCanonical =
        refl
    ; localPDFSHA256 =
        "a105917e23d118c6c41004292c2ecb2a32f042dec738ccd2c380253e0eace6cf"
    ; localPDFSHA256IsBound =
        refl
    ; theoremBoundaryText =
        "Temple-Alexander-Vogler 2026: pressureless Friedmann spacetimes are unstable to radial perturbation in Einstein-Euler self-similar variables xi = r/t, with the critical Friedmann spacetime an unstable saddle rest point"
    ; theoremBoundaryTextIsCanonical =
        refl
    ; authorityScopes =
        canonicalFriedmannInstabilityAuthorityScopes
    ; authorityScopesAreCanonical =
        refl
    ; internalPrecondition =
        BianchiMatter.canonicalContractedBianchiMatterClosureReceipt
    ; internalPreconditionClosurePromotedIsFalse =
        BianchiMatter.contractedBianchiMatterClosureRemainsFailClosed
    ; waldContinuumAuthorityBoundary =
        Wald.canonicalWaldGRAuthorityReceipt
    ; waldContinuumSourcedEinsteinStillFailClosed =
        Wald.waldGRAuthorityContinuumSourcedEinsteinStillFailClosed
    ; selfSimilarVariable =
        "xi = r/t"
    ; selfSimilarVariableIsXi =
        refl
    ; friedmannUnstableSaddlePoint =
        true
    ; friedmannUnstableSaddlePointIsAuthorityBacked =
        refl
    ; carrierXiIdentificationProved =
        false
    ; carrierXiIdentificationProvedIsFalse =
        refl
    ; darkEnergyRemoved =
        false
    ; darkEnergyRemovedIsFalse =
        refl
    ; LCDMFalsified =
        false
    ; LCDMFalsifiedIsFalse =
        refl
    ; cosmologyPromoted =
        false
    ; cosmologyPromotedIsFalse =
        refl
    ; promotionBlockers =
        canonicalFriedmannInstabilityPromotionBlockers
    ; promotionBlockersAreCanonical =
        refl
    ; receiptBoundary =
        "Proc. R. Soc. A 482:20250912 is recorded as an external authority boundary for Friedmann instability in the Einstein-Euler self-similar ODE system"
        ∷ "The internal DASHI precondition is the existing contracted-Bianchi matter closure receipt, which remains fail-closed"
        ∷ "The receipt records xi = r/t as the self-similar variable but does not prove an equivalence with carrier ultrametric depth"
        ∷ "friedmannUnstableSaddlePoint is true only as an authority-backed theorem boundary"
        ∷ "darkEnergyRemoved, LCDMFalsified, carrierXiIdentificationProved, and cosmologyPromoted all remain false"
        ∷ []
    }

friedmannInstabilitySaddlePointAuthorityBacked :
  friedmannUnstableSaddlePoint
    canonicalFriedmannInstabilitySaddleReceipt
  ≡
  true
friedmannInstabilitySaddlePointAuthorityBacked =
  refl

friedmannInstabilityDoesNotRemoveDarkEnergyHere :
  darkEnergyRemoved
    canonicalFriedmannInstabilitySaddleReceipt
  ≡
  false
friedmannInstabilityDoesNotRemoveDarkEnergyHere =
  refl

friedmannInstabilityDoesNotFalsifyLCDMHere :
  LCDMFalsified
    canonicalFriedmannInstabilitySaddleReceipt
  ≡
  false
friedmannInstabilityDoesNotFalsifyLCDMHere =
  refl

friedmannInstabilityCosmologyPromotionStillFailClosed :
  cosmologyPromoted
    canonicalFriedmannInstabilitySaddleReceipt
  ≡
  false
friedmannInstabilityCosmologyPromotionStillFailClosed =
  refl

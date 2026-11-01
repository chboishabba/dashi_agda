module DASHI.Physics.Closure.YMUniversalityClassReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as Balaban
import DASHI.Physics.Closure.BetaCriticalReceipt as B4
import DASHI.Physics.Closure.Phase2ProgrammeReceipt as Phase2

------------------------------------------------------------------------
-- Product-lattice Yang-Mills universality-class receipt.
--
-- This records the 4D product lattice as a candidate in the standard
-- Wilson SU(N) universality class.  It is evidence/route bookkeeping only:
-- Balaban inheritance is conditional on the universality-class hypothesis,
-- and no Clay, continuum mass-gap, or terminal promotion is introduced.

data YMUniversalityClassCandidateStatus : Set where
  productLatticeWilsonSUNCandidateOnly :
    YMUniversalityClassCandidateStatus

data YMUniversalityClassEvidence : Set where
  sameGaugeGroupSU-N :
    YMUniversalityClassEvidence

  oneLoopBetaFromB4 :
    YMUniversalityClassEvidence

  reflectionPositivityOfWilsonPlaquetteAction :
    YMUniversalityClassEvidence

  continuumO4AfterAnisotropyDecay :
    YMUniversalityClassEvidence

  anisotropicLatticeYMKarsch1982Authority :
    YMUniversalityClassEvidence

canonicalYMUniversalityClassEvidence :
  List YMUniversalityClassEvidence
canonicalYMUniversalityClassEvidence =
  sameGaugeGroupSU-N
  ∷ oneLoopBetaFromB4
  ∷ reflectionPositivityOfWilsonPlaquetteAction
  ∷ continuumO4AfterAnisotropyDecay
  ∷ anisotropicLatticeYMKarsch1982Authority
  ∷ []

data YMUniversalityClassOpenObligation : Set where
  missingNonperturbativeUniversalityTheorem :
    YMUniversalityClassOpenObligation

  missingUniformAnisotropyDecayBound :
    YMUniversalityClassOpenObligation

  missingContinuumO4Reconstruction :
    YMUniversalityClassOpenObligation

  missingClayAuthorityAcceptance :
    YMUniversalityClassOpenObligation

canonicalYMUniversalityClassOpenObligations :
  List YMUniversalityClassOpenObligation
canonicalYMUniversalityClassOpenObligations =
  missingNonperturbativeUniversalityTheorem
  ∷ missingUniformAnisotropyDecayBound
  ∷ missingContinuumO4Reconstruction
  ∷ missingClayAuthorityAcceptance
  ∷ []

data YMUniversalityClassPromotion : Set where

ymUniversalityClassPromotionImpossibleHere :
  YMUniversalityClassPromotion →
  ⊥
ymUniversalityClassPromotionImpossibleHere ()

productLatticeCandidateLabel : String
productLatticeCandidateLabel =
  "4D product lattice Wilson SU(N) Yang-Mills candidate"

standardWilsonUniversalityClassLabel : String
standardWilsonUniversalityClassLabel =
  "standard 4D SU(N) Wilson Yang-Mills universality class"

karsch1982AuthorityLabel : String
karsch1982AuthorityLabel =
  "F. Karsch, SU(N) gauge theory couplings on asymmetric lattices, Nuclear Physics B 205(2), 285-300 (1982), DOI 10.1016/0550-3213(82)90390-X"

oneLoopBetaB4Label : String
oneLoopBetaB4Label =
  "B4 records the standard Wilson continuum trajectory; the one-loop beta evidence is used only as universality-class evidence"

record YMUniversalityClassReceipt : Setω where
  field
    status :
      YMUniversalityClassCandidateStatus

    phase2ReframeReceipt :
      Phase2.ManagerCClayReframeReceipt

    phase2ProductLatticeBalabanRouteRecorded :
      Phase2.productLatticeBalabanRouteRecorded phase2ReframeReceipt
      ≡
      true

    phase2UniversalityClassStillUnsettled :
      Phase2.productLatticeUniversalityClassSettled phase2ReframeReceipt
      ≡
      false

    balabanReceipt :
      Balaban.BalabanRGMassGapReceiptSurface

    balabanContinuumPromotionStillFalse :
      Balaban.BalabanRGMassGapReceiptSurface.continuumMassGapPromotedByDASHI
        balabanReceipt
      ≡
      false

    b4BetaReceipt :
      B4.BetaCriticalReceipt

    b4StandardWilsonTrajectoryRecorded :
      B4.standardWilsonContinuumLimitRequiresBetaToInfinity b4BetaReceipt
      ≡
      true

    productLatticeCandidate :
      String

    productLatticeCandidateIsCanonical :
      productLatticeCandidate ≡ productLatticeCandidateLabel

    candidateUniversalityClass :
      String

    candidateUniversalityClassIsCanonical :
      candidateUniversalityClass ≡ standardWilsonUniversalityClassLabel

    sameGaugeGroupEvidence :
      Bool

    sameGaugeGroupEvidenceIsTrue :
      sameGaugeGroupEvidence ≡ true

    oneLoopBetaEvidenceFromB4 :
      Bool

    oneLoopBetaEvidenceFromB4IsTrue :
      oneLoopBetaEvidenceFromB4 ≡ true

    oneLoopBetaEvidenceLabel :
      String

    oneLoopBetaEvidenceLabelIsCanonical :
      oneLoopBetaEvidenceLabel ≡ oneLoopBetaB4Label

    reflectionPositivityEvidence :
      Bool

    reflectionPositivityEvidenceIsTrue :
      reflectionPositivityEvidence ≡ true

    continuumO4AfterAnisotropyDecaysEvidence :
      Bool

    continuumO4AfterAnisotropyDecaysEvidenceIsTrue :
      continuumO4AfterAnisotropyDecaysEvidence ≡ true

    karsch1982AnisotropicLatticeAuthority :
      String

    karsch1982AnisotropicLatticeAuthorityIsCanonical :
      karsch1982AnisotropicLatticeAuthority ≡ karsch1982AuthorityLabel

    candidateEvidence :
      List YMUniversalityClassEvidence

    candidateEvidenceIsCanonical :
      candidateEvidence ≡ canonicalYMUniversalityClassEvidence

    ymL3ViaProductLattice :
      Bool

    ymL3ViaProductLatticeIsTrue :
      ymL3ViaProductLattice ≡ true

    ymL3ViaProductLatticeInheritedFromBalabanGivenUniversalityClass :
      Bool

    ymL3ViaProductLatticeInheritedFromBalabanGivenUniversalityClassIsTrue :
      ymL3ViaProductLatticeInheritedFromBalabanGivenUniversalityClass ≡ true

    universalityClassPromoted :
      Bool

    universalityClassPromotedIsFalse :
      universalityClassPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    openObligations :
      List YMUniversalityClassOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMUniversalityClassOpenObligations

    promotionFlags :
      List YMUniversalityClassPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMUniversalityClassReceipt public

canonicalYMUniversalityClassReceipt :
  YMUniversalityClassReceipt
canonicalYMUniversalityClassReceipt =
  record
    { status =
        productLatticeWilsonSUNCandidateOnly
    ; phase2ReframeReceipt =
        Phase2.canonicalManagerCClayReframeReceipt
    ; phase2ProductLatticeBalabanRouteRecorded =
        refl
    ; phase2UniversalityClassStillUnsettled =
        refl
    ; balabanReceipt =
        Balaban.canonicalBalabanRGMassGapReceiptSurface
    ; balabanContinuumPromotionStillFalse =
        Balaban.BalabanRGMassGapReceiptSurface.continuumMassGapPromotedByDASHIIsFalse
          Balaban.canonicalBalabanRGMassGapReceiptSurface
    ; b4BetaReceipt =
        B4.canonicalBetaCriticalReceipt
    ; b4StandardWilsonTrajectoryRecorded =
        B4.BetaCriticalReceipt.standardWilsonContinuumLimitRequiresBetaToInfinityIsTrue
          B4.canonicalBetaCriticalReceipt
    ; productLatticeCandidate =
        productLatticeCandidateLabel
    ; productLatticeCandidateIsCanonical =
        refl
    ; candidateUniversalityClass =
        standardWilsonUniversalityClassLabel
    ; candidateUniversalityClassIsCanonical =
        refl
    ; sameGaugeGroupEvidence =
        true
    ; sameGaugeGroupEvidenceIsTrue =
        refl
    ; oneLoopBetaEvidenceFromB4 =
        true
    ; oneLoopBetaEvidenceFromB4IsTrue =
        refl
    ; oneLoopBetaEvidenceLabel =
        oneLoopBetaB4Label
    ; oneLoopBetaEvidenceLabelIsCanonical =
        refl
    ; reflectionPositivityEvidence =
        true
    ; reflectionPositivityEvidenceIsTrue =
        refl
    ; continuumO4AfterAnisotropyDecaysEvidence =
        true
    ; continuumO4AfterAnisotropyDecaysEvidenceIsTrue =
        refl
    ; karsch1982AnisotropicLatticeAuthority =
        karsch1982AuthorityLabel
    ; karsch1982AnisotropicLatticeAuthorityIsCanonical =
        refl
    ; candidateEvidence =
        canonicalYMUniversalityClassEvidence
    ; candidateEvidenceIsCanonical =
        refl
    ; ymL3ViaProductLattice =
        true
    ; ymL3ViaProductLatticeIsTrue =
        refl
    ; ymL3ViaProductLatticeInheritedFromBalabanGivenUniversalityClass =
        true
    ; ymL3ViaProductLatticeInheritedFromBalabanGivenUniversalityClassIsTrue =
        refl
    ; universalityClassPromoted =
        false
    ; universalityClassPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; openObligations =
        canonicalYMUniversalityClassOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The 4D product lattice is recorded as a candidate in the standard Wilson SU(N) Yang-Mills universality class"
        ∷ "Evidence recorded: same gauge group, one-loop beta via B4, reflection positivity, and restoration of continuum O(4) after anisotropy decays"
        ∷ "Karsch 1982 is the citation authority for anisotropic lattice YM couplings"
        ∷ "ymL3ViaProductLattice is inherited from Balaban only conditional on the universality-class hypothesis"
        ∷ "The universality class remains candidate-only; no Clay, continuum mass-gap, or terminal promotion is introduced"
        ∷ []
    }

ymUniversalityClassCandidateOnly :
  universalityClassPromoted canonicalYMUniversalityClassReceipt
  ≡
  false
ymUniversalityClassCandidateOnly =
  refl

ymUniversalityClassNoClayPromotion :
  clayYangMillsPromoted canonicalYMUniversalityClassReceipt
  ≡
  false
ymUniversalityClassNoClayPromotion =
  refl

ymL3ViaProductLatticeReceiptRecorded :
  ymL3ViaProductLattice canonicalYMUniversalityClassReceipt
  ≡
  true
ymL3ViaProductLatticeReceiptRecorded =
  refl

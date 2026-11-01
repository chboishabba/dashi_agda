module DASHI.Physics.Closure.WaldGRAuthorityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ContractedBianchiMatterClosure as BianchiMatter
import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as GRB
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as NFScalar

------------------------------------------------------------------------
-- Wald GR authority boundary for Gate 4.
--
-- This receipt records Wald, General Relativity (1984), as an external
-- continuum GR authority for the standard Levi-Civita uniqueness theorem and
-- the sourced Einstein equation boundary.  It consumes the strongest current
-- finite Gate 4 sourced-Einstein compatibility receipt, but does not promote
-- that finite receipt to a continuum theorem or a sourced physical GR claim.

data WaldGRAuthorityStatus : Set where
  waldContinuumAuthorityRecordedFailClosed :
    WaldGRAuthorityStatus

data WaldGRAuthorityScope : Set where
  waldLeviCivitaUniquenessScope :
    WaldGRAuthorityScope
  waldSourcedEinsteinEquationScope :
    WaldGRAuthorityScope
  waldStressEnergyConservationBoundaryScope :
    WaldGRAuthorityScope
  finiteGate4CompatibilityConsumptionScope :
    WaldGRAuthorityScope

canonicalWaldGRAuthorityScopes :
  List WaldGRAuthorityScope
canonicalWaldGRAuthorityScopes =
  waldLeviCivitaUniquenessScope
  ∷ waldSourcedEinsteinEquationScope
  ∷ waldStressEnergyConservationBoundaryScope
  ∷ finiteGate4CompatibilityConsumptionScope
  ∷ []

data WaldGRContinuumPromotionBlocker : Set where
  missingContinuumSmoothManifoldModel :
    WaldGRContinuumPromotionBlocker
  missingContinuumLorentzianMetricAuthority :
    WaldGRContinuumPromotionBlocker
  missingSelectedNonFlatLeviCivitaInternalProof :
    WaldGRContinuumPromotionBlocker
  missingAuthorityBackedStressEnergyTensor :
    WaldGRContinuumPromotionBlocker
  missingContinuumEinsteinEquationDerivation :
    WaldGRContinuumPromotionBlocker

canonicalWaldGRContinuumPromotionBlockers :
  List WaldGRContinuumPromotionBlocker
canonicalWaldGRContinuumPromotionBlockers =
  missingContinuumSmoothManifoldModel
  ∷ missingContinuumLorentzianMetricAuthority
  ∷ missingSelectedNonFlatLeviCivitaInternalProof
  ∷ missingAuthorityBackedStressEnergyTensor
  ∷ missingContinuumEinsteinEquationDerivation
  ∷ []

data AcceptedContinuumGRAuthorityToken : Set where

acceptedContinuumGRAuthorityTokenImpossibleHere :
  AcceptedContinuumGRAuthorityToken →
  ⊥
acceptedContinuumGRAuthorityTokenImpossibleHere ()

record WaldGRAuthorityReceipt : Setω where
  field
    status :
      WaldGRAuthorityStatus

    authorityTitle :
      String

    authorityTitleIsWald :
      authorityTitle ≡ "General Relativity"

    authorityAuthor :
      String

    authorityAuthorIsWald :
      authorityAuthor ≡ "Robert M. Wald"

    authorityYear :
      String

    authorityYearIs1984 :
      authorityYear ≡ "1984"

    authorityPublisher :
      String

    authorityPublisherIsChicago :
      authorityPublisher ≡ "University of Chicago Press"

    leviCivitaUniquenessAuthorityText :
      String

    leviCivitaUniquenessAuthorityTextIsCanonical :
      leviCivitaUniquenessAuthorityText
      ≡
      "Wald General Relativity (1984): torsion-free metric-compatible connection is the unique Levi-Civita connection"

    sourcedEinsteinBoundaryText :
      String

    sourcedEinsteinBoundaryTextIsCanonical :
      sourcedEinsteinBoundaryText
      ≡
      "Wald General Relativity (1984): sourced Einstein equation boundary G_munu = 8pi T_munu"

    authorityScopes :
      List WaldGRAuthorityScope

    authorityScopesAreCanonical :
      authorityScopes ≡ canonicalWaldGRAuthorityScopes

    selectedFourChartLeviCivitaBianchiEinsteinStaging :
      NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt

    selectedFourChartNoSourcedEinsteinPromotion :
      NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.noSourcedEinsteinPromotion
        selectedFourChartLeviCivitaBianchiEinsteinStaging
      ≡
      true

    selectedLeviCivitaDependencyReceipt :
      GRB.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt

    selectedConnectionLeviCivitaDependencyAvailableIsFalse :
      GRB.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.selectedConnectionLeviCivitaDependencyAvailable
        selectedLeviCivitaDependencyReceipt
      ≡
      false

    selectedConnectionDependencyBlockerIsLeviCivita :
      GRB.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlocker
        selectedLeviCivitaDependencyReceipt
      ≡
      GRB.missingCarrierConnectionIsLeviCivita

    finiteSourcedEinsteinCompatibility :
      BianchiMatter.SourcedEinsteinCompatibilityReceipt

    finiteCompatibilityRecorded :
      BianchiMatter.SourcedEinsteinCompatibilityReceipt.finiteCompatibilityRecorded
        finiteSourcedEinsteinCompatibility
      ≡
      true

    finiteSourcedEinsteinTarget :
      BianchiMatter.SourcedEinsteinCompatibilityReceipt.sourcedEinsteinEquationTarget
        finiteSourcedEinsteinCompatibility
      ≡
      "G^munu = 8pi T^munu_YM"

    finiteSourcedEinsteinCompatibilityPromotedIsFalse :
      BianchiMatter.SourcedEinsteinCompatibilityReceipt.sourcedEinsteinCompatibilityPromoted
        finiteSourcedEinsteinCompatibility
      ≡
      false

    w4MatterStressEnergyInterfaceStillImpossible :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    continuumPromotionBlockers :
      List WaldGRContinuumPromotionBlocker

    continuumPromotionBlockersAreCanonical :
      continuumPromotionBlockers
      ≡
      canonicalWaldGRContinuumPromotionBlockers

    acceptedContinuumAuthorityConstructedHere :
      Bool

    acceptedContinuumAuthorityConstructedHereIsFalse :
      acceptedContinuumAuthorityConstructedHere ≡ false

    continuumLeviCivitaPromoted :
      Bool

    continuumLeviCivitaPromotedIsFalse :
      continuumLeviCivitaPromoted ≡ false

    continuumSourcedEinsteinPromoted :
      Bool

    continuumSourcedEinsteinPromotedIsFalse :
      continuumSourcedEinsteinPromoted ≡ false

    acceptedContinuumAuthorityTokenBlocked :
      AcceptedContinuumGRAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open WaldGRAuthorityReceipt public

canonicalWaldGRAuthorityReceipt :
  WaldGRAuthorityReceipt
canonicalWaldGRAuthorityReceipt =
  record
    { status =
        waldContinuumAuthorityRecordedFailClosed
    ; authorityTitle =
        "General Relativity"
    ; authorityTitleIsWald =
        refl
    ; authorityAuthor =
        "Robert M. Wald"
    ; authorityAuthorIsWald =
        refl
    ; authorityYear =
        "1984"
    ; authorityYearIs1984 =
        refl
    ; authorityPublisher =
        "University of Chicago Press"
    ; authorityPublisherIsChicago =
        refl
    ; leviCivitaUniquenessAuthorityText =
        "Wald General Relativity (1984): torsion-free metric-compatible connection is the unique Levi-Civita connection"
    ; leviCivitaUniquenessAuthorityTextIsCanonical =
        refl
    ; sourcedEinsteinBoundaryText =
        "Wald General Relativity (1984): sourced Einstein equation boundary G_munu = 8pi T_munu"
    ; sourcedEinsteinBoundaryTextIsCanonical =
        refl
    ; authorityScopes =
        canonicalWaldGRAuthorityScopes
    ; authorityScopesAreCanonical =
        refl
    ; selectedFourChartLeviCivitaBianchiEinsteinStaging =
        NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; selectedFourChartNoSourcedEinsteinPromotion =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.noSourcedEinsteinPromotionIsTrue
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; selectedLeviCivitaDependencyReceipt =
        GRB.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; selectedConnectionLeviCivitaDependencyAvailableIsFalse =
        GRB.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.selectedConnectionLeviCivitaDependencyAvailableIsFalse
          GRB.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; selectedConnectionDependencyBlockerIsLeviCivita =
        GRB.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlockerIsCarrierConnectionLeviCivita
          GRB.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; finiteSourcedEinsteinCompatibility =
        BianchiMatter.canonicalSourcedEinsteinCompatibilityReceipt
    ; finiteCompatibilityRecorded =
        BianchiMatter.sourcedEinsteinCompatibilityFiniteRecorded
    ; finiteSourcedEinsteinTarget =
        BianchiMatter.SourcedEinsteinCompatibilityReceipt.sourcedEinsteinEquationTargetIsRequested
          BianchiMatter.canonicalSourcedEinsteinCompatibilityReceipt
    ; finiteSourcedEinsteinCompatibilityPromotedIsFalse =
        BianchiMatter.sourcedEinsteinCompatibilityStillFailClosed
    ; w4MatterStressEnergyInterfaceStillImpossible =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; continuumPromotionBlockers =
        canonicalWaldGRContinuumPromotionBlockers
    ; continuumPromotionBlockersAreCanonical =
        refl
    ; acceptedContinuumAuthorityConstructedHere =
        false
    ; acceptedContinuumAuthorityConstructedHereIsFalse =
        refl
    ; continuumLeviCivitaPromoted =
        false
    ; continuumLeviCivitaPromotedIsFalse =
        refl
    ; continuumSourcedEinsteinPromoted =
        false
    ; continuumSourcedEinsteinPromotedIsFalse =
        refl
    ; acceptedContinuumAuthorityTokenBlocked =
        acceptedContinuumGRAuthorityTokenImpossibleHere
    ; receiptBoundary =
        "Wald General Relativity (1984) is recorded as the external continuum authority for Levi-Civita uniqueness and the sourced Einstein equation boundary"
        ∷ "The selected four-chart finite receipt stages a local zero-table Levi-Civita/Bianchi/Einstein surface, but explicitly records no sourced Einstein promotion"
        ∷ "The Gate 4 selected-connection dependency remains blocked at missingCarrierConnectionIsLeviCivita"
        ∷ "The existing finite sourced-Einstein compatibility receipt is consumed as canonical and records G^munu = 8pi T^munu_YM only as a finite fail-closed target"
        ∷ "No W4 matter/stress-energy interface receipt, accepted continuum authority token, continuum Levi-Civita theorem, or continuum sourced Einstein theorem is constructed here"
        ∷ []
    }

waldGRAuthorityConsumesFiniteSourcedCompatibility :
  BianchiMatter.SourcedEinsteinCompatibilityReceipt.finiteCompatibilityRecorded
    (finiteSourcedEinsteinCompatibility canonicalWaldGRAuthorityReceipt)
  ≡
  true
waldGRAuthorityConsumesFiniteSourcedCompatibility =
  finiteCompatibilityRecorded canonicalWaldGRAuthorityReceipt

waldGRAuthorityContinuumLeviCivitaStillFailClosed :
  continuumLeviCivitaPromoted canonicalWaldGRAuthorityReceipt
  ≡
  false
waldGRAuthorityContinuumLeviCivitaStillFailClosed =
  refl

waldGRAuthorityContinuumSourcedEinsteinStillFailClosed :
  continuumSourcedEinsteinPromoted canonicalWaldGRAuthorityReceipt
  ≡
  false
waldGRAuthorityContinuumSourcedEinsteinStillFailClosed =
  refl

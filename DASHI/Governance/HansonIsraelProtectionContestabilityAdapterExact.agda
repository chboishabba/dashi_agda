module DASHI.Governance.HansonIsraelProtectionContestabilityAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ProtectionVocabularyUniversalContestabilityNoncollapseExact as Protection
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.HansonIsraelJewishPluralitySurveillanceGrammarExact as Existing
import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as Panopticon
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Palantir

------------------------------------------------------------------------
-- ADAPTER: HANSON / JEWISH-PLURALITY / PALANTIR INTO GENERIC PROTECTION OWNER
------------------------------------------------------------------------

genericProtectionBoundary : Protection.ProtectionVocabularyBoundary
genericProtectionBoundary = Protection.canonicalProtectionVocabularyBoundary

existingApplicationBoundary : Existing.HansonIsraelJewishSurveillanceBoundary
existingApplicationBoundary =
  Existing.canonicalHansonIsraelJewishSurveillanceBoundary

antiPanopticonBoundary : Panopticon.AntiPanopticonBoundary
antiPanopticonBoundary = Panopticon.canonicalAntiPanopticonBoundary

palantirCapabilityBoundary : Palantir.PalantirCapabilityBoundary
palantirCapabilityBoundary = Palantir.canonicalPalantirCapabilityBoundary

------------------------------------------------------------------------
-- Hanson/community-protection adapter.
------------------------------------------------------------------------

data HansonProtectionState : Set where
  universalMinorityGrammar : HansonProtectionState
  selectiveMinorityGrammar : HansonProtectionState

data HansonProtectionSurface : Set where
  protectCommunityFromHatred : HansonProtectionSurface

data HansonProtectionOutcome : Set where
  universalMinorityRouting : HansonProtectionOutcome
  selectiveMinorityRouting : HansonProtectionOutcome

hansonProtectionObserver : HansonProtectionState → HansonProtectionSurface
hansonProtectionObserver universalMinorityGrammar = protectCommunityFromHatred
hansonProtectionObserver selectiveMinorityGrammar = protectCommunityFromHatred

hansonProtectionOutcome : HansonProtectionState → HansonProtectionOutcome
hansonProtectionOutcome universalMinorityGrammar = universalMinorityRouting
hansonProtectionOutcome selectiveMinorityGrammar = selectiveMinorityRouting

hansonProtectionOutcomeDiffers :
  hansonProtectionOutcome universalMinorityGrammar
  ≡ hansonProtectionOutcome selectiveMinorityGrammar → ⊥
hansonProtectionOutcomeDiffers ()

hansonCommunitySafetyDoesNotDetermineUniversalism :
  INF.FactorsThrough hansonProtectionObserver hansonProtectionOutcome → ⊥
hansonCommunitySafetyDoesNotDetermineUniversalism =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      universalMinorityGrammar
      selectiveMinorityGrammar
      refl
      hansonProtectionOutcomeDiffers)

------------------------------------------------------------------------
-- Palantir/security adapter.
------------------------------------------------------------------------

data PalantirSecurityState : Set where
  securityWithSubjectContestability : PalantirSecurityState
  securityWithoutSubjectContestability : PalantirSecurityState

data PalantirSecuritySurface : Set where
  integratedSecurityCapability : PalantirSecuritySurface

data PalantirContestabilityOutcome : Set where
  inspectionCorrectionAppealInstalled : PalantirContestabilityOutcome
  inspectionCorrectionAppealMissing : PalantirContestabilityOutcome

palantirSecurityObserver :
  PalantirSecurityState → PalantirSecuritySurface
palantirSecurityObserver securityWithSubjectContestability =
  integratedSecurityCapability
palantirSecurityObserver securityWithoutSubjectContestability =
  integratedSecurityCapability

palantirContestabilityOutcome :
  PalantirSecurityState → PalantirContestabilityOutcome
palantirContestabilityOutcome securityWithSubjectContestability =
  inspectionCorrectionAppealInstalled
palantirContestabilityOutcome securityWithoutSubjectContestability =
  inspectionCorrectionAppealMissing

palantirContestabilityDiffers :
  palantirContestabilityOutcome securityWithSubjectContestability
  ≡ palantirContestabilityOutcome securityWithoutSubjectContestability → ⊥
palantirContestabilityDiffers ()

palantirSecurityCapabilityDoesNotDetermineContestability :
  INF.FactorsThrough
    palantirSecurityObserver
    palantirContestabilityOutcome → ⊥
palantirSecurityCapabilityDoesNotDetermineContestability =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      securityWithSubjectContestability
      securityWithoutSubjectContestability
      refl
      palantirContestabilityDiffers)

------------------------------------------------------------------------
-- Direct regressions to current installed boundaries.
------------------------------------------------------------------------

palantirSubjectContestabilityNotInstalled :
  Palantir.PalantirCapabilityBoundary.subjectInspectionCorrectionAppealInstalled
    palantirCapabilityBoundary
  ≡ false
palantirSubjectContestabilityNotInstalled = refl

panopticonObservationDoesNotCreateAuthority :
  Panopticon.AntiPanopticonBoundary.observationCreatesInterventionAuthority
    antiPanopticonBoundary
  ≡ false
panopticonObservationDoesNotCreateAuthority = refl

existingTriadicNetworkStillNotConstructed :
  Existing.HansonIsraelJewishSurveillanceBoundary.hansonSegalPalantirNetworkConstructed
    existingApplicationBoundary
  ≡ false
existingTriadicNetworkStillNotConstructed = refl

existingUniversalMinorityProtectionStillNotAutoPaid :
  Existing.HansonIsraelJewishSurveillanceBoundary.universalMinorityProtectionAutomaticallyPaid
    existingApplicationBoundary
  ≡ false
existingUniversalMinorityProtectionStillNotAutoPaid = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ProtectionContestabilityAdapterBoundary : Set where
  constructor protection-contestability-adapter-boundary
  field
    genericProtectionOwnerReused : Bool
    hansonUniversalismResidualRetained : Bool
    palantirContestabilityResidualRetained : Bool
    antiPanopticonAuthorityBoundaryRetained : Bool
    triadicNetworkStillUnconstructed : Bool
    vocabularyCreatesUniversalism : Bool
    vocabularyCreatesUniversalismIsFalse :
      vocabularyCreatesUniversalism ≡ false
    securityCapabilityCreatesContestability : Bool
    securityCapabilityCreatesContestabilityIsFalse :
      securityCapabilityCreatesContestability ≡ false

open ProtectionContestabilityAdapterBoundary public

canonicalProtectionContestabilityAdapterBoundary :
  ProtectionContestabilityAdapterBoundary
canonicalProtectionContestabilityAdapterBoundary =
  protection-contestability-adapter-boundary
    true true true true true
    false refl
    false refl

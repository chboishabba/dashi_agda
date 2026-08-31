module DASHI.Culture.RastafariItalIndigenousIntersectionalBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.RastafariItalLivityExact as Ital

------------------------------------------------------------------------
-- ITAL / INDIGENOUS / INTERSECTIONAL CROSS-POLLINATION BOUNDARY
--
-- This module deliberately does NOT identify Rastafari Ital livity with any
-- Indigenous knowledge tradition.  It reuses two merged structural lessons:
--
-- 1. Kimmerer / Two-Eyed Seeing bridge:
--      shared ecological observation != same knowledge provenance.
-- 2. Crenshaw-inspired DASHI non-factorability:
--      a flattened single-axis surface need not recover situated relations,
--      power or other hidden coordinates; recharting cannot restore what the
--      coarse observer already erased.
--
-- The finite carriers below are repository-native comparison fixtures, not
-- empirical descriptions of Rastafari or Indigenous communities.
------------------------------------------------------------------------

data PracticeHistory : Set where
  rastafariItalHistory
  indigenousKnowledgeHistory
  scientificManagementHistory
  : PracticeHistory

data SharedPracticeSurface : Set where
  ecologicalCareSurface : SharedPracticeSurface

data AuthorityPosition : Set where
  communityCustodialAuthority
  householdPracticeAuthority
  institutionalTechnicalAuthority
  : AuthorityPosition

data PermissionPosition : Set where
  communityGovernedPermission
  practitionerPermission
  institutionalPermission
  : PermissionPosition

data ObligationPosition : Set where
  reciprocalCareObligation
  livityPracticeObligation
  reportingComplianceObligation
  : ObligationPosition

data PowerPosition : Set where
  lowInstitutionalPower highInstitutionalPower : PowerPosition

record SituatedEcologicalPractice : Set where
  constructor situatedEcologicalPractice
  field
    history : PracticeHistory
    surface : SharedPracticeSurface
    authority : AuthorityPosition
    permission : PermissionPosition
    obligation : ObligationPosition
    power : PowerPosition

open SituatedEcologicalPractice public

italPractice : SituatedEcologicalPractice
italPractice =
  situatedEcologicalPractice
    rastafariItalHistory
    ecologicalCareSurface
    householdPracticeAuthority
    practitionerPermission
    livityPracticeObligation
    lowInstitutionalPower

indigenousFixture : SituatedEcologicalPractice
indigenousFixture =
  situatedEcologicalPractice
    indigenousKnowledgeHistory
    ecologicalCareSurface
    communityCustodialAuthority
    communityGovernedPermission
    reciprocalCareObligation
    lowInstitutionalPower

institutionalFixture : SituatedEcologicalPractice
institutionalFixture =
  situatedEcologicalPractice
    scientificManagementHistory
    ecologicalCareSurface
    institutionalTechnicalAuthority
    institutionalPermission
    reportingComplianceObligation
    highInstitutionalPower

------------------------------------------------------------------------
-- Same visible ecological-care surface does not recover cultural history or
-- governance coordinates.
------------------------------------------------------------------------

sameSurfaceItalIndigenous : surface italPractice ≡ surface indigenousFixture
sameSurfaceItalIndigenous = refl

sameSurfaceItalInstitutional : surface italPractice ≡ surface institutionalFixture
sameSurfaceItalInstitutional = refl

surfaceCannotRecoverHistory :
  NonFactor.FactorsThrough surface history → ⊥
surfaceCannotRecoverHistory =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      italPractice
      indigenousFixture
      refl
      (λ ()))

surfaceCannotRecoverAuthority :
  NonFactor.FactorsThrough surface authority → ⊥
surfaceCannotRecoverAuthority =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      italPractice
      indigenousFixture
      refl
      (λ ()))

surfaceCannotRecoverPermission :
  NonFactor.FactorsThrough surface permission → ⊥
surfaceCannotRecoverPermission =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      italPractice
      indigenousFixture
      refl
      (λ ()))

surfaceCannotRecoverObligation :
  NonFactor.FactorsThrough surface obligation → ⊥
surfaceCannotRecoverObligation =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      italPractice
      indigenousFixture
      refl
      (λ ()))

surfaceCannotRecoverPower :
  NonFactor.FactorsThrough surface power → ⊥
surfaceCannotRecoverPower =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      italPractice
      institutionalFixture
      refl
      (λ ()))

------------------------------------------------------------------------
-- Recharting a flattened ecological-care label cannot repair lost power.
------------------------------------------------------------------------

rechartingCareSurfaceCannotRecoverPower :
  ∀ {Recharted : Set} →
  (rechart : SharedPracticeSurface → Recharted) →
  NonFactor.FactorsThrough (λ practice → rechart (surface practice)) power → ⊥
rechartingCareSurfaceCannotRecoverPower rechart =
  NonFactor.rechartingCannotRecoverErasedPhenomenon
    rechart
    (NonFactor.nonFactorabilityWitness
      italPractice
      institutionalFixture
      refl
      (λ ()))

------------------------------------------------------------------------
-- Direct reuse of the merged Two-Eyed Seeing boundary.
------------------------------------------------------------------------

sharedEcologicalObservationStillDoesNotRecoverKnowledgeProvenance :
  NonFactor.FactorsThrough
    TwoEyed.observeKnowledgeHistory
    TwoEyed.provenance → ⊥
sharedEcologicalObservationStillDoesNotRecoverKnowledgeProvenance =
  TwoEyed.sharedObservationDoesNotRecoverProvenance

------------------------------------------------------------------------
-- No-promotion boundaries.
------------------------------------------------------------------------

data ItalIsIndigenousKnowledgeTradition : Set where

data SharedCareVocabularyMeansSharedAuthority : Set where

data SharedReciprocityLanguageMeansSharedObligation : Set where

data EcologicalSimilarityErasesPowerDifference : Set where

data IntersectionalAnalysisMeansCulturalEquivalence : Set where

italIsNotIdentifiedWithIndigenousKnowledge :
  ItalIsIndigenousKnowledgeTradition → ⊥
italIsNotIdentifiedWithIndigenousKnowledge ()

sharedCareVocabularyDoesNotProveSharedAuthority :
  SharedCareVocabularyMeansSharedAuthority → ⊥
sharedCareVocabularyDoesNotProveSharedAuthority ()

sharedReciprocityLanguageDoesNotProveSharedObligation :
  SharedReciprocityLanguageMeansSharedObligation → ⊥
sharedReciprocityLanguageDoesNotProveSharedObligation ()

ecologicalSimilarityDoesNotErasePowerDifference :
  EcologicalSimilarityErasesPowerDifference → ⊥
ecologicalSimilarityDoesNotErasePowerDifference ()

intersectionalAnalysisDoesNotCreateCulturalEquivalence :
  IntersectionalAnalysisMeansCulturalEquivalence → ⊥
intersectionalAnalysisDoesNotCreateCulturalEquivalence ()

------------------------------------------------------------------------
-- Retain the existing Ital source boundary too.
------------------------------------------------------------------------

italStillDoesNotAutoIdentifyWithPermaculture :
  Ital.ItalIsIdenticalToPermaculture → ⊥
italStillDoesNotAutoIdentifyWithPermaculture =
  Ital.italIsNotAutoIdentifiedWithPermaculture

record ItalIndigenousIntersectionalBoundary : Set where
  constructor italIndigenousIntersectionalBoundary
  field
    sharedEcologicalSurfaceMeansSharedHistory : Bool
    sharedEcologicalSurfaceMeansSharedHistoryIsFalse :
      sharedEcologicalSurfaceMeansSharedHistory ≡ false

    sharedEcologicalSurfaceMeansSharedAuthority : Bool
    sharedEcologicalSurfaceMeansSharedAuthorityIsFalse :
      sharedEcologicalSurfaceMeansSharedAuthority ≡ false

    sharedEcologicalSurfaceMeansSharedPower : Bool
    sharedEcologicalSurfaceMeansSharedPowerIsFalse :
      sharedEcologicalSurfaceMeansSharedPower ≡ false

    structuralCrossPollinationMeansCulturalIdentity : Bool
    structuralCrossPollinationMeansCulturalIdentityIsFalse :
      structuralCrossPollinationMeansCulturalIdentity ≡ false

    richerSituatedCarrierIsRequired : Bool
    richerSituatedCarrierIsRequiredIsTrue :
      richerSituatedCarrierIsRequired ≡ true

canonicalItalIndigenousIntersectionalBoundary :
  ItalIndigenousIntersectionalBoundary
canonicalItalIndigenousIntersectionalBoundary =
  italIndigenousIntersectionalBoundary
    false refl
    false refl
    false refl
    false refl
    true refl

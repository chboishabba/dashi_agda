module DASHI.Culture.ReligiousPowerChildFearClaimBidiExact where

------------------------------------------------------------------------
-- RELIGIOUS-POWER / CHILD-FEAR CLAIM AUDIT
--
-- This is a repository-native BIDI claim-separation owner.  It does NOT
-- certify the truth of the historical or metaphysical assertions represented
-- below.  Its purpose is to prevent a rhetorically unified narrative from
-- silently collapsing distinct empirical, historical, theological,
-- metaphorical and metaphysical obligations into one claim.
--
-- Existing repository owners consumed structurally:
--   * ParentalFearIndependentMobilityExact: fear can regulate behaviour while
--     remaining situated, multi-fibre and observer-bounded.
--   * RepresentationSubjectPositionNonfactorabilityExact: a public
--     representation does not generically recover originating subject-position.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Biology.ParentalFearIndependentMobilityExact as Fear

------------------------------------------------------------------------
-- Claim kinds remain disjoint.  A single sentence may contain several, but
-- evidence admissible for one kind is not thereby evidence for every kind.
------------------------------------------------------------------------

data ClaimKind : Set where
  historicalClaim : ClaimKind
  archaeologicalClaim : ClaimKind
  textualClaim : ClaimKind
  theologicalInterpretation : ClaimKind
  institutionalClaim : ClaimKind
  psychologicalClaim : ClaimKind
  causalClaim : ClaimKind
  metaphoricalClaim : ClaimKind
  metaphysicalClaim : ClaimKind
  groupGeneralisation : ClaimKind

historicalNotMetaphysical : historicalClaim ≡ metaphysicalClaim → ⊥
historicalNotMetaphysical ()

psychologicalNotMetaphysical : psychologicalClaim ≡ metaphysicalClaim → ⊥
psychologicalNotMetaphysical ()

theologyNotInstitution : theologicalInterpretation ≡ institutionalClaim → ⊥
theologyNotInstitution ()

groupGeneralisationNotHistorical : groupGeneralisation ≡ historicalClaim → ⊥
groupGeneralisationNotHistorical ()

------------------------------------------------------------------------
-- Evidence status is not Boolean.  In particular, an unverified assertion is
-- not converted into its negation, while a supported neighbouring claim does
-- not promote an unsupported stronger claim.
------------------------------------------------------------------------

data EvidenceStatus : Set where
  supportedWithinScope : EvidenceStatus
  contested : EvidenceStatus
  unresolved : EvidenceStatus
  unsupportedHere : EvidenceStatus
  notEmpiricallyTestableHere : EvidenceStatus

supportedNotUnsupported : supportedWithinScope ≡ unsupportedHere → ⊥
supportedNotUnsupported ()

unresolvedNotSupported : unresolved ≡ supportedWithinScope → ⊥
unresolvedNotSupported ()

------------------------------------------------------------------------
-- Decompose the narrative into independently auditable atoms.
------------------------------------------------------------------------

data ClaimAtom : Set where
  ancientNearEasternReligiousInteraction : ClaimAtom
  sacrificePracticeInSomeAncientContexts : ClaimAtom
  religiousInstitutionsCanExerciseSocialPower : ClaimAtom
  fearOfPunishmentCanRegulateBehaviour : ClaimAtom
  religiousIdeasCanParticipateInSubjectFormation : ClaimAtom
  religiousTraditionsCanEncodeGenderHierarchy : ClaimAtom
  allAbrahamicReligionIsOneHiddenCult : ClaimAtom
  contemporaryChurchesHarvestLiteralPsychicEnergy : ClaimAtom
  warsAreSecretlyConductedAsBloodSacrifice : ClaimAtom
  wholeReligiousGroupsCommitRitualChildAbuse : ClaimAtom
  demonicEntityRewardsElitesForWorship : ClaimAtom

claimKind : ClaimAtom → ClaimKind
claimKind ancientNearEasternReligiousInteraction = historicalClaim
claimKind sacrificePracticeInSomeAncientContexts = archaeologicalClaim
claimKind religiousInstitutionsCanExerciseSocialPower = institutionalClaim
claimKind fearOfPunishmentCanRegulateBehaviour = psychologicalClaim
claimKind religiousIdeasCanParticipateInSubjectFormation = causalClaim
claimKind religiousTraditionsCanEncodeGenderHierarchy = historicalClaim
claimKind allAbrahamicReligionIsOneHiddenCult = groupGeneralisation
claimKind contemporaryChurchesHarvestLiteralPsychicEnergy = metaphysicalClaim
claimKind warsAreSecretlyConductedAsBloodSacrifice = causalClaim
claimKind wholeReligiousGroupsCommitRitualChildAbuse = groupGeneralisation
claimKind demonicEntityRewardsElitesForWorship = metaphysicalClaim

------------------------------------------------------------------------
-- Promotion requires an explicit bridge.  Merely sharing narrative adjacency
-- is deliberately insufficient.
------------------------------------------------------------------------

record PromotionReceipt (from to : ClaimAtom) : Set where
  constructor promotion-receipt
  field
    sourceStatus : EvidenceStatus
    targetStatus : EvidenceStatus
    scopePreserved : Bool
    scopePreservedIsTrue : scopePreserved ≡ true
    inferentialBridge : String
    evidenceProvenance : String

open PromotionReceipt public

record NoAutomaticPromotionBoundary : Set where
  constructor no-automatic-promotion-boundary
  field
    ancientInteractionImpliesHiddenCult : Bool
    ancientInteractionImpliesHiddenCultIsFalse :
      ancientInteractionImpliesHiddenCult ≡ false
    ancientSacrificeImpliesModernGroupPractice : Bool
    ancientSacrificeImpliesModernGroupPracticeIsFalse :
      ancientSacrificeImpliesModernGroupPractice ≡ false
    fearRegulationImpliesLiteralEnergyHarvest : Bool
    fearRegulationImpliesLiteralEnergyHarvestIsFalse :
      fearRegulationImpliesLiteralEnergyHarvest ≡ false
    symbolicBloodLanguageImpliesCannibalism : Bool
    symbolicBloodLanguageImpliesCannibalismIsFalse :
      symbolicBloodLanguageImpliesCannibalism ≡ false
    institutionalPowerImpliesSecretRitualCause : Bool
    institutionalPowerImpliesSecretRitualCauseIsFalse :
      institutionalPowerImpliesSecretRitualCause ≡ false
    genderHierarchyImpliesSingleOccultOrigin : Bool
    genderHierarchyImpliesSingleOccultOriginIsFalse :
      genderHierarchyImpliesSingleOccultOrigin ≡ false

canonicalNoAutomaticPromotionBoundary : NoAutomaticPromotionBoundary
canonicalNoAutomaticPromotionBoundary =
  no-automatic-promotion-boundary
    false refl false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- Child fear / authority BIDI carrier.
--
-- Forward: authority + threat representation can participate in behavioural
-- regulation / subject formation.
-- Reverse: observed fear, conformity or religious identity does not recover a
-- unique cause, private belief state, coercive mechanism or originating
-- subject-position.
------------------------------------------------------------------------

data FormationState : Set where
  authorityThreatRoute alternativeRoute : FormationState

data BehaviourSurface : Set where
  sameConformingSurface : BehaviourSurface

data FormationRoute : Set where
  authorityThreatFormation alternativeFormation : FormationRoute

behaviourSurface : FormationState → BehaviourSurface
behaviourSurface authorityThreatRoute = sameConformingSurface
behaviourSurface alternativeRoute = sameConformingSurface

formationRoute : FormationState → FormationRoute
formationRoute authorityThreatRoute = authorityThreatFormation
formationRoute alternativeRoute = alternativeFormation

formationRouteDiffers :
  formationRoute authorityThreatRoute ≡ formationRoute alternativeRoute → ⊥
formationRouteDiffers ()

behaviourCannotRecoverFormationRoute :
  INF.FactorsThrough behaviourSurface formationRoute → ⊥
behaviourCannotRecoverFormationRoute =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      authorityThreatRoute alternativeRoute refl formationRouteDiffers)

------------------------------------------------------------------------
-- Explicit reuse receipts: the present owner consumes the canonical fear
-- source and subject-position boundary rather than re-attributing their
-- theorems to religious studies.
------------------------------------------------------------------------

record CrossPollinationReceipt : Set where
  constructor cross-pollination-receipt
  field
    fearSource : Fear.ParentalFearIndependentMobilitySource
    fearSourceIsCanonical :
      fearSource ≡ Fear.canonicalParentalFearIndependentMobilitySource
    subjectBoundary : Subject.RepresentationSubjectPositionBoundary
    subjectBoundaryIsCanonical :
      subjectBoundary ≡ Subject.canonicalRepresentationSubjectPositionBoundary
    fearMechanismTransferredAsStructureOnly : Bool
    fearMechanismTransferredAsStructureOnlyIsTrue :
      fearMechanismTransferredAsStructureOnly ≡ true
    noReligiousEmpiricalClaimAttributedToFearPaper : Bool
    noReligiousEmpiricalClaimAttributedToFearPaperIsTrue :
      noReligiousEmpiricalClaimAttributedToFearPaper ≡ true
    noIrigarayTheoremMisattribution : Bool
    noIrigarayTheoremMisattributionIsTrue :
      noIrigarayTheoremMisattribution ≡ true

canonicalCrossPollinationReceipt : CrossPollinationReceipt
canonicalCrossPollinationReceipt =
  cross-pollination-receipt
    Fear.canonicalParentalFearIndependentMobilitySource refl
    Subject.canonicalRepresentationSubjectPositionBoundary refl
    true refl true refl true refl

------------------------------------------------------------------------
-- Metaphor / mechanism boundary.
------------------------------------------------------------------------

data ExplanatoryRegister : Set where
  socialMechanism : ExplanatoryRegister
  symbolicDescription : ExplanatoryRegister
  literalSupernaturalMechanism : ExplanatoryRegister

socialMechanismNotLiteralSupernatural :
  socialMechanism ≡ literalSupernaturalMechanism → ⊥
socialMechanismNotLiteralSupernatural ()

symbolicNotLiteralSupernatural :
  symbolicDescription ≡ literalSupernaturalMechanism → ⊥
symbolicNotLiteralSupernatural ()

record ReligiousPowerBidiBoundary : Set where
  constructor religious-power-bidi-boundary
  field
    observedFearRecoversUniqueDoctrine : Bool
    observedFearRecoversUniqueDoctrineIsFalse :
      observedFearRecoversUniqueDoctrine ≡ false
    observedConformityRecoversPrivateBelief : Bool
    observedConformityRecoversPrivateBeliefIsFalse :
      observedConformityRecoversPrivateBelief ≡ false
    institutionalBenefitProvesOccultExchange : Bool
    institutionalBenefitProvesOccultExchangeIsFalse :
      institutionalBenefitProvesOccultExchange ≡ false
    metaphoricalEgregoreProvesLiteralEntity : Bool
    metaphoricalEgregoreProvesLiteralEntityIsFalse :
      metaphoricalEgregoreProvesLiteralEntity ≡ false
    criticismOfDoctrineLicensesGroupAttribution : Bool
    criticismOfDoctrineLicensesGroupAttributionIsFalse :
      criticismOfDoctrineLicensesGroupAttribution ≡ false
    structuralFormalisationProvesHistoricalClaim : Bool
    structuralFormalisationProvesHistoricalClaimIsFalse :
      structuralFormalisationProvesHistoricalClaim ≡ false

canonicalReligiousPowerBidiBoundary : ReligiousPowerBidiBoundary
canonicalReligiousPowerBidiBoundary =
  religious-power-bidi-boundary
    false refl false refl false refl false refl false refl false refl

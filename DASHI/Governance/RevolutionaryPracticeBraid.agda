module DASHI.Governance.RevolutionaryPracticeBraid where

open import Agda.Primitive using (Setω)
open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.RelationalQiEducationTraumaBridge as Relational
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Culture.KnotWeaveTopologyCultureBridge as KnotWeave
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.LocalGlobalCouncilGluing as Gluing
import DASHI.Governance.RevolutionarySourceAtlas as Source
import DASHI.Interop.SweetgrassCarrierSpine as Sweetgrass
import DASHI.Reasoning.DialecticalDepthAccumulationReceipt as Dialectic
import DASHI.Reasoning.UnifiedCarryBraidReceipt as CarryBraid

------------------------------------------------------------------------
-- Revolutionary-practice braid.
--
-- The adjunct keeps institutional, relational, epistemic, ecological and
-- historical-trauma strands distinct while allowing typed cross-reference.
-- Braiding is not synthesis-by-collapse.  The module is a candidate practice
-- ecology, not a universal doctrine or source of political authority.
------------------------------------------------------------------------

data RevolutionaryPracticeStrand : Set where
  institutionalTransformationStrand : RevolutionaryPracticeStrand
  relationalTransformationStrand : RevolutionaryPracticeStrand
  epistemicTransformationStrand : RevolutionaryPracticeStrand
  ecologicalTransformationStrand : RevolutionaryPracticeStrand
  historicalTraumaTransformationStrand : RevolutionaryPracticeStrand

canonicalRevolutionaryPracticeStrands : List RevolutionaryPracticeStrand
canonicalRevolutionaryPracticeStrands =
  institutionalTransformationStrand
  ∷ relationalTransformationStrand
  ∷ epistemicTransformationStrand
  ∷ ecologicalTransformationStrand
  ∷ historicalTraumaTransformationStrand
  ∷ []

data RelationalFreedomDimension : Set where
  consentDimension : RelationalFreedomDimension
  autonomyDimension : RelationalFreedomDimension
  dependencyAndMaterialAsymmetryDimension : RelationalFreedomDimension
  obligationAndReciprocityDimension : RelationalFreedomDimension
  exitRecallRevisionDimension : RelationalFreedomDimension

canonicalRelationalFreedomDimensions : List RelationalFreedomDimension
canonicalRelationalFreedomDimensions =
  consentDimension
  ∷ autonomyDimension
  ∷ dependencyAndMaterialAsymmetryDimension
  ∷ obligationAndReciprocityDimension
  ∷ exitRecallRevisionDimension
  ∷ []

data PrefigurativePractice : Set where
  mutualAidPractice : PrefigurativePractice
  recallableDelegationPractice : PrefigurativePractice
  federationWithoutAbsorptionPractice : PrefigurativePractice
  consentAndReconsentPractice : PrefigurativePractice
  sharedCareLabourPractice : PrefigurativePractice
  ecologicalReciprocityPractice : PrefigurativePractice
  affectedVoicePractice : PrefigurativePractice
  reviewAndRepairPractice : PrefigurativePractice

canonicalPrefigurativePractices : List PrefigurativePractice
canonicalPrefigurativePractices =
  mutualAidPractice
  ∷ recallableDelegationPractice
  ∷ federationWithoutAbsorptionPractice
  ∷ consentAndReconsentPractice
  ∷ sharedCareLabourPractice
  ∷ ecologicalReciprocityPractice
  ∷ affectedVoicePractice
  ∷ reviewAndRepairPractice
  ∷ []

data PatternMindStatus : Set where
  repoLocalPatternMindRepairContext : PatternMindStatus

patternMindAttributionBoundary : String
patternMindAttributionBoundary =
  "PatternMind is retained as the repository's relational repair-context vocabulary; this module does not attach a speculative external authorship or doctrine."

record RelationalFreedomSurface : Set where
  constructor relationalFreedomSurface
  field
    dimensions : List RelationalFreedomDimension
    consentRequired : Bool
    exitCapacityRequired : Bool
    materialSecurityRequired : Bool
    voiceRequired : Bool
    reviewabilityRequired : Bool
    roleCategoryAloneCreatesEntitlement : Bool
    declaredConsentImpliesMaterialSymmetry : Bool
    relationshipLabelAlienatesAutonomy : Bool
    informalStructureImpliesEquality : Bool
    relationalModelCreatesEthicalAuthority : Bool

open RelationalFreedomSurface public

canonicalRelationalFreedomSurface : RelationalFreedomSurface
canonicalRelationalFreedomSurface =
  relationalFreedomSurface
    canonicalRelationalFreedomDimensions
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

record SummerOfLoveHistoricalBoundary : Set where
  constructor summerOfLoveHistoricalBoundary
  field
    relationalExperimentationRecorded : Bool
    antiWarAndCommunalPracticeRecorded : Bool
    artisticInfrastructureRecorded : Bool
    informalHierarchyRiskRecorded : Bool
    genderedCareLabourRiskRecorded : Bool
    racialAndClassExclusionRiskRecorded : Bool
    commodificationRiskRecorded : Bool
    conventionRemovalImpliesNonDomination : Bool
    sexualOpennessImpliesConsent : Bool
    communalLifeImpliesSharedLabour : Bool
    spontaneousPracticeCreatesPoliticalAuthority : Bool
    historicalOriginMythPromoted : Bool

open SummerOfLoveHistoricalBoundary public

canonicalSummerOfLoveHistoricalBoundary : SummerOfLoveHistoricalBoundary
canonicalSummerOfLoveHistoricalBoundary =
  summerOfLoveHistoricalBoundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

record MeansEndsSedimentationBoundary : Set where
  constructor meansEndsSedimentationBoundary
  field
    procedureIsInstitutionalInput : Bool
    ordinaryRelationPatternIsInstitutionalInput : Bool
    secrecyWithoutAccountabilityIsNeutral : Bool
    commandWithoutRecallIsNeutral : Bool
    permanentEmergencyIsNeutral : Bool
    charismaticExceptionIsNeutral : Bool
    suppressionInNameOfUnityIsNeutral : Bool
    formalVictoryGuaranteesLiberatoryRelations : Bool

open MeansEndsSedimentationBoundary public

canonicalMeansEndsSedimentationBoundary : MeansEndsSedimentationBoundary
canonicalMeansEndsSedimentationBoundary =
  meansEndsSedimentationBoundary
    true
    true
    false
    false
    false
    false
    false
    false

record RevolutionaryPracticeBraidSurface : Setω where
  constructor revolutionaryPracticeBraidSurface
  field
    sourceAtlas : List Source.SourceReference
    strands : List RevolutionaryPracticeStrand
    practices : List PrefigurativePractice
    relationalFreedom : RelationalFreedomSurface
    summerOfLoveBoundary : SummerOfLoveHistoricalBoundary
    meansEndsBoundary : MeansEndsSedimentationBoundary
    patternMindStatus : PatternMindStatus
    sweetgrassSpine : Sweetgrass.SweetgrassCarrierSpineSurface
    knotWeaveBridge : KnotWeave.KnotWeaveTopologyCultureBridge
    authorityBoundary : Authority.MandateAuthorityBoundary
    localGlobalGluingBoundary : Gluing.CouncilGluingBoundary
    reciprocityBridgeRow : Relational.RelationalQiEducationTraumaBridgeRow
    dialecticalReceipt : Dialectic.DialecticalDepthAccumulationReceipt
    carryBraidReceipt : CarryBraid.UnifiedCarryBraidReceipt
    braidRetainsDistinctStrands : Bool
    braidCollapsesTraditions : Bool
    unityRequiresUniformity : Bool
    publicOwnershipEqualsEcologicalReciprocity : Bool
    institutionalChangeImpliesRelationalChange : Bool
    externalSourceAgreementClaimed : Bool
    universalRevolutionaryDoctrinePromoted : Bool
    legalAuthorityPromoted : Bool
    politicalAuthorityPromoted : Bool

open RevolutionaryPracticeBraidSurface public

canonicalRevolutionaryPracticeBraidSurface :
  RevolutionaryPracticeBraidSurface
canonicalRevolutionaryPracticeBraidSurface =
  revolutionaryPracticeBraidSurface
    Source.canonicalRevolutionarySourceReferences
    canonicalRevolutionaryPracticeStrands
    canonicalPrefigurativePractices
    canonicalRelationalFreedomSurface
    canonicalSummerOfLoveHistoricalBoundary
    canonicalMeansEndsSedimentationBoundary
    repoLocalPatternMindRepairContext
    Sweetgrass.canonicalSweetgrassCarrierSpineSurface
    KnotWeave.canonicalKnotWeaveTopologyCultureBridge
    Authority.canonicalMandateAuthorityBoundary
    Gluing.canonicalCouncilGluingBoundary
    Relational.reciprocityBridgeRow
    Dialectic.canonicalDialecticalDepthAccumulationReceipt
    CarryBraid.canonicalUnifiedCarryBraidReceipt
    true
    false
    false
    false
    false
    false
    false
    false
    false

record RevolutionaryPracticeBraidBoundary : Set where
  constructor revolutionaryPracticeBraidBoundary
  field
    strandsRemainDistinct :
      braidRetainsDistinctStrands canonicalRevolutionaryPracticeBraidSurface
        ≡ true
    traditionsDoNotCollapse :
      braidCollapsesTraditions canonicalRevolutionaryPracticeBraidSurface
        ≡ false
    unityDoesNotRequireUniformity :
      unityRequiresUniformity canonicalRevolutionaryPracticeBraidSurface
        ≡ false
    institutionalChangeDoesNotCloseRelationalChange :
      institutionalChangeImpliesRelationalChange
        canonicalRevolutionaryPracticeBraidSurface
        ≡ false
    universalDoctrineBlocked :
      universalRevolutionaryDoctrinePromoted
        canonicalRevolutionaryPracticeBraidSurface
        ≡ false
    politicalAuthorityBlocked :
      politicalAuthorityPromoted canonicalRevolutionaryPracticeBraidSurface
        ≡ false

open RevolutionaryPracticeBraidBoundary public

canonicalRevolutionaryPracticeBraidBoundary :
  RevolutionaryPracticeBraidBoundary
canonicalRevolutionaryPracticeBraidBoundary =
  revolutionaryPracticeBraidBoundary
    refl
    refl
    refl
    refl
    refl
    refl

canonicalRevolutionaryPracticeBraidReceipt :
  GenericReceipt.GenericReceipt
canonicalRevolutionaryPracticeBraidReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "plural revolutionary-practice ecology"
    "DASHI.Governance.RevolutionaryPracticeBraid"
    "canonicalRevolutionaryPracticeBraidSurface"
    "braids mandate/recall, local-global gluing, relationship-anarchy dimensions, Sweetgrass reciprocity, PatternMind repair context, dialectical memory and distributed braid tension while retaining source provenance"
    "the braid does not collapse traditions, prove a universal ethics, establish consent or material symmetry in an actual relation, or create legal or political authority"
    "agda -i . DASHI/Governance/RevolutionaryPracticeBraid.agda"

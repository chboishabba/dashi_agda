module DASHI.Culture.IndigenousKnowledgeGovernedProofSearchExperimentCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Core.GovernedObservationProvenanceExact as Governed
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed

data EpistemicStatus : Set where
  situatedEpistemicHistory scientificEpistemicHistory : EpistemicStatus

carrierEpistemicStatus : IK.KnowledgeCarrier → EpistemicStatus
carrierEpistemicStatus carrier with IK.knowledgeHistory carrier
... | TwoEyed.indigenousHistory = situatedEpistemicHistory
... | TwoEyed.scientificHistory = scientificEpistemicHistory

provenanceCollision :
  Consumer.ConsumerRelevantCollision IK.extractedProposition IK.carrierProvenance
provenanceCollision =
  Consumer.consumer-relevant-collision
    IK.indigenousMedicinalStoryCarrier IK.scientificMedicinalPaperCarrier refl (λ ())

epistemicCollision :
  Consumer.ConsumerRelevantCollision IK.extractedProposition carrierEpistemicStatus
epistemicCollision =
  Consumer.consumer-relevant-collision
    IK.indigenousMedicinalStoryCarrier IK.scientificMedicinalPaperCarrier refl (λ ())

authorityCollision :
  Consumer.ConsumerRelevantCollision IK.extractedProposition IK.authority
authorityCollision =
  Consumer.consumer-relevant-collision
    IK.indigenousMedicinalStoryCarrier IK.scientificMedicinalPaperCarrier refl (λ ())

permissionCollision :
  Consumer.ConsumerRelevantCollision IK.extractedProposition IK.permission
permissionCollision =
  Consumer.consumer-relevant-collision
    IK.indigenousMedicinalStoryCarrier IK.scientificMedicinalPaperCarrier refl (λ ())

obligationCollision :
  Consumer.ConsumerRelevantCollision IK.extractedProposition IK.obligation
obligationCollision =
  Consumer.consumer-relevant-collision
    IK.indigenousMedicinalStoryCarrier IK.scientificMedicinalPaperCarrier refl (λ ())

DetachedPropositionGovernedSufficiency : Set
DetachedPropositionGovernedSufficiency =
  Governed.GovernedConsumerSufficiency
    IK.extractedProposition
    IK.extractedProposition
    IK.carrierProvenance
    carrierEpistemicStatus
    IK.authority
    IK.permission
    IK.obligation

propositionCannotBeCompleteGovernedConsumer :
  DetachedPropositionGovernedSufficiency → ⊥
propositionCannotBeCompleteGovernedConsumer governed =
  Governed.permissionCollisionBlocksGovernedSufficiency permissionCollision governed

propositionFailsGovernedAuthority :
  DetachedPropositionGovernedSufficiency → ⊥
propositionFailsGovernedAuthority governed =
  Governed.authorityCollisionBlocksGovernedSufficiency authorityCollision governed

propositionFailsGovernedObligation :
  DetachedPropositionGovernedSufficiency → ⊥
propositionFailsGovernedObligation governed =
  Governed.obligationCollisionBlocksGovernedSufficiency obligationCollision governed

translationEffectToGoverned : IK.TranslationEffect → Governed.CoordinateEffect
translationEffectToGoverned IK.preservesCoordinate = Governed.preservesCoordinate
translationEffectToGoverned IK.addsCoordinate = Governed.addsCoordinate
translationEffectToGoverned IK.erasesCoordinate = Governed.erasesCoordinate
translationEffectToGoverned IK.unresolvedCoordinate = Governed.unresolvedCoordinate

extractedProvenanceUsesCanonicalErasure :
  translationEffectToGoverned
    (IK.selectedTranslationEffect IK.extractedClaimStage IK.provenanceCoordinate)
  ≡ Governed.erasesCoordinate
extractedProvenanceUsesCanonicalErasure = refl

assayMechanismUsesCanonicalAddition :
  translationEffectToGoverned
    (IK.selectedTranslationEffect IK.assayStage IK.mechanismCoordinate)
  ≡ Governed.addsCoordinate
assayMechanismUsesCanonicalAddition = refl

eraseThenAddYieldsIntroducedLineage :
  Governed.applyTwoEffects
    Governed.erasesCoordinate Governed.addsCoordinate Governed.inheritedCoordinate
  ≡ Governed.introducedCoordinate
eraseThenAddYieldsIntroducedLineage =
  Governed.additionAfterErasureIsIntroducedNotInherited

eraseThenAddDoesNotRestoreInheritedLineage :
  Governed.applyTwoEffects
    Governed.erasesCoordinate Governed.addsCoordinate Governed.inheritedCoordinate
  ≡ Governed.inheritedCoordinate → ⊥
eraseThenAddDoesNotRestoreInheritedLineage =
  Governed.additionAfterErasureDoesNotRestoreInheritedLineage

indigenousKnowledgeAnalogyCannotCloseProofLeaf :
  ProofSearch.ClosedLeafCapability ProofSearch.analogyOnly → ⊥
indigenousKnowledgeAnalogyCannotCloseProofLeaf = ProofSearch.analogyCannotCloseLeaf

conjecturalTranslationCannotCloseProofLeaf :
  ProofSearch.ClosedLeafCapability ProofSearch.conjectural → ⊥
conjecturalTranslationCannotCloseProofLeaf = ProofSearch.conjectureCannotCloseLeaf

record GovernedKnowledgeRouteAdmission : Set where
  constructor governedKnowledgeRouteAdmission
  field
    proofRoute : ProofSearch.RouteAdmission
    permissionSafe : Governed.PermissionSafe IK.extractedProposition IK.permission
    authoritySafe : Governed.AuthoritySafe IK.extractedProposition IK.authority
    obligationSafe : Governed.ObligationSafe IK.extractedProposition IK.obligation

open GovernedKnowledgeRouteAdmission public

noGovernedRouteCanUseDetachedPropositionForPermission :
  GovernedKnowledgeRouteAdmission → ⊥
noGovernedRouteCanUseDetachedPropositionForPermission route =
  Consumer.coarseCollisionBlocksSufficiency permissionCollision (permissionSafe route)

proofAdmissionDoesNotManufactureCustodialPermission :
  ProofSearch.RouteAdmission →
  Governed.PermissionSafe IK.extractedProposition IK.permission → ⊥
proofAdmissionDoesNotManufactureCustodialPermission proofRoute safe =
  Consumer.coarseCollisionBlocksSufficiency permissionCollision safe

data KnowledgeExperimentWorld : Set where
  custodialWorld researchWorld : KnowledgeExperimentWorld

data KnowledgeExperimentControl : Set where
  readOnlyObservation collectSample : KnowledgeExperimentControl

data KnowledgeExperimentValue : Set where
  sameEfficacyReading custodialCode researchCode : KnowledgeExperimentValue

data KnowledgeExperimentDimension : Set where
  efficacyDimension governanceDimension : KnowledgeExperimentDimension

data KnowledgeExperimentCoordinate : Set where
  efficacyCoordinate permissionCoordinate : KnowledgeExperimentCoordinate

worldPermission : KnowledgeExperimentWorld → IK.PermissionStatus
worldPermission custodialWorld = IK.restrictedPermission
worldPermission researchWorld = IK.openResearchPermission

applyKnowledgeControl :
  KnowledgeExperimentControl → KnowledgeExperimentWorld → KnowledgeExperimentWorld
applyKnowledgeControl readOnlyObservation world = world
applyKnowledgeControl collectSample custodialWorld = researchWorld
applyKnowledgeControl collectSample researchWorld = researchWorld

readKnowledgeCoordinate :
  KnowledgeExperimentCoordinate → KnowledgeExperimentWorld → KnowledgeExperimentValue
readKnowledgeCoordinate efficacyCoordinate _ = sameEfficacyReading
readKnowledgeCoordinate permissionCoordinate custodialWorld = custodialCode
readKnowledgeCoordinate permissionCoordinate researchWorld = researchCode

knowledgeExperimentDesign :
  Experiment.ExperimentalCoordinateDesign
    KnowledgeExperimentWorld KnowledgeExperimentControl
    KnowledgeExperimentValue KnowledgeExperimentDimension
knowledgeExperimentDesign =
  Experiment.experimentalCoordinateDesign
    KnowledgeExperimentCoordinate role dimension readKnowledgeCoordinate applyKnowledgeControl
    coordinateReference dimensionReference calibrationReference controlReference
  where
    role : KnowledgeExperimentCoordinate → Experiment.CoordinateRole
    role efficacyCoordinate = Experiment.measuredObservable
    role permissionCoordinate = Experiment.derivedDiscriminator

    dimension : KnowledgeExperimentCoordinate → KnowledgeExperimentDimension
    dimension efficacyCoordinate = efficacyDimension
    dimension permissionCoordinate = governanceDimension

    coordinateReference : KnowledgeExperimentCoordinate → String
    coordinateReference efficacyCoordinate = "bounded efficacy observation"
    coordinateReference permissionCoordinate = "permission/custodial-governance discriminator"

    dimensionReference : KnowledgeExperimentCoordinate → String
    dimensionReference efficacyCoordinate = "declared efficacy observation dimension"
    dimensionReference permissionCoordinate = "declared governance information dimension"

    calibrationReference : KnowledgeExperimentCoordinate → String
    calibrationReference efficacyCoordinate = "source-bounded scientific calibration required"
    calibrationReference permissionCoordinate = "authority/permission receipt required; not inferred from efficacy"

    controlReference : KnowledgeExperimentControl → String
    controlReference readOnlyObservation = "non-destructive observation"
    controlReference collectSample = "sample collection requires independent authority/permission"

permissionCoordinateSeparatesEfficacyCollision :
  Experiment.CoordinateSeparatesCollision
    knowledgeExperimentDesign
    (Experiment.read knowledgeExperimentDesign efficacyCoordinate)
permissionCoordinateSeparatesEfficacyCollision =
  Experiment.coordinateSeparatesCollision
    permissionCoordinate custodialWorld researchWorld refl (λ ())

collectSampleCanModifyPermissionRelevantWorldState :
  Experiment.CoordinateModifiableBy knowledgeExperimentDesign permissionCoordinate
collectSampleCanModifyPermissionRelevantWorldState =
  Experiment.coordinateModifiableBy collectSample custodialWorld (λ ())

data CollectionAuthority : KnowledgeExperimentControl → Set where
  readOnlyAuthority : CollectionAuthority readOnlyObservation

collectSampleHasNoAutomaticAuthority : CollectionAuthority collectSample → ⊥
collectSampleHasNoAutomaticAuthority ()

record AuthorizedControlledDiscriminator
    (left right : KnowledgeExperimentWorld) : Set₁ where
  constructor authorizedControlledDiscriminator
  field
    discriminator :
      Synthesis.ControlledCoordinateDiscriminator knowledgeExperimentDesign left right
    collectionAuthority : CollectionAuthority (Synthesis.control discriminator)

open AuthorizedControlledDiscriminator public

noAuthorizedSampleDiscriminator :
  (authorized : AuthorizedControlledDiscriminator custodialWorld researchWorld) →
  Synthesis.control (discriminator authorized) ≡ collectSample → ⊥
noAuthorizedSampleDiscriminator authorized refl =
  collectSampleHasNoAutomaticAuthority (collectionAuthority authorized)

efficacyObservation : KnowledgeExperimentWorld → KnowledgeExperimentValue
efficacyObservation = Experiment.read knowledgeExperimentDesign efficacyCoordinate

permissionObservation : KnowledgeExperimentWorld → KnowledgeExperimentValue
permissionObservation = Experiment.read knowledgeExperimentDesign permissionCoordinate

efficacyCollisionForPermission :
  Consumer.ConsumerRelevantCollision efficacyObservation worldPermission
efficacyCollisionForPermission =
  Consumer.consumer-relevant-collision custodialWorld researchWorld refl (λ ())

efficacyCannotClosePermissionConsumer :
  Consumer.ConsumerSufficient efficacyObservation worldPermission → ⊥
efficacyCannotClosePermissionConsumer =
  Consumer.coarseCollisionBlocksSufficiency efficacyCollisionForPermission

permissionDiscriminatorBundle : Synthesis.ExperimentBundle KnowledgeExperimentWorld
permissionDiscriminatorBundle =
  Synthesis.experimentBundle
    KnowledgeExperimentValue
    permissionObservation
    zero
    "permission/custodial-governance discriminator"
    "requires a valid authority/permission information source"

permissionBundleSeparatesEfficacyCollision :
  Synthesis.BundleSeparates permissionDiscriminatorBundle custodialWorld researchWorld
permissionBundleSeparatesEfficacyCollision = Synthesis.bundleSeparates (λ ())

record IndigenousGovernedProofSearchExperimentBoundary : Set where
  constructor indigenousGovernedProofSearchExperimentBoundary
  field
    samePropositionIsGovernedComplete : Bool
    samePropositionIsGovernedCompleteIsFalse : samePropositionIsGovernedComplete ≡ false
    laterScientificMetadataRestoresErasedInheritedLineage : Bool
    laterScientificMetadataRestoresErasedInheritedLineageIsFalse :
      laterScientificMetadataRestoresErasedInheritedLineage ≡ false
    proofRouteAdmissionCreatesCustodialPermission : Bool
    proofRouteAdmissionCreatesCustodialPermissionIsFalse :
      proofRouteAdmissionCreatesCustodialPermission ≡ false
    coordinateModifiabilityCreatesAuthority : Bool
    coordinateModifiabilityCreatesAuthorityIsFalse :
      coordinateModifiabilityCreatesAuthority ≡ false
    scientificDiscriminatorMayIncreaseResolution : Bool
    scientificDiscriminatorMayIncreaseResolutionIsTrue :
      scientificDiscriminatorMayIncreaseResolution ≡ true
    consumerClosingExperimentIsConsumerIndexed : Bool
    consumerClosingExperimentIsConsumerIndexedIsTrue :
      consumerClosingExperimentIsConsumerIndexed ≡ true
    reading : String

canonicalIndigenousGovernedProofSearchExperimentBoundary :
  IndigenousGovernedProofSearchExperimentBoundary
canonicalIndigenousGovernedProofSearchExperimentBoundary =
  indigenousGovernedProofSearchExperimentBoundary
    false refl false refl false refl false refl true refl true refl
    "Post-merge cross-pollination: a detached proposition may be scientifically useful while remaining insufficient for provenance, authority, permission or obligation; erase-then-add does not restore inherited lineage; proof-search admission and experimental discrimination do not manufacture custodial permission; sequential experiment closure is indexed by the actual downstream consumer."

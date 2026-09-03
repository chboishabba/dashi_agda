module DASHI.Culture.IntellectualReceptionContextIndexedAuthorisedStabiliserProofSearchExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.IntellectualReceptionSemanticStabiliserParetoAuthorityCrossPollinationExact as Stabiliser
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Governance.AuthorityMandateCore as Authority

------------------------------------------------------------------------
-- CONTEXT-INDEXED AUTHORISED STABILISER
--
-- Geometry and semantic role preservation remain context-independent in this
-- finite specimen. Authority is context-indexed. The same semantic generator
-- can therefore be excluded in one authority context and admitted in another
-- without changing its underlying Base369/voxel action.
------------------------------------------------------------------------

data ReceptionAuthorityContext : Set where
  baselineAuthorityContext
  reviewedComparisonContext
  : ReceptionAuthorityContext

data ScopedGeneratorAuthority :
  ReceptionAuthorityContext →
  Authority.AuthoritySource →
  Stabiliser.GeometricGenerator →
  Set where

  baselineIdentityScope :
    ScopedGeneratorAuthority
      baselineAuthorityContext
      Authority.constitutionalDelegation
      Stabiliser.identityGenerator

  reviewedIdentityScope :
    ScopedGeneratorAuthority
      reviewedComparisonContext
      Authority.constitutionalDelegation
      Stabiliser.identityGenerator

  reviewedComparisonReflectionScope :
    ScopedGeneratorAuthority
      reviewedComparisonContext
      Authority.judicialWarrant
      Stabiliser.comparisonFlipXGenerator

record ContextAuthorisedGenerator
    (context : ReceptionAuthorityContext)
    (generator : Stabiliser.GeometricGenerator) : Set where
  constructor context-authorised-generator
  field
    semantic : Stabiliser.SemanticRolePreservingGenerator generator
    source : Authority.AuthoritySource
    sourceAdmissible : Authority.AdmissibleAuthoritySource source
    scoped : ScopedGeneratorAuthority context source generator

open ContextAuthorisedGenerator public

baselineIdentityAuthorised :
  ContextAuthorisedGenerator
    baselineAuthorityContext
    Stabiliser.identityGenerator
baselineIdentityAuthorised =
  context-authorised-generator
    Stabiliser.semanticIdentity
    Authority.constitutionalDelegation
    tt
    baselineIdentityScope

reviewedIdentityAuthorised :
  ContextAuthorisedGenerator
    reviewedComparisonContext
    Stabiliser.identityGenerator
reviewedIdentityAuthorised =
  context-authorised-generator
    Stabiliser.semanticIdentity
    Authority.constitutionalDelegation
    tt
    reviewedIdentityScope

reviewedComparisonReflectionAuthorised :
  ContextAuthorisedGenerator
    reviewedComparisonContext
    Stabiliser.comparisonFlipXGenerator
reviewedComparisonReflectionAuthorised =
  context-authorised-generator
    Stabiliser.semanticComparisonReflection
    Authority.judicialWarrant
    tt
    reviewedComparisonReflectionScope

baselineComparisonReflectionNotAuthorised :
  ContextAuthorisedGenerator
    baselineAuthorityContext
    Stabiliser.comparisonFlipXGenerator → ⊥
baselineComparisonReflectionNotAuthorised
  (context-authorised-generator semantic source admissible ())

swapXYNotAuthorisedInAnyContext :
  ∀ {context} →
  ContextAuthorisedGenerator context Stabiliser.swapXYGenerator → ⊥
swapXYNotAuthorisedInAnyContext authorised =
  Stabiliser.swapXYNotSemanticRolePreserving (semantic authorised)

record ContextualAuthorisedFragmentExpansion : Set where
  constructor contextual-authorised-fragment-expansion
  field
    excludedAtBaseline :
      ContextAuthorisedGenerator
        baselineAuthorityContext
        Stabiliser.comparisonFlipXGenerator → ⊥
    admittedAfterIndependentReview :
      ContextAuthorisedGenerator
        reviewedComparisonContext
        Stabiliser.comparisonFlipXGenerator

canonicalContextualAuthorisedFragmentExpansion :
  ContextualAuthorisedFragmentExpansion
canonicalContextualAuthorisedFragmentExpansion =
  contextual-authorised-fragment-expansion
    baselineComparisonReflectionNotAuthorised
    reviewedComparisonReflectionAuthorised

------------------------------------------------------------------------
-- Context-relative eligibility.  Pareto/MDL ranking still occurs only after
-- both semantic and context-indexed authority gates are inhabited.
------------------------------------------------------------------------

contextEligibilityProblem :
  ReceptionAuthorityContext → MDL.ConsumerMDLProblem
contextEligibilityProblem context =
  MDL.consumerMDLProblem
    Stabiliser.GeometricGenerator
    Stabiliser.SemanticRolePreservingGenerator
    (ContextAuthorisedGenerator context)
    Stabiliser.generatorDescriptionLength
    (λ _ _ → ⊤)
    Stabiliser.generatorReference
    "same finite generator code; authority gate indexed by reception context"
    "context-indexed authorised stabiliser"

baselineComparisonReflectionNotEligible :
  MDL.Eligible
    (contextEligibilityProblem baselineAuthorityContext)
    Stabiliser.comparisonFlipXGenerator → ⊥
baselineComparisonReflectionNotEligible eligible =
  baselineComparisonReflectionNotAuthorised (proj₂ eligible)

reviewedComparisonReflectionEligible :
  MDL.Eligible
    (contextEligibilityProblem reviewedComparisonContext)
    Stabiliser.comparisonFlipXGenerator
reviewedComparisonReflectionEligible =
  Stabiliser.semanticComparisonReflection ,
  reviewedComparisonReflectionAuthorised

swapXYNotEligibleInAnyContext :
  ∀ {context} →
  MDL.Eligible
    (contextEligibilityProblem context)
    Stabiliser.swapXYGenerator → ⊥
swapXYNotEligibleInAnyContext eligible =
  Stabiliser.swapXYNotSemanticRolePreserving (proj₁ eligible)

------------------------------------------------------------------------
-- PROOF-SEARCH LEAST PRIVILEGE
--
-- A semantically lawful but currently unauthorised generator may be a live
-- proof-search/investigation target.  Route admission is theorem-search
-- authority; it is deliberately not the governance authority receipt above.
------------------------------------------------------------------------

comparisonReflectionInvestigationRoute : ProofSearch.RouteAdmission
comparisonReflectionInvestigationRoute = ProofSearch.canonicalRouteAdmission

comparisonReflectionInvestigationIsLive : ProofSearch.LiveProofSearch
comparisonReflectionInvestigationIsLive =
  ProofSearch.elaborateRoute comparisonReflectionInvestigationRoute

analogyStillCannotCloseInvestigationLeaf :
  ProofSearch.ClosedLeafCapability ProofSearch.analogyOnly → ⊥
analogyStillCannotCloseInvestigationLeaf = ProofSearch.analogyCannotCloseLeaf

conjectureStillCannotCloseInvestigationLeaf :
  ProofSearch.ClosedLeafCapability ProofSearch.conjectural → ⊥
conjectureStillCannotCloseInvestigationLeaf = ProofSearch.conjectureCannotCloseLeaf

liveProofSearchDoesNotAuthoriseBaselineReflection :
  ProofSearch.LiveProofSearch →
  ContextAuthorisedGenerator
    baselineAuthorityContext
    Stabiliser.comparisonFlipXGenerator → ⊥
liveProofSearchDoesNotAuthoriseBaselineReflection _ =
  baselineComparisonReflectionNotAuthorised

------------------------------------------------------------------------
-- EXPERIMENTAL DESIGN
--
-- The semantic observer cannot distinguish baseline and reviewed authority
-- contexts: comparison reflection is semantically lawful in both.  A separate
-- authority-status coordinate does distinguish them.  This is an information
-- gain, not an authority-producing manipulation.
------------------------------------------------------------------------

data StabiliserExperimentControl : Set where
  inspectSemanticStatus inspectAuthorityStatus : StabiliserExperimentControl

data StabiliserExperimentCoordinate : Set where
  semanticStatusCoordinate authorityStatusCoordinate : StabiliserExperimentCoordinate

data StabiliserExperimentValue : Set where
  semanticLawfulValue
  authorityMissingValue
  authorityPresentValue
  : StabiliserExperimentValue

data StabiliserExperimentDimension : Set where
  semanticRoleDimension authorityScopeDimension : StabiliserExperimentDimension

applyInspection :
  StabiliserExperimentControl →
  ReceptionAuthorityContext →
  ReceptionAuthorityContext
applyInspection _ context = context

semanticContextObservation :
  ReceptionAuthorityContext → StabiliserExperimentValue
semanticContextObservation _ = semanticLawfulValue

authorityContextObservation :
  ReceptionAuthorityContext → StabiliserExperimentValue
authorityContextObservation baselineAuthorityContext = authorityMissingValue
authorityContextObservation reviewedComparisonContext = authorityPresentValue

readStabiliserCoordinate :
  StabiliserExperimentCoordinate →
  ReceptionAuthorityContext →
  StabiliserExperimentValue
readStabiliserCoordinate semanticStatusCoordinate = semanticContextObservation
readStabiliserCoordinate authorityStatusCoordinate = authorityContextObservation

stabiliserExperimentDesign :
  Experiment.ExperimentalCoordinateDesign
    ReceptionAuthorityContext
    StabiliserExperimentControl
    StabiliserExperimentValue
    StabiliserExperimentDimension
stabiliserExperimentDesign =
  Experiment.experimentalCoordinateDesign
    StabiliserExperimentCoordinate
    role
    dimension
    readStabiliserCoordinate
    applyInspection
    coordinateReference
    dimensionReference
    calibrationReference
    controlReference
  where
    role : StabiliserExperimentCoordinate → Experiment.CoordinateRole
    role semanticStatusCoordinate = Experiment.measuredObservable
    role authorityStatusCoordinate = Experiment.derivedDiscriminator

    dimension : StabiliserExperimentCoordinate → StabiliserExperimentDimension
    dimension semanticStatusCoordinate = semanticRoleDimension
    dimension authorityStatusCoordinate = authorityScopeDimension

    coordinateReference : StabiliserExperimentCoordinate → String
    coordinateReference semanticStatusCoordinate =
      "semantic-role lawfulness of comparison reflection"
    coordinateReference authorityStatusCoordinate =
      "context-indexed independent authority status"

    dimensionReference : StabiliserExperimentCoordinate → String
    dimensionReference semanticStatusCoordinate =
      "typed action-voxel semantic-role dimension"
    dimensionReference authorityStatusCoordinate =
      "authority-scope information dimension"

    calibrationReference : StabiliserExperimentCoordinate → String
    calibrationReference semanticStatusCoordinate =
      "IntellectualReceptionSemanticStabiliserParetoAuthorityCrossPollinationExact"
    calibrationReference authorityStatusCoordinate =
      "AuthorityMandateCore plus explicit ScopedGeneratorAuthority witness"

    controlReference : StabiliserExperimentControl → String
    controlReference inspectSemanticStatus = "read semantic stabiliser status"
    controlReference inspectAuthorityStatus = "read independent authority receipt status"

semanticObserverCollapsesAuthorityContexts :
  semanticContextObservation baselineAuthorityContext
  ≡ semanticContextObservation reviewedComparisonContext
semanticObserverCollapsesAuthorityContexts = refl

authorityCoordinateSeparatesSemanticCollision :
  Experiment.CoordinateSeparatesCollision
    stabiliserExperimentDesign
    semanticContextObservation
authorityCoordinateSeparatesSemanticCollision =
  Experiment.coordinateSeparatesCollision
    authorityStatusCoordinate
    baselineAuthorityContext
    reviewedComparisonContext
    refl
    (λ ())

------------------------------------------------------------------------
-- DISCRIMINATOR SYNTHESIS
------------------------------------------------------------------------

authorityStatusBundle :
  Synthesis.ExperimentBundle ReceptionAuthorityContext
authorityStatusBundle =
  Synthesis.experimentBundle
    StabiliserExperimentValue
    authorityContextObservation
    1
    "independent authority-status discriminator"
    "reads a supplied context-indexed authority receipt; does not create one"

authorityBundleSeparatesContexts :
  Synthesis.BundleSeparates
    authorityStatusBundle
    baselineAuthorityContext
    reviewedComparisonContext
authorityBundleSeparatesContexts =
  Synthesis.bundleSeparates (λ ())

authorityLanguageExtension :
  Synthesis.DiscriminatingLanguageExtension semanticContextObservation
authorityLanguageExtension =
  Synthesis.discriminatingLanguageExtension
    (Synthesis.currentObserverCollision
      baselineAuthorityContext
      reviewedComparisonContext
      refl)
    authorityStatusBundle
    authorityBundleSeparatesContexts

authorityJoinedObservationSeparates :
  Synthesis.joinedObservation semanticContextObservation authorityStatusBundle
      baselineAuthorityContext
  ≡ Synthesis.joinedObservation semanticContextObservation authorityStatusBundle
      reviewedComparisonContext → ⊥
authorityJoinedObservationSeparates =
  Synthesis.extensionJoinSeparates authorityLanguageExtension

------------------------------------------------------------------------
-- Consumer-relative residual reading: whether the comparison reflection is
-- authorised is the declared downstream consumer.  The semantic surface alone
-- has a consumer-relevant collision; the authority discriminator repairs it.
------------------------------------------------------------------------

data ReflectionAuthorityDecision : Set where
  reflectionBlocked reflectionAuthorised : ReflectionAuthorityDecision

reflectionAuthorityDecision :
  ReceptionAuthorityContext → ReflectionAuthorityDecision
reflectionAuthorityDecision baselineAuthorityContext = reflectionBlocked
reflectionAuthorityDecision reviewedComparisonContext = reflectionAuthorised

semanticAuthorityCollision :
  Consumer.ConsumerRelevantCollision
    semanticContextObservation
    reflectionAuthorityDecision
semanticAuthorityCollision =
  Consumer.consumer-relevant-collision
    baselineAuthorityContext
    reviewedComparisonContext
    refl
    (λ ())

semanticObserverCannotCloseAuthorityConsumer :
  Consumer.ConsumerSufficient
    semanticContextObservation
    reflectionAuthorityDecision → ⊥
semanticObserverCannotCloseAuthorityConsumer =
  Consumer.coarseCollisionBlocksSufficiency semanticAuthorityCollision

jointSemanticAuthoritySufficient :
  Consumer.ConsumerSufficient
    (λ context →
      semanticContextObservation context , authorityContextObservation context)
    reflectionAuthorityDecision
jointSemanticAuthoritySufficient baselineAuthorityContext baselineAuthorityContext same = refl
jointSemanticAuthoritySufficient baselineAuthorityContext reviewedComparisonContext ()
jointSemanticAuthoritySufficient reviewedComparisonContext baselineAuthorityContext ()
jointSemanticAuthoritySufficient reviewedComparisonContext reviewedComparisonContext same = refl

canonicalAuthorityResidualRepair :
  Consumer.ResidualRepair
    semanticContextObservation
    authorityContextObservation
    reflectionAuthorityDecision
canonicalAuthorityResidualRepair =
  Consumer.residual-repair jointSemanticAuthoritySufficient

------------------------------------------------------------------------
-- CAPSTONE: proof-search and experiment may investigate the missing authority
-- residual, but the post-investigation authority state remains supplied by an
-- independent context-indexed receipt.
------------------------------------------------------------------------

record ContextualStabiliserInvestigation : Set₁ where
  constructor contextual-stabiliser-investigation
  field
    proofRoute : ProofSearch.RouteAdmission
    semanticCandidate :
      Stabiliser.SemanticRolePreservingGenerator
        Stabiliser.comparisonFlipXGenerator
    discriminator :
      Synthesis.DiscriminatingLanguageExtension semanticContextObservation
    reviewedAuthority :
      ContextAuthorisedGenerator
        reviewedComparisonContext
        Stabiliser.comparisonFlipXGenerator

open ContextualStabiliserInvestigation public

canonicalContextualStabiliserInvestigation : ContextualStabiliserInvestigation
canonicalContextualStabiliserInvestigation =
  contextual-stabiliser-investigation
    comparisonReflectionInvestigationRoute
    Stabiliser.semanticComparisonReflection
    authorityLanguageExtension
    reviewedComparisonReflectionAuthorised

data ProofSearchRouteCreatesGovernanceAuthority : Set where
data DiscriminatorObservationCreatesGovernanceAuthority : Set where
data SemanticLawfulnessCreatesGovernanceAuthority : Set where

proofSearchRouteDoesNotCreateGovernanceAuthority :
  ProofSearchRouteCreatesGovernanceAuthority → ⊥
proofSearchRouteDoesNotCreateGovernanceAuthority ()

discriminatorDoesNotCreateGovernanceAuthority :
  DiscriminatorObservationCreatesGovernanceAuthority → ⊥
discriminatorDoesNotCreateGovernanceAuthority ()

semanticLawfulnessDoesNotCreateGovernanceAuthority :
  SemanticLawfulnessCreatesGovernanceAuthority → ⊥
semanticLawfulnessDoesNotCreateGovernanceAuthority ()

record IntellectualReceptionContextIndexedStabiliserProofSearchExperimentBoundary : Set where
  constructor intellectual-reception-context-indexed-stabiliser-proof-search-experiment-boundary
  field
    authorisedStabiliserIsContextIndexed : Bool
    semanticReflectionMayBeInvestigatedBeforeAuthority : Bool
    proofSearchAdmissionCreatesGovernanceAuthority : Bool
    authorityCoordinateCanSeparateSemanticCollision : Bool
    authorityMeasurementCreatesAuthorityReceipt : Bool
    jointObserverCanCloseAuthorityConsumer : Bool
    swapXYCanBecomeAuthorisedWithoutSemanticRepair : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionContextIndexedStabiliserProofSearchExperimentBoundary :
  IntellectualReceptionContextIndexedStabiliserProofSearchExperimentBoundary
canonicalIntellectualReceptionContextIndexedStabiliserProofSearchExperimentBoundary =
  intellectual-reception-context-indexed-stabiliser-proof-search-experiment-boundary
    true true false true false true false true

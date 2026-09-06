module DASHI.Cognition.PNF.SensibLawUniversalLegalAlgebraEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawSourceFormAuthorityRoleBidiExact as SourceRole
import DASHI.Cognition.PNF.SensibLawPrecedentApplicabilityDistinguishingExact as Precedent
import DASHI.Cognition.PNF.SensibLawStatutoryRuleStructureAlgebraExact as Statute
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate

------------------------------------------------------------------------
-- Universal graph and issue-specific graph are one architecture.
------------------------------------------------------------------------

data IssueSpecificPipelineIsSeparateLegalSystem : Set where
issueProjectionIsNotSeparateSystem : IssueSpecificPipelineIsSeparateLegalSystem → ⊥
issueProjectionIsNotSeparateSystem ()

------------------------------------------------------------------------
-- Duty has been lifted out of the climate-only vocabulary.
------------------------------------------------------------------------

climatePhysicalInjuryUsesNegligenceWrongType :
  Negligence.ClimateDutySpecialisation.wrongType
    Negligence.australiaPhysicalInjuryDutySpecialisation
  ≡ Negligence.negligenceWrongType
climatePhysicalInjuryUsesNegligenceWrongType = refl

climatePhysicalInjuryTargetsDutyElement :
  Negligence.ClimateDutySpecialisation.targetElement
    Negligence.australiaPhysicalInjuryDutySpecialisation
  ≡ Negligence.dutyElement
climatePhysicalInjuryTargetsDutyElement = refl

------------------------------------------------------------------------
-- Source form and authority role remain orthogonal.
------------------------------------------------------------------------

caseContainerDoesNotFlattenPropositionRoles :
  SourceRole.CaseSourceMakesEveryPropositionBindingRatio → ⊥
caseContainerDoesNotFlattenPropositionRoles =
  SourceRole.caseContainerDoesNotFlattenRoles

similarFactSurfaceDoesNotAutomaticallyApplyPrecedent :
  Precedent.SimilarFactsAutomaticallyApplyPrecedent → ⊥
similarFactSurfaceDoesNotAutomaticallyApplyPrecedent =
  Precedent.similarityDoesNotProveApplication

statutoryDefinitionRemainsScoped :
  Statute.DefinitionIsGlobalDictionaryMeaning → ⊥
statutoryDefinitionRemainsScoped = Statute.definitionIsScoped

------------------------------------------------------------------------
-- Legacy WrongElement string references no longer count as proof.
------------------------------------------------------------------------

legacyElementReferenceIsNotElementDerivation :
  Elements.ElementStringReferenceIsElementProof → ⊥
legacyElementReferenceIsNotElementDerivation = Elements.stringReferenceDoesNotProveElement

------------------------------------------------------------------------
-- Duty-coordinate stratification from the prior climate owner is preserved.
------------------------------------------------------------------------

foreseeabilityClassIsFactual :
  Negligence.classifyDutyIssue Climate.reasonableForeseeability
  ≡ Negligence.factualDutyFeature
foreseeabilityClassIsFactual = refl

corePolicyClassIsInstitutional :
  Negligence.classifyDutyIssue Climate.coreGovernmentPolicy
  ≡ Negligence.institutionalDutyConstraint
corePolicyClassIsInstitutional = refl

causationClassIsDownstreamElement :
  Negligence.classifyDutyIssue Climate.causation
  ≡ Negligence.downstreamNegligenceElement
causationClassIsDownstreamElement = refl

------------------------------------------------------------------------
-- Aggregate does not claim corpus-complete legal extraction or kernel receipt.
------------------------------------------------------------------------

data UniversalAlgebraAggregateMeansCorpusComplete : Set where
data UniversalAlgebraAggregateMeansKernelValidated : Set where

aggregateDoesNotClaimCorpusCompleteness :
  UniversalAlgebraAggregateMeansCorpusComplete → ⊥
aggregateDoesNotClaimCorpusCompleteness ()

aggregateDoesNotClaimKernelValidation :
  UniversalAlgebraAggregateMeansKernelValidated → ⊥
aggregateDoesNotClaimKernelValidation ()

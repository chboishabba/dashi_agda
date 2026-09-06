module DASHI.Cognition.PNF.SensibLawSourceFormAuthorityRoleBidiExact where

------------------------------------------------------------------------
-- SOURCE FORM <-> PROPOSITION AUTHORITY ROLE
--
-- Existing SensibLaw had two useful but partially overlapping vocabularies:
--   Ontology.NormSourceForm and TypedLegalAuthorityEdge.AuthorityKind.
--
-- This bridge keeps source-container form separate from proposition-level role.
-- A case-law source can contain ratio, dictum, fact finding, policy reasoning,
-- concurrence, dissent, or submissions. The container does not flatten them.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra

record SourceFormRoleReceipt : Set where
  constructor source-form-role-receipt
  field
    sourceIdentity : Edge.SourceIdentity
    sourceForm : Ontology.NormSourceForm
    propositionRole : Algebra.AuthorityRole
    propositionReference : String
    sourceFormSupported : Bool
    propositionRoleSupported : Bool

open SourceFormRoleReceipt public

------------------------------------------------------------------------
-- Coarse container-form projection from the existing AuthorityKind.
-- Proposition role remains independently supplied.
------------------------------------------------------------------------

authorityContainerForm : Edge.AuthorityKind → Ontology.NormSourceForm
authorityContainerForm Edge.constitutionalText = Ontology.constitution
authorityContainerForm Edge.legislation = Ontology.statute
authorityContainerForm Edge.delegatedLegislation = Ontology.regulation
authorityContainerForm Edge.bindingPrecedent = Ontology.caseLaw
authorityContainerForm Edge.persuasivePrecedent = Ontology.caseLaw
authorityContainerForm Edge.commonLawDevelopment = Ontology.caseLaw
authorityContainerForm Edge.judicialPolicyConsideration = Ontology.caseLaw
authorityContainerForm Edge.internationalJudicialOpinion = Ontology.treaty
authorityContainerForm Edge.adjudicatedFact = Ontology.caseLaw
authorityContainerForm Edge.partySubmission = Ontology.caseLaw
authorityContainerForm Edge.empiricalSource = Ontology.custom
authorityContainerForm Edge.criticalTheorySource = Ontology.custom
authorityContainerForm Edge.dashSyntheticInference = Ontology.custom

------------------------------------------------------------------------
-- The mapping above is a storage/container bridge only. In particular, using
-- treaty as the closest existing external-international container for an ICJ
-- opinion does NOT assert that the opinion itself is a treaty.
------------------------------------------------------------------------

data ContainerProjectionIsDoctrinalIdentity : Set where
data CaseSourceMakesEveryPropositionBindingRatio : Set where
data InternationalOpinionIsTreatyInstrument : Set where

containerProjectionDoesNotCreateDoctrinalIdentity :
  ContainerProjectionIsDoctrinalIdentity → ⊥
containerProjectionDoesNotCreateDoctrinalIdentity ()

caseContainerDoesNotFlattenRoles :
  CaseSourceMakesEveryPropositionBindingRatio → ⊥
caseContainerDoesNotFlattenRoles ()

internationalOpinionDoesNotBecomeTreatyInstrument :
  InternationalOpinionIsTreatyInstrument → ⊥
internationalOpinionDoesNotBecomeTreatyInstrument ()

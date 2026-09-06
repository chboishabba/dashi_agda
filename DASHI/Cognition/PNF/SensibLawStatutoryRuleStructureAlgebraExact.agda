module DASHI.Cognition.PNF.SensibLawStatutoryRuleStructureAlgebraExact where

------------------------------------------------------------------------
-- STATUTORY STRUCTURE -> UNIVERSAL LEGAL RULE ALGEBRA
--
-- Statutes are not flat prose blobs. This module types provisions, definitions,
-- exceptions, deeming clauses, provisos, amendments, commencement and repeal as
-- distinct structures that compile into the universal rule graph.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra

------------------------------------------------------------------------
-- Provision topology.
------------------------------------------------------------------------

data ProvisionKind : Set where
  operativeProvision
  definitionProvision
  exceptionProvision
  deemingProvision
  provisoProvision
  powerConferralProvision
  dutyImpositionProvision
  prohibitionProvision
  remedyProvision
  jurisdictionProvision
  commencementProvision
  repealProvision
  amendmentProvision
  : ProvisionKind

record StatutoryProvision : Set where
  constructor statutory-provision
  field
    provisionId : Ontology.StableId
    source : Algebra.LegalSourceRef
    kind : ProvisionKind
    citation : String
    operativeProposition : Algebra.LegalProposition
    conditions : List Algebra.LegalProposition
    exceptions : List Algebra.LegalProposition
    defeaters : List Algebra.LegalProposition
    effectiveFrom : String
    effectiveTo : String

open StatutoryProvision public

------------------------------------------------------------------------
-- Definitions are scoped transformations, not global lexical substitutions.
------------------------------------------------------------------------

record StatutoryDefinition : Set where
  constructor statutory-definition
  field
    definitionProvision : StatutoryProvision
    definedTerm : String
    definedPredicate : Algebra.LegalProposition
    scopePredicate : Algebra.LegalProposition

open StatutoryDefinition public

------------------------------------------------------------------------
-- Amendments/repeal preserve temporal provenance.
------------------------------------------------------------------------

data StatutoryChangeKind : Set where
  insertText
  substituteText
  omitText
  repealProvision
  commenceProvision
  expireProvision
  : StatutoryChangeKind

record StatutoryChange : Set where
  constructor statutory-change
  field
    changeId : Ontology.StableId
    targetProvision : StatutoryProvision
    changeKind : StatutoryChangeKind
    amendingSource : Algebra.LegalSourceRef
    effectiveDate : String
    resultingProposition : Algebra.LegalProposition

open StatutoryChange public

------------------------------------------------------------------------
-- Compilation to universal rules.
------------------------------------------------------------------------

provisionAuthorityRole : ProvisionKind → Algebra.AuthorityRole
provisionAuthorityRole operativeProvision = Algebra.legislativeRuleRole
provisionAuthorityRole definitionProvision = Algebra.legislativeRuleRole
provisionAuthorityRole exceptionProvision = Algebra.legislativeRuleRole
provisionAuthorityRole deemingProvision = Algebra.legislativeRuleRole
provisionAuthorityRole provisoProvision = Algebra.legislativeRuleRole
provisionAuthorityRole powerConferralProvision = Algebra.legislativeRuleRole
provisionAuthorityRole dutyImpositionProvision = Algebra.legislativeRuleRole
provisionAuthorityRole prohibitionProvision = Algebra.legislativeRuleRole
provisionAuthorityRole remedyProvision = Algebra.legislativeRuleRole
provisionAuthorityRole jurisdictionProvision = Algebra.legislativeRuleRole
provisionAuthorityRole commencementProvision = Algebra.legislativeRuleRole
provisionAuthorityRole repealProvision = Algebra.legislativeRuleRole
provisionAuthorityRole amendmentProvision = Algebra.legislativeRuleRole

compileProvision : StatutoryProvision → Algebra.LegalRule
compileProvision p = Algebra.legal-rule
  (StatutoryProvision.provisionId p)
  (StatutoryProvision.conditions p)
  (StatutoryProvision.operativeProposition p)
  (StatutoryProvision.exceptions p)
  (StatutoryProvision.defeaters p)
  (StatutoryProvision.source p)
  (provisionAuthorityRole (StatutoryProvision.kind p))
  (StatutoryProvision.effectiveFrom p)
  "jurisdiction inherited from legal source/system"

------------------------------------------------------------------------
-- A statutory compilation bundle retains source and change history.
------------------------------------------------------------------------

record StatutoryRuleBundle : Set where
  constructor statutory-rule-bundle
  field
    source : Algebra.LegalSourceRef
    provisions : List StatutoryProvision
    changes : List StatutoryChange
    compiledRules : List Algebra.LegalRule
    compilationPreservesProvisionIdentity : Set

open StatutoryRuleBundle public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DefinitionIsGlobalDictionaryMeaning : Set where
data RepealedProvisionRemainsCurrentByTextPresence : Set where
data StatuteSourceFormDeterminesCasePrecedentRole : Set where
data AmendmentErasesPriorTemporalState : Set where

definitionIsScoped : DefinitionIsGlobalDictionaryMeaning → ⊥
definitionIsScoped ()

repealChangesTemporalApplicability : RepealedProvisionRemainsCurrentByTextPresence → ⊥
repealChangesTemporalApplicability ()

statuteDoesNotDetermineCaseRole : StatuteSourceFormDeterminesCasePrecedentRole → ⊥
statuteDoesNotDetermineCaseRole ()

amendmentPreservesHistory : AmendmentErasesPriorTemporalState → ⊥
amendmentPreservesHistory ()

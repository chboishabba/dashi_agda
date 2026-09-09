module DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawSourceFormAuthorityRoleBidiExact as SourceRole

data LegalAttributionLayer : Set where
  primarySourceLayer : LegalAttributionLayer
  secondaryInterpretationLayer : LegalAttributionLayer
  repositoryReconstructionLayer : LegalAttributionLayer

record PropositionSourceReceipt (p : Algebra.LegalProposition) : Set where
  constructor proposition-source-receipt
  field
    attributedSource : Source.AttributedSource
    legalSourceRef : Algebra.LegalSourceRef
    exactLocator : String
    attributionLayer : LegalAttributionLayer
    sourceFormRole : SourceRole.SourceFormRoleReceipt
    legalSourceSystemMatchesProposition :
      Ontology.LegalSource.sourceSystem (Algebra.source legalSourceRef)
      ≡ Algebra.legalSystem p
    sourceFormSupported : SourceRole.sourceFormSupported sourceFormRole ≡ true
    propositionRoleSupported : SourceRole.propositionRoleSupported sourceFormRole ≡ true
    citationStillDoesNotCreateAuthority : Source.citationCreatesAuthority attributedSource ≡ false
    sourceReference : String

open PropositionSourceReceipt public

record SourceRealisedLegalRule (r : Algebra.LegalRule) : Set₁ where
  constructor source-realised-legal-rule
  field
    ruleAttributedSource : Source.AttributedSource
    ruleSourceRef : Algebra.LegalSourceRef
    ruleSourceRefIsCanonical : ruleSourceRef ≡ Algebra.sourceRef r
    ruleExactLocator : String
    ruleAuthorityRoleReceipt : SourceRole.SourceFormRoleReceipt
    ruleAuthorityRoleMatches : SourceRole.propositionRole ruleAuthorityRoleReceipt ≡ Algebra.authorityRole r
    ruleSourceFormSupported : SourceRole.sourceFormSupported ruleAuthorityRoleReceipt ≡ true
    ruleRoleSupported : SourceRole.propositionRoleSupported ruleAuthorityRoleReceipt ≡ true
    ruleCitationStillDoesNotCreateAuthority : Source.citationCreatesAuthority ruleAttributedSource ≡ false

    conclusionSource : PropositionSourceReceipt (Algebra.conclusion r)
    premiseSources : Algebra.All PropositionSourceReceipt (Algebra.premises r)
    exceptionSources : Algebra.All PropositionSourceReceipt (Algebra.exceptions r)
    defeaterSources : Algebra.All PropositionSourceReceipt (Algebra.defeaters r)

    jurisdictionPredicate : Algebra.LegalProposition
    jurisdictionSource : PropositionSourceReceipt jurisdictionPredicate
    jurisdictionPredicateKind : Algebra.propositionKind jurisdictionPredicate ≡ Algebra.jurisdictionPredicate

    temporalPredicate : Algebra.LegalProposition
    temporalSource : PropositionSourceReceipt temporalPredicate
    temporalPredicateKind : Algebra.propositionKind temporalPredicate ≡ Algebra.temporalPredicate

    ruleSystem : Ontology.StableId
    ruleSystemMatchesConclusion : ruleSystem ≡ Algebra.legalSystem (Algebra.conclusion r)
    jurisdictionSystemMatchesRule : Algebra.legalSystem jurisdictionPredicate ≡ ruleSystem
    temporalSystemMatchesRule : Algebra.legalSystem temporalPredicate ≡ ruleSystem
    realisationReference : String

open SourceRealisedLegalRule public

record SourceProjectionAudit (graph : Algebra.LegalGraph) : Set₁ where
  constructor source-projection-audit
  field
    candidateRule : Algebra.LegalRule → Set
    sourcedRule : Algebra.LegalRule → Set
    authorityAdmissibleRule : Algebra.LegalRule → Set
    sourcedImpliesCandidate : ∀ {r} → sourcedRule r → candidateRule r
    authorityImpliesSourced : ∀ {r} → authorityAdmissibleRule r → sourcedRule r
    projectionReference : String

open SourceProjectionAudit public

data NegativeClauseOf (r : Algebra.LegalRule) (p : Algebra.LegalProposition) : Set where
  exceptionClause : Algebra._∈_ p (Algebra.exceptions r) → NegativeClauseOf r p
  defeaterClause : Algebra._∈_ p (Algebra.defeaters r) → NegativeClauseOf r p

record SourceFilterSafety
    (graph : Algebra.LegalGraph)
    (facts : Algebra.FactSet)
    (Strong Weak : Algebra.LegalRule → Set) : Set₁ where
  constructor source-filter-safety
  field
    positiveInclusion : ∀ {r} → Strong r → Weak r
    negativeReflection :
      ∀ {r p} → Strong r → NegativeClauseOf r p →
      Algebra.Derivation graph facts Weak p → Algebra.Derivation graph facts Strong p
    safetyReference : String

open SourceFilterSafety public

mutual
  liftDerivationUnderSafeSourceFilter :
    ∀ {graph facts Strong Weak p} →
    SourceFilterSafety graph facts Strong Weak →
    Algebra.Derivation graph facts Strong p →
    Algebra.Derivation graph facts Weak p
  liftDerivationUnderSafeSourceFilter safety (Algebra.fromFact fact) = Algebra.fromFact fact
  liftDerivationUnderSafeSourceFilter safety
    (Algebra.byRule {r = r} inGraph strong premises noExceptions noDefeaters) =
    Algebra.byRule inGraph (positiveInclusion safety strong)
      (liftAllPositive safety premises)
      (liftAllNegative safety strong exceptionMarker noExceptions)
      (liftAllNegative safety strong defeaterMarker noDefeaters)
    where
      exceptionMarker : ∀ {p} → Algebra._∈_ p (Algebra.exceptions r) → NegativeClauseOf r p
      exceptionMarker membership = exceptionClause membership
      defeaterMarker : ∀ {p} → Algebra._∈_ p (Algebra.defeaters r) → NegativeClauseOf r p
      defeaterMarker membership = defeaterClause membership

  liftAllPositive :
    ∀ {graph facts Strong Weak ps} →
    SourceFilterSafety graph facts Strong Weak →
    Algebra.All (Algebra.Derivation graph facts Strong) ps →
    Algebra.All (Algebra.Derivation graph facts Weak) ps
  liftAllPositive safety Algebra.[] = Algebra.[]
  liftAllPositive safety (p Algebra.∷ ps) =
    liftDerivationUnderSafeSourceFilter safety p Algebra.∷ liftAllPositive safety ps

  liftAllNegative :
    ∀ {graph facts Strong Weak r ps} →
    SourceFilterSafety graph facts Strong Weak → Strong r →
    (∀ {p} → Algebra._∈_ p ps → NegativeClauseOf r p) →
    Algebra.All (λ p → Algebra.Derivation graph facts Strong p → ⊥) ps →
    Algebra.All (λ p → Algebra.Derivation graph facts Weak p → ⊥) ps
  liftAllNegative safety strong mark Algebra.[] = Algebra.[]
  liftAllNegative {ps = p ∷ ps} safety strong mark (notP Algebra.∷ notPs) =
    (λ weakP → notP (negativeReflection safety strong (mark Algebra.here) weakP)) Algebra.∷
    liftAllNegative safety strong (λ membership → mark (Algebra.there membership)) notPs

sourceFilteringCannotCreateReachabilityWhenNegativeClosed :
  ∀ {graph facts Strong Weak p} →
  SourceFilterSafety graph facts Strong Weak →
  Algebra.Derivation graph facts Strong p →
  Algebra.Derivation graph facts Weak p
sourceFilteringCannotCreateReachabilityWhenNegativeClosed = liftDerivationUnderSafeSourceFilter

data CitationAloneRealisesLegalRule : Set where
data RuleStringScopePaysJurisdiction : Set where
data RuleStringScopePaysTemporalValidity : Set where
data SourceFilteringAlwaysMonotoneWithDefeaters : Set where
data LaterCitationRestoresErasedPrimaryLineage : Set where
data UnsourcedConclusionMayBeProducedBySourcedRule : Set where

citationAloneDoesNotRealiseLegalRule : CitationAloneRealisesLegalRule → ⊥
citationAloneDoesNotRealiseLegalRule ()
jurisdictionStringDoesNotPayJurisdiction : RuleStringScopePaysJurisdiction → ⊥
jurisdictionStringDoesNotPayJurisdiction ()
temporalStringDoesNotPayTemporalValidity : RuleStringScopePaysTemporalValidity → ⊥
temporalStringDoesNotPayTemporalValidity ()
sourceFilteringIsNotUnconditionallyMonotone : SourceFilteringAlwaysMonotoneWithDefeaters → ⊥
sourceFilteringIsNotUnconditionallyMonotone ()
laterCitationDoesNotRestoreErasedPrimaryLineage : LaterCitationRestoresErasedPrimaryLineage → ⊥
laterCitationDoesNotRestoreErasedPrimaryLineage ()
unsourcedConclusionCannotBeProducedBySourcedRule : UnsourcedConclusionMayBeProducedBySourcedRule → ⊥
unsourcedConclusionCannotBeProducedBySourcedRule ()

record SourceRealisedLegalRuleBoundary : Set where
  constructor source-realised-legal-rule-boundary
  field
    primarySourcePropositionSeparatedFromReconstruction : Bool
    conclusionSourceRequired : Bool
    premiseSourcesRequired : Bool
    exceptionSourcesRequired : Bool
    defeaterSourcesRequired : Bool
    typedJurisdictionSourceRequired : Bool
    typedTemporalSourceRequired : Bool
    sourceFormAndPropositionRoleSeparated : Bool
    citationCreatesAuthority : Bool
    sourceFilteringMonotoneWithoutNegativeClosure : Bool

canonicalSourceRealisedLegalRuleBoundary : SourceRealisedLegalRuleBoundary
canonicalSourceRealisedLegalRuleBoundary =
  source-realised-legal-rule-boundary true true true true true true true true false false

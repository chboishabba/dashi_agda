module DASHI.Cognition.PNF.SensibLawPrecedentApplicabilityDistinguishingExact where

------------------------------------------------------------------------
-- PRECEDENT PROPOSITION / APPLICABILITY / DISTINGUISHING ALGEBRA
--
-- A judgment is a source container. Its propositions may have different legal
-- roles: ratio, dictum, factual finding, concurrence, dissent, policy reason,
-- submission, etc. Applicability to a later case requires proof-bearing fit;
-- textual similarity does not establish precedent application.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra

------------------------------------------------------------------------
-- Proposition role within a case source.
------------------------------------------------------------------------

data JudgmentPropositionRole : Set where
  ratio
  dictum
  adjudicatedFact
  policyReason
  partySubmission
  concurrence
  dissent
  proceduralHolding
  remedyHolding
  : JudgmentPropositionRole

record PrecedentProposition : Set where
  constructor precedent-proposition
  field
    caseSource : Algebra.LegalSourceRef
    court : String
    jurisdiction : String
    decisionDate : String
    proposition : Algebra.LegalProposition
    role : JudgmentPropositionRole
    majoritySupport : Bool
    issueReference : Ontology.StableId
    materialFeatures : List Algebra.LegalProposition
    laterTreatmentReference : String

open PrecedentProposition public

------------------------------------------------------------------------
-- Later treatment is proposition-specific rather than whole-case magic.
------------------------------------------------------------------------

data LaterTreatment : Set where
  followed
  applied
  distinguished
  doubted
  disapproved
  overruled
  supersededByStatute
  notYetClassified
  : LaterTreatment

record TreatmentReceipt (p : PrecedentProposition) : Set where
  constructor treatment-receipt
  field
    treatment : LaterTreatment
    laterSource : Algebra.LegalSourceRef
    treatedProposition : Algebra.LegalProposition
    sameProposition : treatedProposition ≡ proposition p
    treatmentStatement : String

open TreatmentReceipt public

------------------------------------------------------------------------
-- Current-case features.
------------------------------------------------------------------------

record CurrentCase : Set where
  constructor current-case
  field
    caseId : Ontology.StableId
    legalSystem : Ontology.StableId
    jurisdiction : String
    issueReference : Ontology.StableId
    factsAndFeatures : List Algebra.LegalProposition

open CurrentCase public

------------------------------------------------------------------------
-- Legacy material factual/doctrinal correspondence.
--
-- Kept for compatibility. `mapsFeature` is selected inside the witness, so this
-- shape is not strong enough by itself for promotion from a finite missing-
-- feature search. The policy-indexed layer below is the preferred executable
-- promotion surface.
------------------------------------------------------------------------

record FeatureMap (p : PrecedentProposition) (c : CurrentCase) : Set where
  constructor feature-map
  field
    mapsFeature : Algebra.LegalProposition → Algebra.LegalProposition → Set
    everyMaterialPrecedentFeatureMapped :
      ∀ {f} → Algebra._∈_ f (materialFeatures p) →
      Σ Algebra.LegalProposition (λ g →
        Algebra._∈_ g (factsAndFeatures c) × mapsFeature f g)

open FeatureMap public

record PrecedentApplicable (p : PrecedentProposition) (c : CurrentCase) : Set where
  constructor precedent-applicable
  field
    jurisdictionCompatible : String
    issueIdentity : issueReference p ≡ issueReference c
    roleCanCarryRule : Set
    featureMap : FeatureMap p c
    notOverruledForThisProposition : Set

open PrecedentApplicable public

------------------------------------------------------------------------
-- Distinguishing is a proof-bearing material difference set.
------------------------------------------------------------------------

record MaterialDifference (p : PrecedentProposition) (c : CurrentCase) : Set where
  constructor material-difference
  field
    precedentFeature : Algebra.LegalProposition
    currentFeature : Algebra.LegalProposition
    precedentFeatureWasMaterial :
      Algebra._∈_ precedentFeature (materialFeatures p)
    differenceStatement : String
    legallyMaterialBecause : Algebra.LegalSourceRef

open MaterialDifference public

record DistinguishingSet (p : PrecedentProposition) (c : CurrentCase) : Set where
  constructor distinguishing-set
  field
    differences : List (MaterialDifference p c)
    nonEmptyDifference : Set
    distinctionDefeatsOrNarrowsApplication : Set

open DistinguishingSet public

record MinimalDistinguishingSet (p : PrecedentProposition) (c : CurrentCase) : Set where
  constructor minimal-distinguishing-set
  field
    distinguishing : DistinguishingSet p c
    sufficientAgainstApplication : PrecedentApplicable p c → ⊥
    eachDifferenceNecessary :
      ∀ {d} →
      Algebra._∈_ d (DistinguishingSet.differences distinguishing) → Set

open MinimalDistinguishingSet public

------------------------------------------------------------------------
-- Preferred policy-indexed applicability layer.
--
-- A correspondence policy is fixed before application is attempted. This avoids
-- both unsound extremes:
--   * `same StableId` silently becoming universal materiality;
--   * the applicability witness privately choosing any relation it needs.
------------------------------------------------------------------------

record MaterialCorrespondencePolicy
  (p : PrecedentProposition)
  (c : CurrentCase) : Set where
  constructor material-correspondence-policy
  field
    corresponds : Algebra.LegalProposition → Algebra.LegalProposition → Set
    criterionLabel : String
    criterionAuthority : Algebra.LegalSourceRef
    criterionItselfRequiresLegalJustification : Bool

open MaterialCorrespondencePolicy public

record PolicyFeatureMap
  {p : PrecedentProposition}
  {c : CurrentCase}
  (policy : MaterialCorrespondencePolicy p c) : Set where
  constructor policy-feature-map
  field
    everyMaterialFeatureMappedUnderPolicy :
      ∀ {f} → Algebra._∈_ f (materialFeatures p) →
      Σ Algebra.LegalProposition (λ g →
        Algebra._∈_ g (factsAndFeatures c) ×
        MaterialCorrespondencePolicy.corresponds policy f g)

open PolicyFeatureMap public

record PolicyPrecedentApplicable
  {p : PrecedentProposition}
  {c : CurrentCase}
  (policy : MaterialCorrespondencePolicy p c) : Set where
  constructor policy-precedent-applicable
  field
    jurisdictionCompatibleUnderPolicy : String
    issueIdentityUnderPolicy : issueReference p ≡ issueReference c
    roleCanCarryRuleUnderPolicy : Set
    policyFeatureMap : PolicyFeatureMap policy
    notOverruledForThisPropositionUnderPolicy : Set

open PolicyPrecedentApplicable public

record PolicyMinimalDistinguishingSet
  {p : PrecedentProposition}
  {c : CurrentCase}
  (policy : MaterialCorrespondencePolicy p c) : Set where
  constructor policy-minimal-distinguishing-set
  field
    policyDistinguishing : DistinguishingSet p c
    sufficientAgainstPolicyApplication :
      PolicyPrecedentApplicable policy → ⊥
    eachPolicyDifferenceNecessary :
      ∀ {d} →
      Algebra._∈_ d (DistinguishingSet.differences policyDistinguishing) → Set

open PolicyMinimalDistinguishingSet public

------------------------------------------------------------------------
-- Role-to-authority bridge.
------------------------------------------------------------------------

roleAuthority : JudgmentPropositionRole → Algebra.AuthorityRole
roleAuthority ratio = Algebra.bindingRatioRole
roleAuthority dictum = Algebra.dictumRole
roleAuthority adjudicatedFact = Algebra.adjudicatedFactRole
roleAuthority policyReason = Algebra.judicialPolicyReasonRole
roleAuthority partySubmission = Algebra.partySubmissionRole
roleAuthority concurrence = Algebra.concurrenceRole
roleAuthority dissent = Algebra.dissentRole
roleAuthority proceduralHolding = Algebra.bindingRatioRole
roleAuthority remedyHolding = Algebra.bindingRatioRole

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameCaseMeansSameAuthorityRole : Set where
data SimilarFactsAutomaticallyApplyPrecedent : Set where
data DistinctionAutomaticallyOverrulesPrecedent : Set where
data DissentIsBindingRatioBySourceContainer : Set where
data LegacyFeatureMapSupportsExecutablePromotionByItself : Set where
data OneCorrespondencePolicyIsUniversalMateriality : Set where

sameCaseDoesNotFlattenRoles : SameCaseMeansSameAuthorityRole → ⊥
sameCaseDoesNotFlattenRoles ()

similarityDoesNotProveApplication : SimilarFactsAutomaticallyApplyPrecedent → ⊥
similarityDoesNotProveApplication ()

distinguishingDoesNotOverrule : DistinctionAutomaticallyOverrulesPrecedent → ⊥
distinguishingDoesNotOverrule ()

dissentDoesNotBecomeBindingRatio : DissentIsBindingRatioBySourceContainer → ⊥
dissentDoesNotBecomeBindingRatio ()

legacyFeatureMapDoesNotSupportSafeSearchPromotion :
  LegacyFeatureMapSupportsExecutablePromotionByItself → ⊥
legacyFeatureMapDoesNotSupportSafeSearchPromotion ()

correspondencePolicyDoesNotBecomeUniversalLaw :
  OneCorrespondencePolicyIsUniversalMateriality → ⊥
correspondencePolicyDoesNotBecomeUniversalLaw ()

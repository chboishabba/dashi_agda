module DASHI.Cognition.PNF.SensibLawPrecedentApplicabilityDistinguishingExact where

------------------------------------------------------------------------
-- PRECEDENT PROPOSITION / APPLICABILITY / DISTINGUISHING ALGEBRA
--
-- A judgment is a source container. Its propositions may have different legal
-- roles: ratio, dictum, factual finding, concurrence, dissent, policy reason,
-- submission, etc. Applicability to a later case requires proof-bearing fit;
-- textual similarity does not establish precedent application.
--
-- This version makes the material-correspondence theory explicit. A consumer
-- cannot manufacture applicability by choosing an arbitrary private `mapsFeature`
-- relation inside the applicability proof itself. Conversely, this module does
-- not impose StableId equality as a universal legal-materiality criterion.
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
-- Material factual/doctrinal correspondence is consumer/source-theory indexed.
--
-- Examples of correspondence theories may demand literal identity, a recognised
-- doctrinal analogue, or a source-backed mapping. The theory is fixed *before*
-- an applicability witness is supplied.
------------------------------------------------------------------------

record ApplicabilityTheory
  (p : PrecedentProposition)
  (c : CurrentCase) : Set where
  constructor applicability-theory
  field
    corresponds : Algebra.LegalProposition → Algebra.LegalProposition → Set
    criterionLabel : String
    criterionAuthority : Algebra.LegalSourceRef
    criterionItselfRequiresLegalJustification : Bool

open ApplicabilityTheory public

record FeatureMap
  {p : PrecedentProposition}
  {c : CurrentCase}
  (theory : ApplicabilityTheory p c) : Set where
  constructor feature-map
  field
    everyMaterialPrecedentFeatureMapped :
      ∀ {f} → Algebra._∈_ f (materialFeatures p) →
      Σ Algebra.LegalProposition (λ g →
        Algebra._∈_ g (factsAndFeatures c) ×
        ApplicabilityTheory.corresponds theory f g)

open FeatureMap public

record PrecedentApplicable
  {p : PrecedentProposition}
  {c : CurrentCase}
  (theory : ApplicabilityTheory p c) : Set where
  constructor precedent-applicable
  field
    jurisdictionCompatible : String
    issueIdentity : issueReference p ≡ issueReference c
    roleCanCarryRule : Set
    featureMap : FeatureMap theory
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

------------------------------------------------------------------------
-- A minimal distinguishing set is relative to an explicit applicability theory.
-- This prevents two opposite errors:
--   * executable mismatch -> universal doctrinal distinction;
--   * arbitrary correspondence relation -> automatic applicability.
------------------------------------------------------------------------

record MinimalDistinguishingSet
  {p : PrecedentProposition}
  {c : CurrentCase}
  (theory : ApplicabilityTheory p c) : Set where
  constructor minimal-distinguishing-set
  field
    distinguishing : DistinguishingSet p c
    sufficientAgainstApplication : PrecedentApplicable theory → ⊥
    eachDifferenceNecessary :
      ∀ {d} →
      Algebra._∈_ d (DistinguishingSet.differences distinguishing) → Set

open MinimalDistinguishingSet public

------------------------------------------------------------------------
-- Role-to-authority bridge. This keeps source form separate from proposition
-- role, while allowing ratios/other roles to participate in the universal graph.
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
data ApplicabilityMayChoosePrivateCorrespondenceTheory : Set where

data OneCorrespondenceTheoryIsUniversalMateriality : Set where

sameCaseDoesNotFlattenRoles : SameCaseMeansSameAuthorityRole → ⊥
sameCaseDoesNotFlattenRoles ()

similarityDoesNotProveApplication : SimilarFactsAutomaticallyApplyPrecedent → ⊥
similarityDoesNotProveApplication ()

distinguishingDoesNotOverrule : DistinctionAutomaticallyOverrulesPrecedent → ⊥
distinguishingDoesNotOverrule ()

dissentDoesNotBecomeBindingRatio : DissentIsBindingRatioBySourceContainer → ⊥
dissentDoesNotBecomeBindingRatio ()

applicabilityUsesSuppliedTheory : ApplicabilityMayChoosePrivateCorrespondenceTheory → ⊥
applicabilityUsesSuppliedTheory ()

correspondenceTheoryDoesNotBecomeUniversalLaw :
  OneCorrespondenceTheoryIsUniversalMateriality → ⊥
correspondenceTheoryDoesNotBecomeUniversalLaw ()

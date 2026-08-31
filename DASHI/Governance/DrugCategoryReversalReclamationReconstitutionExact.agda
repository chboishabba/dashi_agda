module DASHI.Governance.DrugCategoryReversalReclamationReconstitutionExact where

open import DASHI.Core.Prelude

import DASHI.Governance.SuffrageWitchReclamationGenealogyExact as FeministGenealogy
import DASHI.Governance.FeministDrugClassificationAuthorityExact as Authority
import DASHI.Governance.CountercultureDrugReclassificationHistoryExact as Counterculture

------------------------------------------------------------------------
-- DRUG CATEGORY REVERSAL / RECLAMATION / RECONSTITUTION
--
-- Cross-pollinates the feminist genealogy rule:
--   value reversal != imposed-category reclamation != positive subject
--   reconstitution.
--
-- A state or market can change the sign of an inherited drug category without
-- changing who authors the classifier grammar.  A formerly deviant/criminalized
-- psychedelic can therefore become "therapeutic" while the affected subject or
-- community remains represented rather than originating the new category.
------------------------------------------------------------------------

data DrugRechartOperation : Set where
  negativeToPositiveValueReversal
  imposedDrugCategoryReclamation
  subjectAuthoredReconstitution
  communityAuthoredReconstitution
  sovereignCeremonialReconstitution
  : DrugRechartOperation

valueReversal≠reclamation :
  negativeToPositiveValueReversal ≡ imposedDrugCategoryReclamation → ⊥
valueReversal≠reclamation ()

reclamation≠subjectReconstitution :
  imposedDrugCategoryReclamation ≡ subjectAuthoredReconstitution → ⊥
reclamation≠subjectReconstitution ()

reclamation≠communityReconstitution :
  imposedDrugCategoryReclamation ≡ communityAuthoredReconstitution → ⊥
reclamation≠communityReconstitution ()

communityReconstitution≠sovereignReconstitution :
  communityAuthoredReconstitution ≡ sovereignCeremonialReconstitution → ⊥
communityReconstitution≠sovereignReconstitution ()

------------------------------------------------------------------------
-- Finite category-history fixture.
------------------------------------------------------------------------

data DrugCategoryHistoryState : Set where
  criminalizedCountercultureState
  stateTherapeuticReversalState
  commercialPsychedelicReclamationState
  patientSubjectReconstitutionState
  indigenousSovereignReconstitutionState
  : DrugCategoryHistoryState

data ValueSign : Set where
  negativeValue positiveValue : ValueSign

data CategoryAuthorPosition : Set where
  externalStateAuthor
  commercialAuthor
  affectedSubjectAuthor
  affectedCommunityAuthor
  sovereignCommunityAuthor
  : CategoryAuthorPosition

valueSign : DrugCategoryHistoryState → ValueSign
valueSign criminalizedCountercultureState = negativeValue
valueSign stateTherapeuticReversalState = positiveValue
valueSign commercialPsychedelicReclamationState = positiveValue
valueSign patientSubjectReconstitutionState = positiveValue
valueSign indigenousSovereignReconstitutionState = positiveValue

authorPosition : DrugCategoryHistoryState → CategoryAuthorPosition
authorPosition criminalizedCountercultureState = externalStateAuthor
authorPosition stateTherapeuticReversalState = externalStateAuthor
authorPosition commercialPsychedelicReclamationState = commercialAuthor
authorPosition patientSubjectReconstitutionState = affectedSubjectAuthor
authorPosition indigenousSovereignReconstitutionState = sovereignCommunityAuthor

samePositiveValueDifferentAuthor :
  valueSign stateTherapeuticReversalState
  ≡ valueSign patientSubjectReconstitutionState
samePositiveValueDifferentAuthor = refl

authorDiffersAfterSamePositiveValue :
  authorPosition stateTherapeuticReversalState
  ≡ authorPosition patientSubjectReconstitutionState → ⊥
authorDiffersAfterSamePositiveValue ()

commercialAndSovereignReconstitutionDiffer :
  authorPosition commercialPsychedelicReclamationState
  ≡ authorPosition indigenousSovereignReconstitutionState → ⊥
commercialAndSovereignReconstitutionDiffer ()

------------------------------------------------------------------------
-- Boundaries: medical/commercial positive revaluation can be historically real
-- without constituting subject/community authorship or repairing prior harms.
------------------------------------------------------------------------

data PositiveMedicalValuePromotesSubjectAuthorship : Set where

data CommercialReclamationPromotesCommunityAuthority : Set where

data TherapeuticReversalPromotesHistoricalRepair : Set where

data ReclassificationPromotesRetroactiveDecriminalization : Set where

positiveMedicalValueDoesNotPromoteSubjectAuthorship :
  PositiveMedicalValuePromotesSubjectAuthorship → ⊥
positiveMedicalValueDoesNotPromoteSubjectAuthorship ()

commercialReclamationDoesNotPromoteCommunityAuthority :
  CommercialReclamationPromotesCommunityAuthority → ⊥
commercialReclamationDoesNotPromoteCommunityAuthority ()

therapeuticReversalDoesNotPromoteHistoricalRepair :
  TherapeuticReversalPromotesHistoricalRepair → ⊥
therapeuticReversalDoesNotPromoteHistoricalRepair ()

reclassificationDoesNotPromoteRetroactiveDecriminalization :
  ReclassificationPromotesRetroactiveDecriminalization → ⊥
reclassificationDoesNotPromoteRetroactiveDecriminalization ()

feministGenealogyBoundary : FeministGenealogy.SuffrageWitchGenealogyBoundary
feministGenealogyBoundary = FeministGenealogy.canonicalSuffrageWitchGenealogyBoundary

authorityBoundary : Authority.FeministDrugClassificationAuthorityBoundary
authorityBoundary = Authority.canonicalFeministDrugClassificationAuthorityBoundary

countercultureBoundary : Counterculture.CountercultureDrugReclassificationBoundary
countercultureBoundary = Counterculture.canonicalCountercultureDrugReclassificationBoundary

record DrugCategoryRechartBoundary : Set where
  constructor drugCategoryRechartBoundary
  field
    positiveRevaluationEqualsSubjectReconstitution : Bool
    positiveRevaluationEqualsSubjectReconstitutionIsFalse :
      positiveRevaluationEqualsSubjectReconstitution ≡ false
    medicalReclassificationEqualsHistoricalRepair : Bool
    medicalReclassificationEqualsHistoricalRepairIsFalse :
      medicalReclassificationEqualsHistoricalRepair ≡ false
    commercialReclamationEqualsCommunityAuthorship : Bool
    commercialReclamationEqualsCommunityAuthorshipIsFalse :
      commercialReclamationEqualsCommunityAuthorship ≡ false
    samePositiveCategoryCanHideDifferentCategoryAuthors : Bool
    samePositiveCategoryCanHideDifferentCategoryAuthorsIsTrue :
      samePositiveCategoryCanHideDifferentCategoryAuthors ≡ true
    sovereignReconstitutionIsDistinctFromCommercialReclamation : Bool
    sovereignReconstitutionIsDistinctFromCommercialReclamationIsTrue :
      sovereignReconstitutionIsDistinctFromCommercialReclamation ≡ true

canonicalDrugCategoryRechartBoundary : DrugCategoryRechartBoundary
canonicalDrugCategoryRechartBoundary =
  drugCategoryRechartBoundary
    false refl
    false refl
    false refl
    true refl
    true refl

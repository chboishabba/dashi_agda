module DASHI.Reasoning.ComparativeInstitutionalMeaningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COMPARATIVE INSTITUTIONAL MEANING
--
-- Structural interpretation becomes causal only relative to an explicit
-- institutional contrast.  A political-economy label by itself is not a
-- counterfactual.  This owner records which coordinates are matched, which
-- institutional coordinates differ, which outcome is compared, and what
-- mediation/comparability receipts warrant the comparison.
------------------------------------------------------------------------

data InstitutionalCoordinate : Set where
  ownershipCoordinate
  profitIncentiveCoordinate
  externalityAllocationCoordinate
  regulatoryRuleCoordinate
  enforcementCapacityCoordinate
  informationTransparencyCoordinate
  patientVoiceCoordinate
  productionTechnologyCoordinate
  productStandardCoordinate
  populationCoordinate
  timeCoordinate
  : InstitutionalCoordinate

data CoordinateRelation : Set where
  heldMatched intentionallyVaried unresolvedCoordinate : CoordinateRelation

record InstitutionalWorld : Set₁ where
  constructor institutionalWorld
  field
    WorldState : Set
    worldState : WorldState
    coordinateRelation : InstitutionalCoordinate → CoordinateRelation
    worldReference : String
    provenanceReference : String

open InstitutionalWorld public

record MatchedInstitutionalContrast
    (actual alternative : InstitutionalWorld) : Set₁ where
  constructor matchedInstitutionalContrast
  field
    matchedCoordinate : InstitutionalCoordinate → Set
    variedCoordinate : InstitutionalCoordinate → Set
    noCoordinateBothMatchedAndVaried :
      (coordinate : InstitutionalCoordinate) →
      matchedCoordinate coordinate →
      variedCoordinate coordinate →
      ⊥
    matchingReference : String
    variationReference : String
    comparabilityReference : String

open MatchedInstitutionalContrast public

record InstitutionalOutcomeComparison
    {actual alternative : InstitutionalWorld}
    (contrast : MatchedInstitutionalContrast actual alternative) : Set₁ where
  constructor institutionalOutcomeComparison
  field
    Outcome : Set
    actualOutcome : Outcome
    alternativeOutcome : Outcome
    outcomeDifference : actualOutcome ≡ alternativeOutcome → ⊥
    measurementReference : String
    transportReference : String
    nuisanceReference : String

open InstitutionalOutcomeComparison public

record StructuralMediationReceipt
    {actual alternative : InstitutionalWorld}
    {contrast : MatchedInstitutionalContrast actual alternative}
    (comparison : InstitutionalOutcomeComparison contrast) : Set where
  constructor structuralMediationReceipt
  field
    structuralCoordinate : InstitutionalCoordinate
    coordinateActuallyVaried :
      variedCoordinate contrast structuralCoordinate
    mediatorReference : String
    temporalOrderingReference : String
    alternativeMechanismAuditReference : String
    causalScopeReference : String

open StructuralMediationReceipt public

record ComparativeStructuralMeaning
    {actual alternative : InstitutionalWorld}
    {contrast : MatchedInstitutionalContrast actual alternative}
    (comparison : InstitutionalOutcomeComparison contrast) : Set₁ where
  constructor comparativeStructuralMeaning
  field
    mediation : StructuralMediationReceipt comparison
    recurrenceReference : String
    ownershipAndIncentiveReference : String
    externalityReference : String
    governanceReference : String
    counterfactualReference : String
    interpretationReference : String

open ComparativeStructuralMeaning public

------------------------------------------------------------------------
-- Boundaries: labels and raw outcome differences do not manufacture the
-- matched/counterfactual structure required for structural attribution.
------------------------------------------------------------------------

data PoliticalEconomyLabel : Set where
  capitalismLabel cooperativeLabel publicProvisionLabel mixedEconomyLabel
  : PoliticalEconomyLabel

record ComparativeInstitutionalMeaningBoundary : Set where
  constructor comparativeInstitutionalMeaningBoundary
  field
    politicalEconomyLabelIsCounterfactualWorld : Bool
    politicalEconomyLabelIsCounterfactualWorldIsFalse :
      politicalEconomyLabelIsCounterfactualWorld ≡ false
    observedOutcomeDifferenceAloneIdentifiesStructuralCause : Bool
    observedOutcomeDifferenceAloneIdentifiesStructuralCauseIsFalse :
      observedOutcomeDifferenceAloneIdentifiesStructuralCause ≡ false
    structuralMeaningRequiresExplicitVariedCoordinate : Bool
    structuralMeaningRequiresExplicitVariedCoordinateIsTrue :
      structuralMeaningRequiresExplicitVariedCoordinate ≡ true
    structuralMeaningRequiresMatchingAndComparability : Bool
    structuralMeaningRequiresMatchingAndComparabilityIsTrue :
      structuralMeaningRequiresMatchingAndComparability ≡ true
    structuralMeaningRequiresMediationAudit : Bool
    structuralMeaningRequiresMediationAuditIsTrue :
      structuralMeaningRequiresMediationAudit ≡ true

canonicalComparativeInstitutionalMeaningBoundary :
  ComparativeInstitutionalMeaningBoundary
canonicalComparativeInstitutionalMeaningBoundary =
  comparativeInstitutionalMeaningBoundary
    false refl
    false refl
    true refl
    true refl
    true refl

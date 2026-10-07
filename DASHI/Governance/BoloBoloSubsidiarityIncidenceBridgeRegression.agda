module DASHI.Governance.BoloBoloSubsidiarityIncidenceBridgeRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloSubsidiarityIncidenceBridgeExact as Bridge
import DASHI.Governance.FederatedDecisionIncidenceFiniteExampleExact as Example

sourceDesignDoesNotBecomeDASHIOntology :
  Bridge.sourceArchitectureEqualsFormalSubsidiarityOntology Bridge.canonicalBoloSubsidiarityBridgeBoundary ≡ false
sourceDesignDoesNotBecomeDASHIOntology = refl

localityContractionIsConditional :
  Bridge.localityContractionRequiresSubsidiarityAndOutsiderWitness Bridge.canonicalBoloSubsidiarityBridgeBoundary ≡ true
localityContractionIsConditional = refl

finiteSpecimenExercisesBoloBridge :
  Bridge.BoloLocalityContraction
    Example.exampleGovernance
    Example.localAIssue
    Example.federationIssue
finiteSpecimenExercisesBoloBridge =
  Bridge.exampleBoloLocalityContraction

contractionIsNotCostLaw :
  Bridge.strictContractionIsEmpiricalCostReduction Bridge.canonicalBoloSubsidiarityBridgeBoundary ≡ false
contractionIsNotCostLaw = refl

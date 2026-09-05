module DASHI.Law.MissingnessMechanismFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Missingness is attached to the observation as a proof-relevant mechanism
-- fibre.  We do not collapse mechanisms to a single global MCAR/MAR/MNAR tag.
------------------------------------------------------------------------

data DependencyState : Set where
  depends doesNotDepend dependencyUnresolved : DependencyState

record MissingnessMechanismFibre : Set where
  constructor missingnessMechanismFibre
  field
    dependsOnGroup : DependencyState
    dependsOnSelection : DependencyState
    dependsOnOutcome : DependencyState
    dependsOnOfficer : DependencyState
    dependsOnDeployment : DependencyState
    dependsOnObservedCovariates : DependencyState
    unobservedDependencyPossible : Bool
    mechanismReference : String

open MissingnessMechanismFibre public

record MissingObservation : Set where
  constructor missingObservation
  field
    observationReference : String
    mechanism : MissingnessMechanismFibre
    mechanismEvidenceReference : String

open MissingObservation public

------------------------------------------------------------------------
-- Assumption classes are derived summaries of fibres, not substitutes for the
-- underlying dependency coordinates.
------------------------------------------------------------------------

data MechanismClass : Set where
  unrestrictedMissingness
  observationIndependentMissingness
  observedCovariateConditionedMissingness
  nonIgnorableOrUnresolvedMissingness : MechanismClass

allNoObservedDependencies : MissingnessMechanismFibre → Bool
allNoObservedDependencies m with dependsOnGroup m
... | doesNotDepend with dependsOnSelection m
...   | doesNotDepend with dependsOnOutcome m
...     | doesNotDepend with dependsOnOfficer m
...       | doesNotDepend with dependsOnDeployment m
...         | doesNotDepend with dependsOnObservedCovariates m
...           | doesNotDepend = true
...           | _ = false
...         | _ = false
...       | _ = false
...     | _ = false
...   | _ = false
... | _ = false

classifyMechanism : MissingnessMechanismFibre → MechanismClass
classifyMechanism m with allNoObservedDependencies m | unobservedDependencyPossible m
... | true | false = observationIndependentMissingness
... | true | true = nonIgnorableOrUnresolvedMissingness
... | false | _ with dependsOnObservedCovariates m | unobservedDependencyPossible m
...   | depends | false = observedCovariateConditionedMissingness
...   | _ | _ = nonIgnorableOrUnresolvedMissingness

canonicalUnrestrictedMechanism : MissingnessMechanismFibre
canonicalUnrestrictedMechanism = missingnessMechanismFibre
  dependencyUnresolved dependencyUnresolved dependencyUnresolved
  dependencyUnresolved dependencyUnresolved dependencyUnresolved true
  "baseline: no missingness-independence assumption"

canonicalOutcomeDependentMechanism : MissingnessMechanismFibre
canonicalOutcomeDependentMechanism = missingnessMechanismFibre
  doesNotDepend doesNotDepend depends doesNotDepend doesNotDepend
  doesNotDepend true
  "synthetic outcome-dependent missingness witness"

canonicalIndependentMechanism : MissingnessMechanismFibre
canonicalIndependentMechanism = missingnessMechanismFibre
  doesNotDepend doesNotDepend doesNotDepend doesNotDepend doesNotDepend
  doesNotDepend false
  "synthetic observation-independent missingness witness"

canonicalUnrestrictedClass :
  classifyMechanism canonicalUnrestrictedMechanism ≡ nonIgnorableOrUnresolvedMissingness
canonicalUnrestrictedClass = refl

canonicalIndependentClass :
  classifyMechanism canonicalIndependentMechanism ≡ observationIndependentMissingness
canonicalIndependentClass = refl

------------------------------------------------------------------------
-- Consumer-specific BIDI obligations.
------------------------------------------------------------------------

data MechanismClaim : Set where
  unrestrictedWorstCaseBounds
  narrowedBoundsUnderIndependence
  completeCaseRepresentsPopulation : MechanismClaim

data MechanismProducer : Set where
  unresolvedMassProducer
  missingnessIndependenceReceipt
  completeCaseTransportReceipt : MechanismProducer

reverseMechanism : MechanismClaim → MechanismProducer
reverseMechanism unrestrictedWorstCaseBounds = unresolvedMassProducer
reverseMechanism narrowedBoundsUnderIndependence = missingnessIndependenceReceipt
reverseMechanism completeCaseRepresentsPopulation = completeCaseTransportReceipt

record MissingnessMechanismBoundary : Set where
  constructor missingnessMechanismBoundary
  field
    missingnessMayBeAssumedIndependentWithoutReceipt : Bool
    missingnessMayBeAssumedIndependentWithoutReceiptIsFalse :
      missingnessMayBeAssumedIndependentWithoutReceipt ≡ false
    completeCaseRateAutomaticallyEqualsPopulationRate : Bool
    completeCaseRateAutomaticallyEqualsPopulationRateIsFalse :
      completeCaseRateAutomaticallyEqualsPopulationRate ≡ false
    narrowerBoundsMayUseUnstatedMechanismAssumption : Bool
    narrowerBoundsMayUseUnstatedMechanismAssumptionIsFalse :
      narrowerBoundsMayUseUnstatedMechanismAssumption ≡ false

canonicalMissingnessMechanismBoundary : MissingnessMechanismBoundary
canonicalMissingnessMechanismBoundary =
  missingnessMechanismBoundary false refl false refl false refl

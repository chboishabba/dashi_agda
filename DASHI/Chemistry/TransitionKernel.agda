module DASHI.Chemistry.TransitionKernel where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Generic chemistry transition kernel.
--
-- This is a solver-neutral, qualitative carrier.  It deliberately does
-- not claim measured rates, molecular identities, or wet-lab validation.
-- Those remain governed by ChemistryQuantitativeAdapter and the existing
-- chemistry/biology promotion obligations.

------------------------------------------------------------------------
-- Material vocabulary.

data Phase : Set where
  solid liquid gas gel emulsion adsorbed dissolved : Phase

data MobilityClass : Set where
  immobile restricted mobile volatile : MobilityClass

data TransitionKind : Set where
  chemicalReaction
  phaseTransition
  bindingTransition
  transportTransition
  opticalTransition
  mechanicalEvent : TransitionKind

data Reversibility : Set where
  irreversible reversible conditionallyReversible : Reversibility

data EvidenceStatus : Set where
  literatureEstablished
  patentDisclosed
  directlyMeasured
  inferredFromOutput
  fitted
  assumed
  unresolved : EvidenceStatus

data ParameterStatus : Set where
  exactParameter intervalParameter symbolicParameter unknownParameter : ParameterStatus

record Interval : Set where
  field
    lower : Nat
    upper : Nat

open Interval public

record Parameter : Set where
  field
    parameterLabel : String
    parameterStatus : ParameterStatus
    parameterInterval : Interval
    evidenceStatus : EvidenceStatus
    provenanceLabel : String

open Parameter public

record Species : Set where
  field
    speciesId : String
    phase : Phase
    chargeLabel : String
    compositionLabel : String
    mobilityClass : MobilityClass
    activityModelLabel : String
    opticalRoleLabel : String
    evidence : EvidenceStatus

open Species public

record StoichiometricTerm : Set where
  field
    species : Species
    coefficient : Nat

open StoichiometricTerm public

------------------------------------------------------------------------
-- Rate-law hierarchy.  Quantitative semantics are supplied externally.

data RateLawKind : Set where
  massAction
  michaelisMenten
  hill
  arrhenius
  empirical
  intervalBounded
  unknownRateLaw : RateLawKind

record RateLaw : Set where
  field
    rateLawKind : RateLawKind
    symbolicForm : String
    parameters : List Parameter
    validityRegime : String
    evidence : EvidenceStatus

open RateLaw public

record Environment : Set where
  field
    temperatureCarrier : String
    pHCarrier : String
    pressureCarrier : String
    humidityCarrier : String
    illuminationCarrier : String
    ionicStrengthCarrier : String

open Environment public

record Condition : Set where
  field
    conditionLabel : String
    environment : Environment
    guardExpression : String

open Condition public

------------------------------------------------------------------------
-- Reactions, physical transitions, binding, and transport share one type.

record Transition : Set where
  field
    transitionId : String
    transitionKind : TransitionKind
    reactants : List StoichiometricTerm
    products : List StoichiometricTerm
    catalysts : List Species
    rateLaw : RateLaw
    condition : Condition
    reversibility : Reversibility
    evidence : EvidenceStatus

open Transition public

------------------------------------------------------------------------
-- Compartment and interface structure.

record Compartment : Set where
  field
    compartmentId : String
    geometryCarrier : String
    phase : Phase
    speciesInventory : List Species
    porosityCarrier : String
    diffusivityCarrier : String

open Compartment public

record Interface : Set where
  field
    interfaceId : String
    leftCompartment : String
    rightCompartment : String
    permeabilityCarrier : String
    adsorptionLawCarrier : String
    interfaceTransitions : List Transition
    opticalBoundaryCarrier : String

open Interface public

record ReactionNetwork : Set where
  field
    networkId : String
    species : List Species
    transitions : List Transition
    compartments : List Compartment
    interfaces : List Interface
    environment : Environment

open ReactionNetwork public

------------------------------------------------------------------------
-- Conservation and malformed-model checks.

record ConservationQuantity : Set where
  field
    quantityLabel : String
    coefficientVectorLabel : String

open ConservationQuantity public

record ConservationWitness : Set where
  field
    quantity : ConservationQuantity
    stoichiometricMatrixLabel : String
    kernelEquation : String
    elementConservationChecked : Bool
    chargeConservationChecked : Bool

open ConservationWitness public

record ConservationCertificate : Set where
  field
    witnesses : List ConservationWitness
    allElementBalancesChecked : Bool
    allChargeBalancesChecked : Bool
    catalystRegenerationChecked : Bool
    conservationPromoted : Bool
    conservationPromotedIsFalse : conservationPromoted ≡ false

open ConservationCertificate public

------------------------------------------------------------------------
-- Hybrid events and transition ordering.

record ChemicalEvent : Set where
  field
    eventId : String
    guardCarrier : String
    stateUpdateCarrier : String
    eventKind : TransitionKind
    evidence : EvidenceStatus

open ChemicalEvent public

data ObligationKind : Set where
  mustNeutralise
  mustImmobilise
  mustConsume
  mustSealInterface
  mustDischargeCharge
  customObligation : ObligationKind

record TransitionObligation : Set where
  field
    obligationId : String
    obligationKind : ObligationKind
    pushedBy : String
    dischargedBy : String
    dischargeCondition : String

open TransitionObligation public

record OrderingConstraint : Set where
  field
    predecessor : String
    successor : String
    orderingMeaning : String

open OrderingConstraint public

record HybridTransitionSystem : Set where
  field
    reactionNetwork : ReactionNetwork
    events : List ChemicalEvent
    obligations : List TransitionObligation
    orderingConstraints : List OrderingConstraint
    continuousEvolutionCarrier : String
    discreteEventCarrier : String

open HybridTransitionSystem public

------------------------------------------------------------------------
-- Reachability, forbidden states, and process windows.

record ProcessWindow : Set where
  field
    startEvent : String
    goalEvent : String
    shutdownEvent : String
    damageEvent : String
    orderingExpression : String
    nonemptyWindow : Bool

open ProcessWindow public

record ReachabilityProblem : Set where
  field
    initialStateCarrier : String
    goalStateCarrier : String
    forbiddenRegionCarrier : String
    transitionSystem : HybridTransitionSystem
    goalReachable : Bool
    forbiddenRegionAvoided : Bool
    obligationsDischarged : Bool

open ReachabilityProblem public

record StabilitySurface : Set where
  field
    endpointCarrier : String
    perturbationCarrier : String
    stabilityCriterion : String
    stableEndpointExists : Bool

open StabilitySurface public

------------------------------------------------------------------------
-- Observables and causal reduction.

record ObservableMap : Set where
  field
    observableId : String
    stateCarrier : String
    outputCarrier : String
    mapExpression : String
    instrumentResponseCarrier : String

open ObservableMap public

record ModelReduction : Set where
  field
    detailedNetwork : ReactionNetwork
    reducedNetwork : ReactionNetwork
    observableSet : List ObservableMap
    observationalEquivalenceCarrier : String
    invariantPreservationCarrier : String
    descriptionLengthCarrier : String
    reductionValidated : Bool

open ModelReduction public

------------------------------------------------------------------------
-- Experiment selection under uncertainty.

record ExperimentCandidate : Set where
  field
    experimentId : String
    measuredCarrier : String
    uncertaintyTarget : String
    expectedModelSpaceReduction : Interval
    protocolReceiptRequired : Bool

open ExperimentCandidate public

record ExperimentSelection : Set where
  field
    candidates : List ExperimentCandidate
    rankingCriterion : String
    selectedExperiment : String
    selectionValidated : Bool

open ExperimentSelection public

------------------------------------------------------------------------
-- Whole-kernel authority boundary.

record ChemistryTransitionKernel : Set₁ where
  field
    system : HybridTransitionSystem
    conservation : ConservationCertificate
    processWindows : List ProcessWindow
    reachabilityProblems : List ReachabilityProblem
    stabilitySurfaces : List StabilitySurface
    observables : List ObservableMap
    reductions : List ModelReduction
    experimentSelection : ExperimentSelection

    quantitativeParametersMeasured : Bool
    quantitativeParametersMeasuredIsFalse :
      quantitativeParametersMeasured ≡ false

    wetLabValidationAccepted : Bool
    wetLabValidationAcceptedIsFalse :
      wetLabValidationAccepted ≡ false

    molecularIdentityAuthority : Bool
    molecularIdentityAuthorityIsFalse :
      molecularIdentityAuthority ≡ false

    kernelReading : String

open ChemistryTransitionKernel public

------------------------------------------------------------------------
-- Small reusable utilities.

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

emptyEnvironment : Environment
emptyEnvironment = record
  { temperatureCarrier = "unresolved temperature carrier"
  ; pHCarrier = "unresolved pH carrier"
  ; pressureCarrier = "unresolved pressure carrier"
  ; humidityCarrier = "unresolved humidity carrier"
  ; illuminationCarrier = "unresolved illumination carrier"
  ; ionicStrengthCarrier = "unresolved ionic-strength carrier"
  }

unknownRate : RateLaw
unknownRate = record
  { rateLawKind = unknownRateLaw
  ; symbolicForm = "unknown rate law"
  ; parameters = []
  ; validityRegime = "unresolved"
  ; evidence = unresolved
  }

canonicalKernelBoundary :
  (system : HybridTransitionSystem) →
  (conservation : ConservationCertificate) →
  (processWindows : List ProcessWindow) →
  (reachabilityProblems : List ReachabilityProblem) →
  (stabilitySurfaces : List StabilitySurface) →
  (observables : List ObservableMap) →
  (reductions : List ModelReduction) →
  (experimentSelection : ExperimentSelection) →
  ChemistryTransitionKernel
canonicalKernelBoundary system conservation processWindows reachabilityProblems
  stabilitySurfaces observables reductions experimentSelection = record
  { system = system
  ; conservation = conservation
  ; processWindows = processWindows
  ; reachabilityProblems = reachabilityProblems
  ; stabilitySurfaces = stabilitySurfaces
  ; observables = observables
  ; reductions = reductions
  ; experimentSelection = experimentSelection
  ; quantitativeParametersMeasured = false
  ; quantitativeParametersMeasuredIsFalse = refl
  ; wetLabValidationAccepted = false
  ; wetLabValidationAcceptedIsFalse = refl
  ; molecularIdentityAuthority = false
  ; molecularIdentityAuthorityIsFalse = refl
  ; kernelReading =
      "solver-neutral chemistry transition kernel; quantitative and wet-lab promotion remains fail-closed"
  }

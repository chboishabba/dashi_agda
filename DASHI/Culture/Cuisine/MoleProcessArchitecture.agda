module DASHI.Culture.Cuisine.MoleProcessArchitecture where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Culture.Cuisine.QualitativeSensoryCore as Sensory
import DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas as Sources

------------------------------------------------------------------------
-- Mole as an order-sensitive material process.
--
-- Ingredients do not disappear into an unordered inventory.  Each component
-- carries a thermal, hydration, particle, lipid, sensory, labour and source
-- history.  The finite routes below witness shape and order only; their
-- numerical coordinates are candidate descriptors, not measured rheology.
------------------------------------------------------------------------

data MoleOperation : Set where
  dehydrateOperation : MoleOperation
  toastOperation : MoleOperation
  fryOperation : MoleOperation
  charOperation : MoleOperation
  carboniseOperation : MoleOperation
  washOperation : MoleOperation
  rehydrateOperation : MoleOperation
  grindOperation : MoleOperation
  shearOperation : MoleOperation
  disperseOperation : MoleOperation
  reduceOperation : MoleOperation
  simmerOperation : MoleOperation
  restOperation : MoleOperation

data ThermalState : Set where
  rawThermalState : ThermalState
  driedThermalState : ThermalState
  toastedThermalState : ThermalState
  friedThermalState : ThermalState
  charredThermalState : ThermalState
  controlledCarbonisedState : ThermalState
  washedCarbonisedState : ThermalState
  acridlyBurntState : ThermalState

data CandidateMoleState : Set where
  rawChileState : CandidateMoleState
  friedChileState : CandidateMoleState
  rehydratedChileState : CandidateMoleState
  friedThenRehydratedChileState : CandidateMoleState
  rehydratedThenFriedChileState : CandidateMoleState
  rawSeedState : CandidateMoleState
  carbonisedSeedState : CandidateMoleState
  washedAshState : CandidateMoleState
  rawComponentAssemblyState : CandidateMoleState
  differentiallyPreparedAssemblyState : CandidateMoleState
  groundPasteState : CandidateMoleState
  hotFatDispersedPasteState : CandidateMoleState
  serviceStableMoleState : CandidateMoleState

record ProcessControl : Set where
  constructor processControl
  field
    timeCoordinate : Nat
    temperatureCoordinate : Nat
    medium : String
    observableTarget : String

open ProcessControl public

record ProcessEvent
    (before after : CandidateMoleState) : Set where
  constructor processEvent
  field
    operation : MoleOperation
    thermalStateAfter : ThermalState
    control : ProcessControl
    eventReading : String

open ProcessEvent public

data ProcessRoute : CandidateMoleState → CandidateMoleState → Set where
  routeStop :
    {state : CandidateMoleState} →
    ProcessRoute state state

  routeStep :
    {before middle after : CandidateMoleState} →
    ProcessEvent before middle →
    ProcessRoute middle after →
    ProcessRoute before after

fryRawChile : ProcessEvent rawChileState friedChileState
fryRawChile =
  processEvent
    fryOperation
    friedThermalState
    (processControl 1 1 "fat" "puff and colour shift without acrid scorching")
    "candidate flash-fry event"

rehydrateFriedChile :
  ProcessEvent friedChileState friedThenRehydratedChileState
rehydrateFriedChile =
  processEvent
    rehydrateOperation
    friedThermalState
    (processControl 20 1 "hot water" "softened fried chile matrix")
    "candidate rehydration after frying"

rehydrateRawChile : ProcessEvent rawChileState rehydratedChileState
rehydrateRawChile =
  processEvent
    rehydrateOperation
    rawThermalState
    (processControl 20 1 "hot water" "softened raw dried-chile matrix")
    "candidate rehydration before frying"

fryRehydratedChile :
  ProcessEvent rehydratedChileState rehydratedThenFriedChileState
fryRehydratedChile =
  processEvent
    fryOperation
    friedThermalState
    (processControl 1 1 "fat" "surface frying of hydrated material")
    "candidate frying after rehydration"

fryThenRehydrateRoute :
  ProcessRoute rawChileState friedThenRehydratedChileState
fryThenRehydrateRoute =
  routeStep fryRawChile
    (routeStep rehydrateFriedChile routeStop)

rehydrateThenFryRoute :
  ProcessRoute rawChileState rehydratedThenFriedChileState
rehydrateThenFryRoute =
  routeStep rehydrateRawChile
    (routeStep fryRehydratedChile routeStop)

record OrderSensitiveRouteWitness : Set where
  constructor orderSensitiveRouteWitness
  field
    fryThenRehydrate :
      ProcessRoute rawChileState friedThenRehydratedChileState
    rehydrateThenFry :
      ProcessRoute rawChileState rehydratedThenFriedChileState
    endpointDistinctionReading : String

open OrderSensitiveRouteWitness public

canonicalOrderSensitiveRouteWitness : OrderSensitiveRouteWitness
canonicalOrderSensitiveRouteWitness =
  orderSensitiveRouteWitness
    fryThenRehydrateRoute
    rehydrateThenFryRoute
    "The two orderings inhabit different indexed endpoints; no context-free commutation theorem is asserted."

carboniseSeeds : ProcessEvent rawSeedState carbonisedSeedState
carboniseSeeds =
  processEvent
    carboniseOperation
    controlledCarbonisedState
    (processControl 1 2 "dry comal or fire" "candidate carbonised seed state")
    "practitioner-described candidate carbonisation event"

washCarbonisedSeeds :
  ProcessEvent carbonisedSeedState washedAshState
washCarbonisedSeeds =
  processEvent
    washOperation
    washedCarbonisedState
    (processControl 1 0 "water" "candidate reduction of acrid residual")
    "candidate washing event; selective chemical effect remains empirical"

canonicalAshRoute : ProcessRoute rawSeedState washedAshState
canonicalAshRoute =
  routeStep carboniseSeeds
    (routeStep washCarbonisedSeeds routeStop)

record AshTransformationReceipt : Set where
  constructor ashTransformationReceipt
  field
    route : ProcessRoute rawSeedState washedAshState
    intendedSensoryRole : String
    processAssurance : Sensory.ProcessAssurance
    safetyEvidence : Sensory.SafetyEvidence
    selectiveAcridityRemovalClaim : Bool
    selectiveAcridityRemovalClaimIsFalse :
      selectiveAcridityRemovalClaim ≡ false
    permanentSafetyClaim : Bool
    permanentSafetyClaimIsFalse : permanentSafetyClaim ≡ false
    receiptReading : String

open AshTransformationReceipt public

canonicalAshTransformationReceipt : AshTransformationReceipt
canonicalAshTransformationReceipt =
  ashTransformationReceipt
    canonicalAshRoute
    "dark colour, smoke, bitterness, and mineral character are candidate practitioner readings"
    Sensory.unknownProcess
    Sensory.safetyUnknown
    false
    refl
    false
    refl
    "The process route is retained while selective washing and safety remain external evidence obligations."

prepareAssembly :
  ProcessEvent rawComponentAssemblyState differentiallyPreparedAssemblyState
prepareAssembly =
  processEvent
    toastOperation
    toastedThermalState
    (processControl 30 1 "multiple pans and media" "components reach their distinct target states")
    "compressed event standing for separately controlled chile, seed, nut, fruit, bread, allium, and spice histories"

grindAssembly :
  ProcessEvent differentiallyPreparedAssemblyState groundPasteState
grindAssembly =
  processEvent
    grindOperation
    toastedThermalState
    (processControl 4 1 "metate, molino, or blender" "target particle distribution and paste continuity")
    "mechanical outcome does not imply cultural equivalence among tools"

dispersePaste :
  ProcessEvent groundPasteState hotFatDispersedPasteState
dispersePaste =
  processEvent
    disperseOperation
    friedThermalState
    (processControl 1 2 "hot fat and aqueous paste" "continuous dispersion without uncontrolled splashing")
    "candidate multiphase assembly event"

simmerMole :
  ProcessEvent hotFatDispersedPasteState serviceStableMoleState
simmerMole =
  processEvent
    simmerOperation
    friedThermalState
    (processControl 45 1 "cazuela or heavy vessel" "target gloss, coating continuity, aroma, and service stability")
    "service stability is operational and time-bounded, not permanent"

canonicalCandidateMoleRoute :
  ProcessRoute rawComponentAssemblyState serviceStableMoleState
canonicalCandidateMoleRoute =
  routeStep prepareAssembly
    (routeStep grindAssembly
      (routeStep dispersePaste
        (routeStep simmerMole routeStop)))

data IngredientTraceStatus : Set where
  materiallyTransformedTrace : IngredientTraceStatus
  sensoriallyDetectableTrace : IngredientTraceStatus
  historicallyTraceableTrace : IngredientTraceStatus
  sociallyAttributedTrace : IngredientTraceStatus
  unresolvedTrace : IngredientTraceStatus

record IngredientPersistence : Set where
  constructor ingredientPersistence
  field
    ingredientLabel : String
    transformedState : CandidateMoleState
    retainedTraces : List IngredientTraceStatus
    persistenceReading : String

open IngredientPersistence public

canonicalChilePersistence : IngredientPersistence
canonicalChilePersistence =
  ingredientPersistence
    "dried chile family"
    serviceStableMoleState
    ( materiallyTransformedTrace
    ∷ sensoriallyDetectableTrace
    ∷ historicallyTraceableTrace
    ∷ sociallyAttributedTrace
    ∷ [] )
    "Integration into mole is not ingredient erasure; material, sensory, historical, and social traces may remain distinct."

record MultiphaseMoleState : Set where
  constructor multiphaseMoleState
  field
    aqueousPhaseIndex : Nat
    lipidPhaseIndex : Nat
    suspendedSolidIndex : Nat
    particleScaleIndex : Nat
    viscosityIndex : Nat
    yieldBehaviourIndex : Nat
    shearHistory : String
    serviceStable : Bool
    permanentSuspensionClaim : Bool
    permanentSuspensionClaimIsFalse :
      permanentSuspensionClaim ≡ false

open MultiphaseMoleState public

canonicalCandidateMultiphaseMole : MultiphaseMoleState
canonicalCandidateMultiphaseMole =
  multiphaseMoleState
    3
    2
    5
    2
    6
    4
    "candidate grinding, shearing, dispersion, and low-heat development history"
    true
    false
    refl

data ControlObservation : Set where
  colourObservation : ControlObservation
  aromaObservation : ControlObservation
  soundObservation : ControlObservation
  viscosityObservation : ControlObservation
  surfaceOilObservation : ControlObservation
  particleTextureObservation : ControlObservation

data ControlAction : Set where
  increaseHeatAction : ControlAction
  decreaseHeatAction : ControlAction
  removeFromHeatAction : ControlAction
  stirAction : ControlAction
  grindFurtherAction : ControlAction
  addLiquidAction : ControlAction
  continueAction : ControlAction
  stopAction : ControlAction

record EmbodiedControlDecision : Set where
  constructor embodiedControlDecision
  field
    observations : List ControlObservation
    processHistory : String
    situatedKnowledge : String
    selectedAction : ControlAction
    decisionReading : String

open EmbodiedControlDecision public

canonicalMoleCompletionDecision : EmbodiedControlDecision
canonicalMoleCompletionDecision =
  embodiedControlDecision
    ( colourObservation
    ∷ aromaObservation
    ∷ viscosityObservation
    ∷ surfaceOilObservation
    ∷ particleTextureObservation
    ∷ [] )
    "differential preparation, grinding, hot-fat dispersion, and extended stirring"
    "practitioner-calibrated distinction between developed paste, scorching, and structural separation"
    stopAction
    "Embodied completion criteria are feedback observations, not a fixed duration alone."

data MoleProcessNonCollapse : Set where
  sameIngredientsDoNotFixRoute : MoleProcessNonCollapse
  sameColourDoesNotFixThermalHistory : MoleProcessNonCollapse
  charredDoesNotImplyFailed : MoleProcessNonCollapse
  charredDoesNotImplySafe : MoleProcessNonCollapse
  serviceStableDoesNotImplyPermanent : MoleProcessNonCollapse
  mechanicallySimilarDoesNotImplyCulturallyEquivalent : MoleProcessNonCollapse
  integratedDoesNotImplyErased : MoleProcessNonCollapse

canonicalMoleProcessNonCollapses : List MoleProcessNonCollapse
canonicalMoleProcessNonCollapses =
  sameIngredientsDoNotFixRoute
  ∷ sameColourDoesNotFixThermalHistory
  ∷ charredDoesNotImplyFailed
  ∷ charredDoesNotImplySafe
  ∷ serviceStableDoesNotImplyPermanent
  ∷ mechanicallySimilarDoesNotImplyCulturallyEquivalent
  ∷ integratedDoesNotImplyErased
  ∷ []

record MoleProcessArchitectureBoundary : Set where
  constructor moleProcessArchitectureBoundary
  field
    candidateRoute :
      ProcessRoute rawComponentAssemblyState serviceStableMoleState
    orderWitness : OrderSensitiveRouteWitness
    ashReceipt : AshTransformationReceipt
    ingredientPersistenceWitness : IngredientPersistence
    multiphaseState : MultiphaseMoleState
    embodiedDecision : EmbodiedControlDecision
    nonCollapses : List MoleProcessNonCollapse
    sources : Sources.canonicalCuisineKnowledgeSourceCount ≡ 22
    measuredConstitutiveLawClaim : Bool
    measuredConstitutiveLawClaimIsFalse :
      measuredConstitutiveLawClaim ≡ false
    regionalAuthenticityClaim : Bool
    regionalAuthenticityClaimIsFalse : regionalAuthenticityClaim ≡ false

open MoleProcessArchitectureBoundary public

canonicalMoleProcessArchitectureBoundary : MoleProcessArchitectureBoundary
canonicalMoleProcessArchitectureBoundary =
  moleProcessArchitectureBoundary
    canonicalCandidateMoleRoute
    canonicalOrderSensitiveRouteWitness
    canonicalAshTransformationReceipt
    canonicalChilePersistence
    canonicalCandidateMultiphaseMole
    canonicalMoleCompletionDecision
    canonicalMoleProcessNonCollapses
    Sources.canonicalCuisineKnowledgeSourceCountIsTwentyTwo
    false
    refl
    false
    refl

canonicalMoleProcessArchitectureReceipt : GenericReceipt.GenericReceipt
canonicalMoleProcessArchitectureReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "mole process architecture"
    "DASHI.Culture.Cuisine.MoleProcessArchitecture"
    "canonicalMoleProcessArchitectureBoundary"
    "formalises order-sensitive routes, ash as transformation receipt, ingredient persistence, candidate multiphase state, and embodied control"
    "the finite coordinates do not establish measured rheology, selective chemistry, food safety, regional authenticity, ritual meaning, or cultural authority"
    "agda -i . DASHI/Culture/Cuisine/MoleProcessArchitecture.agda"

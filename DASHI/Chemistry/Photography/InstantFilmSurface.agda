module DASHI.Chemistry.Photography.InstantFilmSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.ExistingContentBridge as Existing
import DASHI.Chemistry.TransitionKernel as K

------------------------------------------------------------------------
-- Instant film as a coupled optical/reaction/transport/timing system.
--
-- Roller and pod mechanics are retained as optional boundary carriers, not
-- treated as the central reconstruction problem.  No proprietary recipe,
-- measured coefficient, or wet-lab success is asserted here.

data FilmProcessFamily : Set where
  integralColour
  peelApartColour
  peelApartBlackAndWhite
  singleColourSurrogate : FilmProcessFamily

data FilmLayerRole : Set where
  clearSupport
  acidNeutralisationLayer
  timingLayer
  imageReceiver
  reflectingLayer
  opacificationLayer
  blueSensitiveRecord
  yellowImageLayer
  greenSensitiveRecord
  magentaImageLayer
  redSensitiveRecord
  cyanImageLayer
  interlayer
  opaqueSupport
  reagentSpreadLayer : FilmLayerRole

record FilmLayer : Set where
  field
    layerId : String
    role : FilmLayerRole
    orderIndexCarrier : String
    thicknessParameter : K.Parameter
    porosityParameter : K.Parameter
    diffusivityCarrier : String
    spectralResponseCarrier : String
    containedSpecies : List K.Species
    interfaceBoundaryCarrier : String
    evidence : K.EvidenceStatus

open FilmLayer public

record SpectralRecord : Set where
  field
    recordId : String
    sensitivityCarrier : String
    stackTransmissionCarrier : String
    exposureIntegral : String
    latentImageResponse : String
    complementaryImageCarrier : String
    crossoverBudgetCarrier : String
    evidence : K.EvidenceStatus

open SpectralRecord public

record ReactionDiffusionLaw : Set where
  field
    speciesFieldCarrier : String
    spatialCoordinateCarrier : String
    timeCarrier : String
    diffusionCarrier : String
    reactionCarrier : String
    equationCarrier : String
    activityDependenceCarrier : String
    evidence : K.EvidenceStatus

open ReactionDiffusionLaw public

record AlkaliTimingSurface : Set where
  field
    activeAlkalinityCarrier : String
    neutralisationFrontCarrier : String
    spreadTimeCarrier : String
    imageFormationTimeCarrier : String
    shutdownTimeCarrier : String
    damageTimeCarrier : String
    requiredOrdering : String
    processMarginCarrier : String
    processWindowNonempty : Bool

open AlkaliTimingSurface public

record OptionalSpreadMechanics : Set where
  field
    enabled : Bool
    reagentVolumeCarrier : String
    imageAreaCarrier : String
    retainedFractionCarrier : String
    meanThicknessCarrier : String
    spatialVariationCarrier : String
    visibleDensityErrorBudgetCarrier : String
    mechanicsValidated : Bool

open OptionalSpreadMechanics public

record FilmObservable : Set where
  field
    observableId : String
    exposureCarrier : String
    outputImageCarrier : String
    temperatureCarrier : String
    humidityCarrier : String
    elapsedTimeCarrier : String
    observableExpression : String
    instrumentResponseCarrier : String

open FilmObservable public

record GapLedgerRow : Set where
  field
    component : String
    functionalRoleKnown : Bool
    molecularFamilyKnown : Bool
    exactMaterialKnown : Bool
    parametersMeasured : Bool
    substituteValidated : Bool
    evidence : K.EvidenceStatus
    nextDiscriminatingMeasurement : String

open GapLedgerRow public

record ReconstructionStage : Set where
  field
    stageId : String
    processFamily : FilmProcessFamily
    target : String
    requiredObservables : List String
    successCriterion : String
    completed : Bool

open ReconstructionStage public

------------------------------------------------------------------------
-- Canonical species roles.  These are functional classes, not recipes.

functionalSpecies : List K.Species
functionalSpecies =
  record
    { speciesId = "developer functional class"
    ; phase = K.dissolved
    ; chargeLabel = "candidate/context dependent"
    ; compositionLabel = "unresolved molecular identity"
    ; mobilityClass = K.mobile
    ; activityModelLabel = "activity or concentration carrier"
    ; opticalRoleLabel = "none directly"
    ; evidence = K.literatureEstablished
    }
  ∷ record
    { speciesId = "silver-halide photosensitive population"
    ; phase = K.emulsion
    ; chargeLabel = "crystal/defect-state carrier"
    ; compositionLabel = "AgX family; exact emulsion unresolved"
    ; mobilityClass = K.immobile
    ; activityModelLabel = "grain population carrier"
    ; opticalRoleLabel = "latent image formation"
    ; evidence = K.literatureEstablished
    }
  ∷ record
    { speciesId = "oxidised developer functional class"
    ; phase = K.dissolved
    ; chargeLabel = "candidate/context dependent"
    ; compositionLabel = "unresolved molecular identity"
    ; mobilityClass = K.restricted
    ; activityModelLabel = "local redox-state carrier"
    ; opticalRoleLabel = "imagewise mobility control"
    ; evidence = K.literatureEstablished
    }
  ∷ record
    { speciesId = "mobile complementary image species"
    ; phase = K.dissolved
    ; chargeLabel = "candidate/context dependent"
    ; compositionLabel = "dye or dye-precursor family"
    ; mobilityClass = K.mobile
    ; activityModelLabel = "diffusing image-species carrier"
    ; opticalRoleLabel = "cyan/magenta/yellow image density"
    ; evidence = K.literatureEstablished
    }
  ∷ record
    { speciesId = "receiver-bound image species"
    ; phase = K.adsorbed
    ; chargeLabel = "mordant-dependent"
    ; compositionLabel = "mobile image species bound to receiver"
    ; mobilityClass = K.immobile
    ; activityModelLabel = "binding-site occupancy"
    ; opticalRoleLabel = "final positive image"
    ; evidence = K.literatureEstablished
    }
  ∷ record
    { speciesId = "active alkali"
    ; phase = K.gel
    ; chargeLabel = "alkaline activity carrier"
    ; compositionLabel = "exact formulation unresolved"
    ; mobilityClass = K.mobile
    ; activityModelLabel = "pH/activity carrier"
    ; opticalRoleLabel = "processing activation/opacification context"
    ; evidence = K.literatureEstablished
    }
  ∷ record
    { speciesId = "acid neutralisation capacity"
    ; phase = K.solid
    ; chargeLabel = "acid-base capacity carrier"
    ; compositionLabel = "polymeric acid family"
    ; mobilityClass = K.immobile
    ; activityModelLabel = "neutralisation-front carrier"
    ; opticalRoleLabel = "post-process stability"
    ; evidence = K.patentDisclosed
    }
  ∷ []

filmEnvironment : K.Environment
filmEnvironment = record
  { temperatureCarrier = "film/process temperature T"
  ; pHCarrier = "layer-resolved pH(z,t)"
  ; pressureCarrier = "ambient and optional roller contact pressure"
  ; humidityCarrier = "relative humidity H"
  ; illuminationCarrier = "spectral exposure E(x,y,lambda)"
  ; ionicStrengthCarrier = "layer-resolved ionic strength I(z,t)"
  }

filmCondition : K.Condition
filmCondition = record
  { conditionLabel = "instant-film operating context"
  ; environment = filmEnvironment
  ; guardExpression = "declared process family, temperature, humidity, exposure, layer order, and elapsed time"
  }

filmRate : K.RateLaw
filmRate = record
  { rateLawKind = K.intervalBounded
  ; symbolicForm = "k_min(T,pH,I) <= k <= k_max(T,pH,I)"
  ; parameters = []
  ; validityRegime = "specified layer, phase, temperature, pH, and ionic-strength range"
  ; evidence = K.unresolved
  }

------------------------------------------------------------------------
-- Minimal causal transition graph.

filmTransitions : List K.Transition
filmTransitions =
  record
    { transitionId = "latent-image development"
    ; transitionKind = K.chemicalReaction
    ; reactants = []
    ; products = []
    ; catalysts = []
    ; rateLaw = filmRate
    ; condition = filmCondition
    ; reversibility = K.irreversible
    ; evidence = K.literatureEstablished
    }
  ∷ record
    { transitionId = "imagewise dye mobility or release control"
    ; transitionKind = K.chemicalReaction
    ; reactants = []
    ; products = []
    ; catalysts = []
    ; rateLaw = filmRate
    ; condition = filmCondition
    ; reversibility = K.conditionallyReversible
    ; evidence = K.patentDisclosed
    }
  ∷ record
    { transitionId = "mobile image species crosses interlayer"
    ; transitionKind = K.transportTransition
    ; reactants = []
    ; products = []
    ; catalysts = []
    ; rateLaw = filmRate
    ; condition = filmCondition
    ; reversibility = K.conditionallyReversible
    ; evidence = K.literatureEstablished
    }
  ∷ record
    { transitionId = "receiver immobilises image species"
    ; transitionKind = K.bindingTransition
    ; reactants = []
    ; products = []
    ; catalysts = []
    ; rateLaw = filmRate
    ; condition = filmCondition
    ; reversibility = K.conditionallyReversible
    ; evidence = K.literatureEstablished
    }
  ∷ record
    { transitionId = "timing layer changes permeability"
    ; transitionKind = K.phaseTransition
    ; reactants = []
    ; products = []
    ; catalysts = []
    ; rateLaw = filmRate
    ; condition = filmCondition
    ; reversibility = K.irreversible
    ; evidence = K.patentDisclosed
    }
  ∷ record
    { transitionId = "acid layer neutralises active alkali"
    ; transitionKind = K.chemicalReaction
    ; reactants = []
    ; products = []
    ; catalysts = []
    ; rateLaw = filmRate
    ; condition = filmCondition
    ; reversibility = K.irreversible
    ; evidence = K.literatureEstablished
    }
  ∷ []

filmNetwork : K.ReactionNetwork
filmNetwork = record
  { networkId = "instant-film qualitative reaction/transport network"
  ; species = functionalSpecies
  ; transitions = filmTransitions
  ; compartments = []
  ; interfaces = []
  ; environment = filmEnvironment
  }

filmEvents : List K.ChemicalEvent
filmEvents =
  record
    { eventId = "reagent contacts photosensitive stack"
    ; guardCarrier = "process initiated"
    ; stateUpdateCarrier = "transport and development enabled"
    ; eventKind = K.mechanicalEvent
    ; evidence = K.literatureEstablished
    }
  ∷ record
    { eventId = "neutralisation front reaches active stack"
    ; guardCarrier = "timing-layer delay discharged"
    ; stateUpdateCarrier = "active alkalinity decreases"
    ; eventKind = K.chemicalReaction
    ; evidence = K.patentDisclosed
    }
  ∷ []

filmObligations : List K.TransitionObligation
filmObligations =
  record
    { obligationId = "mobile image must be immobilised"
    ; obligationKind = K.mustImmobilise
    ; pushedBy = "imagewise dye mobility or release control"
    ; dischargedBy = "receiver immobilises image species"
    ; dischargeCondition = "receiver density reaches target before shutdown"
    }
  ∷ record
    { obligationId = "active alkali must be neutralised"
    ; obligationKind = K.mustNeutralise
    ; pushedBy = "reagent contacts photosensitive stack"
    ; dischargedBy = "acid layer neutralises active alkali"
    ; dischargeCondition = "neutralisation occurs after image formation and before damage"
    }
  ∷ []

filmOrder : List K.OrderingConstraint
filmOrder =
  record
    { predecessor = "reagent contacts photosensitive stack"
    ; successor = "latent-image development"
    ; orderingMeaning = "processing must begin before image development"
    }
  ∷ record
    { predecessor = "latent-image development"
    ; successor = "receiver immobilises image species"
    ; orderingMeaning = "imagewise chemistry must precede final receiver capture"
    }
  ∷ record
    { predecessor = "receiver immobilises image species"
    ; successor = "acid layer neutralises active alkali"
    ; orderingMeaning = "useful image formation must precede shutdown"
    }
  ∷ []

filmHybridSystem : K.HybridTransitionSystem
filmHybridSystem = record
  { reactionNetwork = filmNetwork
  ; events = filmEvents
  ; obligations = filmObligations
  ; orderingConstraints = filmOrder
  ; continuousEvolutionCarrier =
      "partial_t c_k = div(D_k grad c_k) + sum_r N_kr v_r"
  ; discreteEventCarrier =
      "guarded contact, permeability, peel, gelation, precipitation, or shutdown events"
  }

canonicalTimingSurface : AlkaliTimingSurface
canonicalTimingSurface = record
  { activeAlkalinityCarrier = "a(z,t)"
  ; neutralisationFrontCarrier = "q(z,t)"
  ; spreadTimeCarrier = "t_spread"
  ; imageFormationTimeCarrier = "t_image"
  ; shutdownTimeCarrier = "t_shutdown"
  ; damageTimeCarrier = "t_damage"
  ; requiredOrdering = "t_spread < t_image < t_shutdown < t_damage"
  ; processMarginCarrier =
      "min(t_shutdown-t_image, t_damage-t_shutdown, t_image-t_spread)"
  ; processWindowNonempty = false
  }

canonicalOptionalSpreadMechanics : OptionalSpreadMechanics
canonicalOptionalSpreadMechanics = record
  { enabled = false
  ; reagentVolumeCarrier = "V"
  ; imageAreaCarrier = "w*l"
  ; retainedFractionCarrier = "eta"
  ; meanThicknessCarrier = "h_bar approximately eta*V/(w*l)"
  ; spatialVariationCarrier = "delta_h = rms(h-h_bar)/h_bar"
  ; visibleDensityErrorBudgetCarrier = "delta_D < epsilon_visible"
  ; mechanicsValidated = false
  }

canonicalGapLedger : List GapLedgerRow
canonicalGapLedger =
  record
    { component = "silver-halide emulsion"
    ; functionalRoleKnown = true
    ; molecularFamilyKnown = true
    ; exactMaterialKnown = false
    ; parametersMeasured = false
    ; substituteValidated = false
    ; evidence = K.literatureEstablished
    ; nextDiscriminatingMeasurement = "spectral response, characteristic curve, grain/layer microscopy"
    }
  ∷ record
    { component = "spectral sensitisers"
    ; functionalRoleKnown = true
    ; molecularFamilyKnown = true
    ; exactMaterialKnown = false
    ; parametersMeasured = false
    ; substituteValidated = false
    ; evidence = K.inferredFromOutput
    ; nextDiscriminatingMeasurement = "layer-resolved excitation/absorption response"
    }
  ∷ record
    { component = "colour image chemistry"
    ; functionalRoleKnown = true
    ; molecularFamilyKnown = true
    ; exactMaterialKnown = false
    ; parametersMeasured = false
    ; substituteValidated = false
    ; evidence = K.patentDisclosed
    ; nextDiscriminatingMeasurement = "single-channel transfer monotonicity and crossover assay"
    }
  ∷ record
    { component = "interlayers and scavengers"
    ; functionalRoleKnown = true
    ; molecularFamilyKnown = true
    ; exactMaterialKnown = false
    ; parametersMeasured = false
    ; substituteValidated = false
    ; evidence = K.patentDisclosed
    ; nextDiscriminatingMeasurement = "cross-diffusion and off-diagonal colour response"
    }
  ∷ record
    { component = "receiver and mordant"
    ; functionalRoleKnown = true
    ; molecularFamilyKnown = true
    ; exactMaterialKnown = false
    ; parametersMeasured = false
    ; substituteValidated = false
    ; evidence = K.literatureEstablished
    ; nextDiscriminatingMeasurement = "binding isotherm, mobility arrest, density and fade tests"
    }
  ∷ record
    { component = "timing and acid layers"
    ; functionalRoleKnown = true
    ; molecularFamilyKnown = true
    ; exactMaterialKnown = false
    ; parametersMeasured = false
    ; substituteValidated = false
    ; evidence = K.patentDisclosed
    ; nextDiscriminatingMeasurement = "temperature-dependent pH-front timing"
    }
  ∷ record
    { component = "complete coating process"
    ; functionalRoleKnown = true
    ; molecularFamilyKnown = false
    ; exactMaterialKnown = false
    ; parametersMeasured = false
    ; substituteValidated = false
    ; evidence = K.unresolved
    ; nextDiscriminatingMeasurement = "layer thickness/uniformity and reproducible coating protocol"
    }
  ∷ []

canonicalReconstructionStages : List ReconstructionStage
canonicalReconstructionStages =
  record
    { stageId = "A-characterise-surviving-systems"
    ; processFamily = integralColour
    ; target = "constraint atlas from surviving and current film"
    ; requiredObservables =
        "layer thickness" ∷ "spectral response" ∷ "pH-front timing"
        ∷ "temperature response" ∷ "time-resolved image formation" ∷ []
    ; successCriterion = "reproducible measurement set with provenance and uncertainty"
    ; completed = false
    }
  ∷ record
    { stageId = "B-black-and-white-diffusion-transfer"
    ; processFamily = peelApartBlackAndWhite
    ; target = "minimal silver transfer kernel"
    ; requiredObservables =
        "positive density" ∷ "resolution" ∷ "peel/process timing" ∷ []
    ; successCriterion = "repeatable positive image with conservation and process-window receipts"
    ; completed = false
    }
  ∷ record
    { stageId = "C-single-colour-surrogate"
    ; processFamily = singleColourSurrogate
    ; target = "one photosensitive record to one mobile image channel"
    ; requiredObservables =
        "exposure monotonicity" ∷ "receiver sharpness" ∷ "shutdown timing" ∷ []
    ; successCriterion = "H(x,y) maps monotonically to receiver image density"
    ; completed = false
    }
  ∷ record
    { stageId = "D-two-channel-interference"
    ; processFamily = peelApartColour
    ; target = "measure and bound off-diagonal channel crossover"
    ; requiredObservables =
        "X_12" ∷ "X_21" ∷ "interlayer transport" ∷ []
    ; successCriterion = "cross-channel derivatives below declared colour-error budget"
    ; completed = false
    }
  ∷ record
    { stageId = "E-full-RGB-stability"
    ; processFamily = integralColour
    ; target = "multi-objective colour, fog, timing, ageing, and manufacturability surface"
    ; requiredObservables =
        "DeltaE" ∷ "fog density" ∷ "development time"
        ∷ "ageing drift" ∷ "coating reproducibility" ∷ []
    ; successCriterion = "nonempty robust operating region; not merely a single successful shot"
    ; completed = false
    }
  ∷ []

------------------------------------------------------------------------
-- Whole application surface.

record InstantFilmFormalisation : Set₁ where
  field
    existingChemistry : Existing.ExistingChemistryBridge
    transitionSystem : K.HybridTransitionSystem
    layers : List FilmLayer
    spectralRecords : List SpectralRecord
    reactionDiffusionLaws : List ReactionDiffusionLaw
    timing : AlkaliTimingSurface
    optionalSpreadMechanics : OptionalSpreadMechanics
    observables : List FilmObservable
    gapLedger : List GapLedgerRow
    reconstructionStages : List ReconstructionStage

    spectralSeparationSufficient : Bool
    layerOrderOpticallyCompatible : Bool
    imageSpeciesReachesReceiver : Bool
    crossLayerContaminationBounded : Bool
    imageFormsBeforeNeutralisation : Bool
    neutralisationPrecedesDamage : Bool
    ambientOperatingWindowNonempty : Bool
    shelfLifeLowerBoundEstablished : Bool
    candidateStackManufacturable : Bool

    proprietaryRecipeRecovered : Bool
    proprietaryRecipeRecoveredIsFalse : proprietaryRecipeRecovered ≡ false
    wetLabValidationAccepted : Bool
    wetLabValidationAcceptedIsFalse : wetLabValidationAccepted ≡ false

    formalisationReading : String

open InstantFilmFormalisation public

canonicalInstantFilmFormalisation : InstantFilmFormalisation
canonicalInstantFilmFormalisation = record
  { existingChemistry = Existing.canonicalExistingChemistryBridge
  ; transitionSystem = filmHybridSystem
  ; layers = []
  ; spectralRecords = []
  ; reactionDiffusionLaws =
      record
        { speciesFieldCarrier = "c_k(z,t)"
        ; spatialCoordinateCarrier = "layer depth z"
        ; timeCarrier = "elapsed process time t"
        ; diffusionCarrier = "D_k(c,T,pH)"
        ; reactionCarrier = "R_k(c,T,pH)"
        ; equationCarrier =
            "partial_t c_k = partial_z(D_k partial_z c_k) + R_k"
        ; activityDependenceCarrier = "temperature, pH, phase, ionic strength, viscosity"
        ; evidence = K.literatureEstablished
        }
      ∷ []
  ; timing = canonicalTimingSurface
  ; optionalSpreadMechanics = canonicalOptionalSpreadMechanics
  ; observables = []
  ; gapLedger = canonicalGapLedger
  ; reconstructionStages = canonicalReconstructionStages
  ; spectralSeparationSufficient = false
  ; layerOrderOpticallyCompatible = false
  ; imageSpeciesReachesReceiver = false
  ; crossLayerContaminationBounded = false
  ; imageFormsBeforeNeutralisation = false
  ; neutralisationPrecedesDamage = false
  ; ambientOperatingWindowNonempty = false
  ; shelfLifeLowerBoundEstablished = false
  ; candidateStackManufacturable = false
  ; proprietaryRecipeRecovered = false
  ; proprietaryRecipeRecoveredIsFalse = refl
  ; wetLabValidationAccepted = false
  ; wetLabValidationAcceptedIsFalse = refl
  ; formalisationReading =
      "instant film is modelled as a coupled spectral exposure, reaction-diffusion, interface binding, timed shutdown, observable, and uncertainty-reduction problem; mechanics remain optional"
  }

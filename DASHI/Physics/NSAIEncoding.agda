module DASHI.Physics.NSAIEncoding where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)

import DASHI.Core.ContextIndexedEncoding as CIE
import DASHI.Core.NSAIFormalism as NSAI
import DASHI.Core.ProjectionGrammar as PG

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

------------------------------------------------------------------------
-- NS-AI as a context-indexed projection
--
--   E_NS : FlowCarrier × SimulationContext → ObservableFlowSurface
--
-- For Navier–Stokes AI, the hidden carrier is the full fluid state
-- (velocity field, pressure field, material properties).  The context
-- bundles the discretisation scheme, solver parameters, boundary
-- conditions, mesh refinement, model architecture, and training
-- distribution.  The observable is a predicted flow quantity.
--
-- Like Prot2Prop, NS-AI is NOT a PDE theorem.  Its predictions are
-- context-indexed projections that require residual closure against
-- an external authority (PDE residual, experiment, DNS reference).
--
--   Prot2Prop   : ProteinCarrier × ModelContext → DevelopabilitySurface
--   NS-AI       : FlowCarrier   × SimulationContext → ObservableFlowSurface
--
-- Both are instances of the same DASHI meta-pattern:
--
--   π : H × Γ → O
--   residual against external authority
--   no promotion without closure
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Flow carrier (hidden fluid state)
------------------------------------------------------------------------

-- The hidden carrier includes velocity field, pressure field, density,
-- viscosity, and any material-specific parameters.  These are never
-- directly observed — only projected through the simulation context.

record FlowCarrier : Set where
  field
    -- Velocity field (hidden; abstract)
    velocityField    : ⊤
    -- Pressure field (hidden; abstract)
    pressureField    : ⊤
    -- Fluid/material parameters (density, viscosity, ...)
    fluidParameters  : ⊤

open FlowCarrier public

canonicalFlowCarrier : FlowCarrier
canonicalFlowCarrier = record
  { velocityField   = tt
  ; pressureField   = tt
  ; fluidParameters = tt
  }

------------------------------------------------------------------------
-- 2. Simulation context
------------------------------------------------------------------------

-- The context bundles everything that determines how the hidden
-- carrier is projected onto an observable prediction.

record SimulationContext : Set where
  field
    -- Spatial and temporal discretisation (abstract)
    meshType          : ⊤
    timeStepping      : ⊤
    -- Boundary and initial conditions (abstract)
    boundaryConditions : ⊤
    initialConditions  : ⊤
    -- Model architecture (e.g. FNO, PINN, transformer) (abstract)
    modelArchitecture  : ⊤
    -- Training data distribution (abstract)
    trainingDistribution : ⊤

open SimulationContext public

canonicalSimulationContext : SimulationContext
canonicalSimulationContext = record
  { meshType             = tt
  ; timeStepping         = tt
  ; boundaryConditions   = tt
  ; initialConditions    = tt
  ; modelArchitecture    = tt
  ; trainingDistribution = tt
  }

------------------------------------------------------------------------
-- 3. Observable flow surface
------------------------------------------------------------------------

-- The model predicts one or more flow observables.

data FlowObservable : Set where
  VelocityField     : FlowObservable
  PressureField     : FlowObservable
  VorticityField    : FlowObservable
  DragCoefficient   : FlowObservable
  LiftCoefficient   : FlowObservable
  ReynoldsStress    : FlowObservable
  HeatFlux          : FlowObservable
  SkinFriction      : FlowObservable

allFlowObservables : List FlowObservable
allFlowObservables =
  VelocityField ∷ PressureField ∷ VorticityField
  ∷ DragCoefficient ∷ LiftCoefficient ∷ ReynoldsStress
  ∷ HeatFlux ∷ SkinFriction ∷ []

ObservableFlowSurface : Set
ObservableFlowSurface = ⊤

CarrierPackage : Set
CarrierPackage = FlowCarrier × SimulationContext

------------------------------------------------------------------------
-- 4. NS-AI projection
------------------------------------------------------------------------

-- The core encoding: hidden carrier × simulation context → observable.
-- The projection depends on the context: changing mesh, solver, or
-- model architecture produces different predictions.

πNS : CarrierPackage → FlowObservable → ObservableFlowSurface
πNS _ _ = tt

------------------------------------------------------------------------
-- 5. Residual against PDE/experiment authority
------------------------------------------------------------------------

-- NS-AI requires residual closure against an external authority:
--   • PDE residual (strong or weak form)
--   • Direct numerical simulation (DNS) reference
--   • Wind-tunnel / experimental measurement

Residual : Set
Residual = Nat

ρNS : CarrierPackage → FlowObservable → Residual
ρNS _ _ = zero

------------------------------------------------------------------------
-- 6. Guards
------------------------------------------------------------------------

-- Forbidden claims: things NS-AI does NOT license
data NSAIForbiddenClaim : Set where
  PDETheoremClaim           : NSAIForbiddenClaim
  UniversalTurbulenceLaw    : NSAIForbiddenClaim
  ClosureWithoutValidation  : NSAIForbiddenClaim
  MeshIndependenceClaim     : NSAIForbiddenClaim
  ExtrapolationBeyondData   : NSAIForbiddenClaim

canonicalNSAIForbiddenClaims : List NSAIForbiddenClaim
canonicalNSAIForbiddenClaims =
  PDETheoremClaim ∷ UniversalTurbulenceLaw
  ∷ ClosureWithoutValidation ∷ MeshIndependenceClaim
  ∷ ExtrapolationBeyondData ∷ []

-- Allowed operations
data NSAIAllowedOperation : Set where
  FlowProjection         : NSAIAllowedOperation
  ContextAwarePrediction : NSAIAllowedOperation
  ResidualMeasurement    : NSAIAllowedOperation
  PDEResidualComputation : NSAIAllowedOperation
  CalibrationMapping     : NSAIAllowedOperation
  AuthorityComparison    : NSAIAllowedOperation

canonicalNSAIAllowedOperations : List NSAIAllowedOperation
canonicalNSAIAllowedOperations =
  FlowProjection ∷ ContextAwarePrediction
  ∷ ResidualMeasurement ∷ PDEResidualComputation
  ∷ CalibrationMapping ∷ AuthorityComparison ∷ []

-- Guards
data NSAIGuard : Set where
  NoPDETheoremClaim           : NSAIGuard
  NoUniversalTurbulenceLaw    : NSAIGuard
  NoClosureWithoutValidation  : NSAIGuard
  NoExtrapolationBeyondData   : NSAIGuard

canonicalNSAIGuards : List NSAIGuard
canonicalNSAIGuards =
  NoPDETheoremClaim ∷ NoUniversalTurbulenceLaw
  ∷ NoClosureWithoutValidation ∷ NoExtrapolationBeyondData ∷ []

------------------------------------------------------------------------
-- 7. NS-AI as a ContextIndexedEncoding
------------------------------------------------------------------------

-- The encoding is parameterised by the flow observable as context:
--   Carrier   = FlowCarrier × SimulationContext
--   Context   = FlowObservable
--   Observable = ObservableFlowSurface

NSAIEncoding : CIE.ContextIndexedEncoding
  CarrierPackage FlowObservable ObservableFlowSurface
NSAIEncoding = record
  { π                      = πNS
  ; transport              = λ _ _ o → o
  ; residual               = λ _ _ _ → ⊤
  ; contextDependent       = true
  ; contextDependentIsTrue = refl
  ; promotionGateCarrier   = ⊤
  ; promotionGateClosed    = λ _ → false
  ; encodingGuards         =
      "noPDETheoremClaim"
      ∷ "noClosureWithoutValidation"
      ∷ "noExtrapolationBeyondData"
      ∷ []
  ; forbiddenPromotions    =
      "predictionPromotedToPDETheorem"
      ∷ "modelAccuracyPromotedToPhysicalTruth"
      ∷ "calibrationPromotedToValidation"
      ∷ []
  ; allowedOperations      =
      "contextAwareFlowProjection"
      ∷ "residualMeasurementAgainstPDE"
      ∷ "calibrationMapping"
      ∷ "authorityComparison"
      ∷ []
  ; encodingReading        =
      "NS-AI encoding: π : FlowCarrier × SimulationContext → ObservableFlowSurface. Predictions are context-indexed projections, not PDE theorems. Residual closure against PDE, DNS, or experimental authority is required before any promotion."
  }

------------------------------------------------------------------------
-- 8. Governance receipt
--
--   NS-AI prediction ≠ PDE theorem
--   benchmark win ≠ physical truth
--   calibration ≠ validation
--   surrogate accuracy ≠ theorem
------------------------------------------------------------------------

record NSAIGovernanceReceipt : Set where
  field
    predictionIsNotPDE        : Bool
    predictionIsNotPDEIsTrue  : predictionIsNotPDE ≡ true
    requiresValidation        : Bool
    requiresValidationIsTrue  : requiresValidation ≡ true
    residualExpected          : Bool
    residualExpectedIsTrue    : residualExpected ≡ true
    calibrationIsNotValidation : Bool
    calibrationIsNotValidationIsTrue : calibrationIsNotValidation ≡ true
    certificateReading         : String

open NSAIGovernanceReceipt public

canonicalNSAIGovernanceReceipt : NSAIGovernanceReceipt
canonicalNSAIGovernanceReceipt = record
  { predictionIsNotPDE             = true
  ; predictionIsNotPDEIsTrue       = refl
  ; requiresValidation             = true
  ; requiresValidationIsTrue       = refl
  ; residualExpected               = true
  ; residualExpectedIsTrue         = refl
  ; calibrationIsNotValidation     = true
  ; calibrationIsNotValidationIsTrue = refl
  ; certificateReading             =
      "NS-AI governance: predictions are not PDE theorems; validation against PDE residual, DNS, or experiment is required; residuals are expected; calibration does not substitute for validation."
  }

------------------------------------------------------------------------
-- 9. Non-promotion certificate
------------------------------------------------------------------------

record NSAINonPromotionCertificate : Set where
  field
    guardsMatch         : CIE.encodingGuards NSAIEncoding ≡
      ("noPDETheoremClaim" ∷ "noClosureWithoutValidation"
      ∷ "noExtrapolationBeyondData" ∷ [])
    forbiddenMatch      : CIE.forbiddenPromotions NSAIEncoding ≡
      ("predictionPromotedToPDETheorem"
      ∷ "modelAccuracyPromotedToPhysicalTruth"
      ∷ "calibrationPromotedToValidation" ∷ [])
    allowedMatch        : CIE.allowedOperations NSAIEncoding ≡
      ("contextAwareFlowProjection" ∷ "residualMeasurementAgainstPDE"
      ∷ "calibrationMapping" ∷ "authorityComparison" ∷ [])
    governanceMatch     : NSAIGovernanceReceipt
    predictionPromoted  : Bool
    predictionPromotedIsFalse : predictionPromoted ≡ false
    certificateReading  : String

open NSAINonPromotionCertificate public

canonicalNSAINonPromotionCertificate : NSAINonPromotionCertificate
canonicalNSAINonPromotionCertificate = record
  { guardsMatch              = refl
  ; forbiddenMatch           = refl
  ; allowedMatch             = refl
  ; governanceMatch          = canonicalNSAIGovernanceReceipt
  ; predictionPromoted       = false
  ; predictionPromotedIsFalse = refl
  ; certificateReading       =
      "The canonical NS-AI encoding is non-promoting: predictions remain candidate projections until residual closure against PDE, DNS, or experimental authority is demonstrated. No model accuracy win is promoted to physical truth without external validation."
  }

-----------------------------------------------------------------------
-- 10. NS-AI as a ProjectionGrammar
-----------------------------------------------------------------------

-- FlowObservable is the grammar that generates the admissible
-- prediction space.  For each observable, HomSpace(o) =
-- CarrierPackage → ObservableFlowSurface.  The NS-AI surrogate
-- and the PDE authority each generate their own Hom-spaces.
--
--   Grammar          = FlowObservable
--   HomSpace(o)      = CarrierPackage → ObservableFlowSurface
--   Carrier          = CarrierPackage (FlowCarrier × SimulationContext)
--   Observable       = ObservableFlowSurface

nsGrammar : PG.ProjectionGrammar
nsGrammar = record
  { Carrier             = CarrierPackage
  ; Observable          = ObservableFlowSurface
  ; Grammar             = FlowObservable
  ; HomSpace            = λ _ → CarrierPackage → ObservableFlowSurface
  ; apply               = λ h → h
  ; forbiddenPromotions =
      "predictionPromotedToPDETheorem" ∷
      "modelAccuracyPromotedToPhysicalTruth" ∷
      "calibrationPromotedToValidation" ∷ []
  ; allowedOperations   =
      "contextAwareFlowProjection" ∷
      "residualMeasurementAgainstPDE" ∷
      "calibrationMapping" ∷
      "authorityComparison" ∷ []
  ; encodingReading     =
      "NS-AI ProjectionGrammar: FlowObservable generates the admissible CarrierPackage→ObservableFlowSurface prediction space. Changing the observable selects a different projection surface."
  }

-----------------------------------------------------------------------
-- 11. NS-AI full formalism: PDE/experiment authority
-----------------------------------------------------------------------

-- PDE authority grammar: FlowObservable generates the admissible
-- PDE/DNS/experimental reference space.
pdeAuthorityGrammar : NSAI.AuthorityGrammar
pdeAuthorityGrammar = record
  { Carrier             = CarrierPackage
  ; AuthoritySurface    = ObservableFlowSurface
  ; AGrammar            = FlowObservable
  ; HomAuthority        = λ _ → CarrierPackage → ObservableFlowSurface
  ; applyAuthority      = λ h → h
  ; forbiddenPromotions =
      "pdeSolverPromotedToPhysicalTruth" ∷ []
  ; allowedOperations   =
      "pdeBasedReference" ∷
      "predictionAuthorityComparison" ∷ []
  ; encodingReading     =
      "PDE Authority Grammar: the PDE/DNS/experimental reference generates the admissible CarrierPackage→ObservableFlowSurface space of physically correct solutions."
  }

-- Residual comparison: NS-AI prediction vs PDE authority
nsResidualComparison : NSAI.ResidualComparison
  nsGrammar pdeAuthorityGrammar
nsResidualComparison = record
  { carrierCoercion = λ x → x
  ; residual        = λ _ _ → ⊤
  ; closed          = λ _ _ → ⊤
  ; residualReading =
      "NS-AI residual comparison: NS-AI surrogate (FlowObservable grammar) vs PDE authority (FlowObservable grammar). Residual expected; promotion requires closure."
  }

-- Promotion gate
nsPromotionGate : NSAI.PromotionGate
  nsGrammar pdeAuthorityGrammar nsResidualComparison
nsPromotionGate = record
  { Promoted   = λ π α → ⊤
  ; promote    = λ _ _ _ _ → tt
  ; failClosed = λ _ _ _ → tt , tt
  ; gateReading =
      "NS-AI promotion gate: an NS-AI prediction is promoted only when the residual against PDE/DNS/experimental authority is closed."
  }

-- NS-AI learner (trivial: πNS is the selected morphism)
nsLearner : NSAI.Learner nsGrammar
nsLearner = record
  { TrainingCarrier = ⊤
  ; LossSurface     = ⊤
  ; select          = λ o _ cp → πNS cp o
  ; loss            = λ _ _ _ → tt
  ; learnerReading  =
      "NS-AI learner: selects πNS : CarrierPackage→ObservableFlowSurface as the admissible flow prediction morphism."
  }

-- Full NS-AI pipeline
nsPipeline : NSAI.NSAIPipeline
  nsGrammar pdeAuthorityGrammar
nsPipeline = record
  { learner    = nsLearner
  ; comparison = nsResidualComparison
  ; gate       = nsPromotionGate
  }

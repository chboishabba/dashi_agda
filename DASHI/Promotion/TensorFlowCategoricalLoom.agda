module DASHI.Promotion.TensorFlowCategoricalLoom where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionHomology as PH
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionConstructor as PCON

----------------------------------------------------------------------
-- TensorFlow: grammar-generated tensor projection category.
--
-- Γ_TF is an architecture/training grammar, not a constraint grammar.
-- Training selects fθ ∈ Hom_Γ_TF(InputCarrier, PredictionSurface).
--
--   Γ_TF =
--     { input schema
--     , network architecture
--     , layer types
--     , activation functions
--     , parameter shapes
--     , loss function
--     , optimiser
--     , learning-rate schedule
--     , regularisation
--     , training data
--     , batching / order
--     , stopping criterion
--     }
--
-- Objects of 𝓟_TF:
--   RawInputCarrier        : the input data space
--   TensorSurface          : embedded/flattened tensor space
--   HiddenRepresentation   : a hidden-layer activation space
--   LogitSurface           : pre-activation output space
--   PredictionSurface      : the model output space
--   LossSurface            : the scalar loss space (training only)
--
-- Morphisms (postulated per-grammar):
--   embed          : RawInputCarrier → TensorSurface
--   denseLayer     : TensorSurface → HiddenRepresentation
--   hiddenToLogit  : HiddenRepresentation → LogitSurface
--   softmaxHead    : LogitSurface → PredictionSurface
--   lossEval       : PredictionSurface → LossSurface
--   gradientUpdate : LossSurface → TensorSurface  (training feedback)
--
-- Composite predictor:
--   fθ = softmaxHead ∘ hiddenToLogit ∘ denseLayer ∘ embed
--   Γ_TF ⊢ fθ : RawInputCarrier → PredictionSurface
--
-- Relation to TFL:
--   Hom_𝓟_TFL ⊂ Hom_𝓟_TF
--   TFL is a constrained subcategory. Every TFL model is a TF model,
--   but not every TF model is lattice-admissible.
--
-- Fibre: fθ⁻¹(y) = { x | fθ(x) = y }
--   TF loom = weave of learned neural fibres — how the projection
--   collapses input regions into the same output fibre.
--
-- Ladder:
--   TF:       unconstrained learned tensor projection category
--   TFL:      constrained learned tensor/lattice projection category
--   NS-AI:    learned + symbolic/proof/reasoning categories
--   DASHI:    grammar-generated categories + authority + residual
--             naturality + promotion + fibre/loom homology
----------------------------------------------------------------------

data TFObj : Set where
  rawInput          : TFObj
  tensorSurface     : TFObj
  hiddenRepr        : TFObj
  logitSurface      : TFObj
  predictionSurface : TFObj
  lossSurface       : TFObj

postulate
  InputCarrier        : Set
  TensorCarrier       : Set
  HiddenCarrier       : Set
  LogitCarrier        : Set
  PredictionCarrier   : Set
  LossCarrier         : Set

Underlying : TFObj → Set
Underlying rawInput          = InputCarrier
Underlying tensorSurface     = TensorCarrier
Underlying hiddenRepr        = HiddenCarrier
Underlying logitSurface      = LogitCarrier
Underlying predictionSurface = PredictionCarrier
Underlying lossSurface       = LossCarrier

-- The TF architecture/training grammar

record TFGrammar : Set where
  field
    inputSchema        : ⊤
    architecture       : ⊤
    layerTypes         : ⊤
    activationFunctions : ⊤
    parameterShapes    : ⊤
    lossFunction       : ⊤
    optimiser          : ⊤
    learningRate       : ⊤
    regularisation     : ⊤
    trainingData       : ⊤
    batchingOrder      : ⊤
    stoppingCriterion  : ⊤
    grammarReading     : String

canonicalTFGrammar : TFGrammar
canonicalTFGrammar = record
  { inputSchema        = tt
  ; architecture       = tt
  ; layerTypes         = tt
  ; activationFunctions = tt
  ; parameterShapes    = tt
  ; lossFunction       = tt
  ; optimiser          = tt
  ; learningRate       = tt
  ; regularisation     = tt
  ; trainingData       = tt
  ; batchingOrder      = tt
  ; stoppingCriterion  = tt
  ; grammarReading     = "Gamma_TF (canonical architecture)"
  }

-- The projection category: objects are tensor pipeline stages,
-- morphisms are differentiable tensor programs

tfProjectionCategory : PC.ProjectionCategory
tfProjectionCategory = record
  { Obj             = TFObj
  ; Hom             = λ A B → Underlying A → Underlying B
  ; id              = λ x → x
  ; _∘_             = λ g f x → g (f x)
  ; id-left         = λ f → refl
  ; id-right        = λ f → refl
  ; assoc           = λ f g h → refl
  ; categoryReading = "Pi_TF(differentiable tensor programs)"
  }

-- Grammar-generated category: Γ_TF ↦ 𝓟_TF

tfGrammarCategory : GGC.GrammarGeneratedCategory
tfGrammarCategory = record
  { Grammar        = TFGrammar
  ; 𝓟              = λ _ → tfProjectionCategory
  ; grammarReading = "Gamma_TF = architecture/training grammar"
  }

----------------------------------------------------------------------
-- Pipeline morphisms (postulated, selected by training)
----------------------------------------------------------------------

postulate
  embed          : (Γ : TFGrammar) → InputCarrier → TensorCarrier
  denseLayer     : (Γ : TFGrammar) → TensorCarrier → HiddenCarrier
  hiddenToLogit  : (Γ : TFGrammar) → HiddenCarrier → LogitCarrier
  softmaxHead    : (Γ : TFGrammar) → LogitCarrier → PredictionCarrier
  lossEval       : (Γ : TFGrammar) → PredictionCarrier → LossCarrier
  gradientUpdate : (Γ : TFGrammar) → LossCarrier → TensorCarrier

-- Composite predictor: fθ = softmaxHead ∘ hiddenToLogit ∘ denseLayer ∘ embed

fPredict : (Γ : TFGrammar) → InputCarrier → PredictionCarrier
fPredict Γ x = softmaxHead Γ (hiddenToLogit Γ (denseLayer Γ (embed Γ x)))

----------------------------------------------------------------------
-- Default carriers for unused morphism branches
----------------------------------------------------------------------

postulate
  defaultInput        : InputCarrier
  defaultTensor       : TensorCarrier
  defaultHidden       : HiddenCarrier
  defaultLogit        : LogitCarrier
  defaultPrediction   : PredictionCarrier
  defaultLoss         : LossCarrier

defaultUnderlying : (B : TFObj) → Underlying B
defaultUnderlying rawInput          = defaultInput
defaultUnderlying tensorSurface     = defaultTensor
defaultUnderlying hiddenRepr        = defaultHidden
defaultUnderlying logitSurface      = defaultLogit
defaultUnderlying predictionSurface = defaultPrediction
defaultUnderlying lossSurface       = defaultLoss

----------------------------------------------------------------------
-- Fibre of a TF predictor: fθ⁻¹(y) = { x | fθ(x) = y }
----------------------------------------------------------------------

fibreOverPrediction : (Γ : TFGrammar) (y : PredictionCarrier) → Set
fibreOverPrediction Γ y = ⊤

----------------------------------------------------------------------
-- Constructor: TF training selects a predictor morphism
----------------------------------------------------------------------

constructTF : {A B : TFObj} (Γ : TFGrammar)
            → (Underlying A → Underlying B)
constructTF {rawInput} {tensorSurface} Γ       = embed Γ
constructTF {rawInput} {hiddenRepr} Γ           = λ x → denseLayer Γ (embed Γ x)
constructTF {rawInput} {logitSurface} Γ         = λ x → hiddenToLogit Γ (denseLayer Γ (embed Γ x))
constructTF {rawInput} {predictionSurface} Γ    = fPredict Γ
constructTF {tensorSurface} {hiddenRepr} Γ      = denseLayer Γ
constructTF {tensorSurface} {logitSurface} Γ    = λ x → hiddenToLogit Γ (denseLayer Γ x)
constructTF {tensorSurface} {predictionSurface} Γ = λ x → softmaxHead Γ (hiddenToLogit Γ (denseLayer Γ x))
constructTF {hiddenRepr} {logitSurface} Γ       = hiddenToLogit Γ
constructTF {hiddenRepr} {predictionSurface} Γ  = λ x → softmaxHead Γ (hiddenToLogit Γ x)
constructTF {logitSurface} {predictionSurface} Γ = softmaxHead Γ
constructTF {predictionSurface} {lossSurface} Γ  = lossEval Γ
constructTF {lossSurface} {tensorSurface} Γ      = gradientUpdate Γ
constructTF {A} {B} Γ = λ _ → defaultUnderlying B

tfConstructor : PCON.ProjectionConstructor tfProjectionCategory
tfConstructor = record
  { MethodCarrier = TFGrammar
  ; construct     = constructTF
  ; methodKind    = "TF training: architecture -> differentiable program"
  }

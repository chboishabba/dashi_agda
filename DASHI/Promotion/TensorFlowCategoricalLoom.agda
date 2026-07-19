module DASHI.Promotion.TensorFlowCategoricalLoom where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionConstructor as PCON
import DASHI.Core.ProjectionFibre as PF
import DASHI.Core.LoomEncoding as LE

----------------------------------------------------------------------
-- TensorFlow: grammar-generated tensor projection category.
--
-- Γ_TF is an architecture/training grammar.  Training constructs a
-- differentiable tensor-program morphism inside the generated category.
-- The fibre and loom below are concrete: a prediction fibre is the
-- dependent preimage of fPredict, and a weave is a transformation of the
-- input carrier whose residual records failure to preserve prediction.
----------------------------------------------------------------------

data TFObj : Set where
  rawInput          : TFObj
  tensorSurface     : TFObj
  hiddenRepr        : TFObj
  logitSurface      : TFObj
  predictionSurface : TFObj
  lossSurface       : TFObj

postulate
  InputCarrier      : Set
  TensorCarrier     : Set
  HiddenCarrier     : Set
  LogitCarrier      : Set
  PredictionCarrier : Set
  LossCarrier       : Set

Underlying : TFObj → Set
Underlying rawInput          = InputCarrier
Underlying tensorSurface     = TensorCarrier
Underlying hiddenRepr        = HiddenCarrier
Underlying logitSurface      = LogitCarrier
Underlying predictionSurface = PredictionCarrier
Underlying lossSurface       = LossCarrier

record TFGrammar : Set where
  field
    inputSchema         : ⊤
    architecture        : ⊤
    layerTypes          : ⊤
    activationFunctions : ⊤
    parameterShapes     : ⊤
    lossFunction        : ⊤
    optimiser           : ⊤
    learningRate        : ⊤
    regularisation      : ⊤
    trainingData        : ⊤
    batchingOrder       : ⊤
    stoppingCriterion   : ⊤
    grammarReading      : String

canonicalTFGrammar : TFGrammar
canonicalTFGrammar = record
  { inputSchema         = tt
  ; architecture        = tt
  ; layerTypes          = tt
  ; activationFunctions = tt
  ; parameterShapes     = tt
  ; lossFunction        = tt
  ; optimiser           = tt
  ; learningRate        = tt
  ; regularisation      = tt
  ; trainingData        = tt
  ; batchingOrder       = tt
  ; stoppingCriterion   = tt
  ; grammarReading      = "Gamma_TF (canonical architecture)"
  }

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

tfGrammarCategory : GGC.GrammarGeneratedCategory
tfGrammarCategory = record
  { Grammar        = TFGrammar
  ; 𝓟              = λ _ → tfProjectionCategory
  ; grammarReading = "Gamma_TF = architecture/training grammar"
  }

postulate
  embed          : (Γ : TFGrammar) → InputCarrier → TensorCarrier
  denseLayer     : (Γ : TFGrammar) → TensorCarrier → HiddenCarrier
  hiddenToLogit  : (Γ : TFGrammar) → HiddenCarrier → LogitCarrier
  softmaxHead    : (Γ : TFGrammar) → LogitCarrier → PredictionCarrier
  lossEval       : (Γ : TFGrammar) → PredictionCarrier → LossCarrier
  gradientUpdate : (Γ : TFGrammar) → LossCarrier → TensorCarrier

fPredict : (Γ : TFGrammar) → InputCarrier → PredictionCarrier
fPredict Γ x = softmaxHead Γ (hiddenToLogit Γ (denseLayer Γ (embed Γ x)))

postulate
  defaultInput      : InputCarrier
  defaultTensor     : TensorCarrier
  defaultHidden     : HiddenCarrier
  defaultLogit      : LogitCarrier
  defaultPrediction : PredictionCarrier
  defaultLoss       : LossCarrier

defaultUnderlying : (B : TFObj) → Underlying B
defaultUnderlying rawInput          = defaultInput
defaultUnderlying tensorSurface     = defaultTensor
defaultUnderlying hiddenRepr        = defaultHidden
defaultUnderlying logitSurface      = defaultLogit
defaultUnderlying predictionSurface = defaultPrediction
defaultUnderlying lossSurface       = defaultLoss

----------------------------------------------------------------------
-- Concrete projection fibre.
----------------------------------------------------------------------

tfProjectionFibre : (Γ : TFGrammar) → PF.ProjectionFibre tfProjectionCategory
tfProjectionFibre Γ = record
  { Underlying   = Underlying
  ; Carrier      = rawInput
  ; Observable   = predictionSurface
  ; π            = fPredict Γ
  ; apply        = λ f x → f x
  ; fibreReading = "TF prediction fibre: dependent preimage of fPredict"
  }

fibreOverPrediction : (Γ : TFGrammar) (y : PredictionCarrier) → Set
fibreOverPrediction Γ y = PF.Fibre (tfProjectionFibre Γ) y

----------------------------------------------------------------------
-- Concrete loom over the prediction fibre.
--
-- A strand is an input.  A weave transforms inputs.  The residual says
-- two weaves disagree when their transformed inputs project to different
-- predictions.  Closure is exactly pointwise fibre preservation.
----------------------------------------------------------------------

tfLoomEncoding : (Γ : TFGrammar) →
  LE.LoomEncoding tfProjectionCategory (tfProjectionFibre Γ)
tfLoomEncoding Γ = record
  { Strand            = InputCarrier
  ; Weave             = InputCarrier → InputCarrier
  ; weaveId           = λ x _ → x
  ; weaveSeq          = λ g f x → g (f x)
  ; ProjectionSurface = PredictionCarrier
  ; project           = fPredict Γ
  ; fibreEquivalent   = λ x y → fPredict Γ x ≡ fPredict Γ y
  ; residual          = λ f g → ∀ x → fPredict Γ (f x) ≡ fPredict Γ (g x)
  ; closed            = λ f g → ∀ x → fPredict Γ (f x) ≡ fPredict Γ (g x)
  ; loomReading       = "TF loom: input transformations compared by prediction-fibre preservation"
  }

----------------------------------------------------------------------
-- Constructor: training selects a tensor-program morphism.
----------------------------------------------------------------------

constructTF : {A B : TFObj} (Γ : TFGrammar) → Underlying A → Underlying B
constructTF {rawInput} {tensorSurface} Γ          = embed Γ
constructTF {rawInput} {hiddenRepr} Γ             = λ x → denseLayer Γ (embed Γ x)
constructTF {rawInput} {logitSurface} Γ           = λ x → hiddenToLogit Γ (denseLayer Γ (embed Γ x))
constructTF {rawInput} {predictionSurface} Γ      = fPredict Γ
constructTF {tensorSurface} {hiddenRepr} Γ        = denseLayer Γ
constructTF {tensorSurface} {logitSurface} Γ      = λ x → hiddenToLogit Γ (denseLayer Γ x)
constructTF {tensorSurface} {predictionSurface} Γ = λ x → softmaxHead Γ (hiddenToLogit Γ (denseLayer Γ x))
constructTF {hiddenRepr} {logitSurface} Γ         = hiddenToLogit Γ
constructTF {hiddenRepr} {predictionSurface} Γ    = λ x → softmaxHead Γ (hiddenToLogit Γ x)
constructTF {logitSurface} {predictionSurface} Γ  = softmaxHead Γ
constructTF {predictionSurface} {lossSurface} Γ   = lossEval Γ
constructTF {lossSurface} {tensorSurface} Γ       = gradientUpdate Γ
constructTF {A} {B} Γ                             = λ _ → defaultUnderlying B

tfConstructor : PCON.ProjectionConstructor tfProjectionCategory
tfConstructor = record
  { MethodCarrier = TFGrammar
  ; construct     = constructTF
  ; methodKind    = "TF training: architecture -> differentiable program"
  }

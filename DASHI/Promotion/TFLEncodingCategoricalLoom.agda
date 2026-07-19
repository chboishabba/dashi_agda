module DASHI.Promotion.TFLEncodingCategoricalLoom where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionConstructor as PCON
import DASHI.Core.ProjectionFibre as PF
import DASHI.Core.LoomEncoding as LE

----------------------------------------------------------------------
-- TensorFlow Lattice: grammar-generated constrained projection category.
--
-- Γ_TFL generates the admissible constrained predictor class. Training
-- selects a morphism inside that category.  The fibre and loom are
-- concrete dependent structures over the learned composite predictor.
----------------------------------------------------------------------

data TFLObj : Set where
  rawFeature        : TFLObj
  calibratedFeature : TFLObj
  latticeCell       : TFLObj
  interpolated      : TFLObj
  prediction        : TFLObj
  outputCalibrated  : TFLObj

postulate
  FeatureCarrier          : Set
  CalibratedCarrier       : Set
  LatticeCellCarrier      : Set
  InterpolatedCarrier     : Set
  PredictionCarrier       : Set
  OutputCalibratedCarrier : Set

Underlying : TFLObj → Set
Underlying rawFeature        = FeatureCarrier
Underlying calibratedFeature = CalibratedCarrier
Underlying latticeCell       = LatticeCellCarrier
Underlying interpolated      = InterpolatedCarrier
Underlying prediction        = PredictionCarrier
Underlying outputCalibrated  = OutputCalibratedCarrier

record TFLGrammar : Set where
  field
    calibratorCount         : ⊤
    knotCount               : ⊤
    latticeResolution       : ⊤
    interpolationRule       : ⊤
    monotonicityConstraints : ⊤
    convexityConstraints    : ⊤
    trustConstraints        : ⊤
    interactionConstraints  : ⊤
    regulariserWeights      : ⊤
    ensembleWiring          : ⊤
    outputCalibrationSpec   : ⊤
    grammarReading          : String

canonicalTFLGrammar : TFLGrammar
canonicalTFLGrammar = record
  { calibratorCount         = tt
  ; knotCount               = tt
  ; latticeResolution       = tt
  ; interpolationRule       = tt
  ; monotonicityConstraints = tt
  ; convexityConstraints    = tt
  ; trustConstraints        = tt
  ; interactionConstraints  = tt
  ; regulariserWeights      = tt
  ; ensembleWiring          = tt
  ; outputCalibrationSpec   = tt
  ; grammarReading          = "Gamma_TFL (canonical lattice grammar)"
  }

tflProjectionCategory : PC.ProjectionCategory
tflProjectionCategory = record
  { Obj             = TFLObj
  ; Hom             = λ A B → Underlying A → Underlying B
  ; id              = λ x → x
  ; _∘_             = λ g f x → g (f x)
  ; id-left         = λ f → refl
  ; id-right        = λ f → refl
  ; assoc           = λ f g h → refl
  ; categoryReading = "Pi_TFL(admissible constrained predictors)"
  }

tflGrammarCategory : GGC.GrammarGeneratedCategory
tflGrammarCategory = record
  { Grammar        = TFLGrammar
  ; 𝓟              = λ _ → tflProjectionCategory
  ; grammarReading = "Gamma_TFL = lattice/constraint grammar"
  }

postulate
  calibrate          : (Γ : TFLGrammar) → FeatureCarrier → CalibratedCarrier
  latticeInterpolate : (Γ : TFLGrammar) → CalibratedCarrier → LatticeCellCarrier
  constrainedPredict : (Γ : TFLGrammar) → LatticeCellCarrier → PredictionCarrier
  outputCalibrate    : (Γ : TFLGrammar) → PredictionCarrier → OutputCalibratedCarrier

fPredict : (Γ : TFLGrammar) → FeatureCarrier → OutputCalibratedCarrier
fPredict Γ x = outputCalibrate Γ (constrainedPredict Γ (latticeInterpolate Γ (calibrate Γ x)))

postulate
  defaultFeature          : FeatureCarrier
  defaultCalibrated       : CalibratedCarrier
  defaultLatticeCell      : LatticeCellCarrier
  defaultInterpolated     : InterpolatedCarrier
  defaultPrediction       : PredictionCarrier
  defaultOutputCalibrated : OutputCalibratedCarrier

defaultUnderlying : (B : TFLObj) → Underlying B
defaultUnderlying rawFeature        = defaultFeature
defaultUnderlying calibratedFeature = defaultCalibrated
defaultUnderlying latticeCell       = defaultLatticeCell
defaultUnderlying interpolated      = defaultInterpolated
defaultUnderlying prediction        = defaultPrediction
defaultUnderlying outputCalibrated  = defaultOutputCalibrated

----------------------------------------------------------------------
-- Concrete dependent prediction fibre.
----------------------------------------------------------------------

tflProjectionFibre : (Γ : TFLGrammar) → PF.ProjectionFibre tflProjectionCategory
tflProjectionFibre Γ = record
  { Underlying   = Underlying
  ; Carrier      = rawFeature
  ; Observable   = outputCalibrated
  ; π            = fPredict Γ
  ; apply        = λ f x → f x
  ; fibreReading = "TFL prediction fibre: dependent preimage of the constrained predictor"
  }

fibreOverPrediction : (Γ : TFLGrammar) (y : OutputCalibratedCarrier) → Set
fibreOverPrediction Γ y = PF.Fibre (tflProjectionFibre Γ) y

----------------------------------------------------------------------
-- Concrete TFL loom.
--
-- Strands are feature vectors.  Weaves are feature transformations.  A
-- closed residual means two feature transformations remain equivalent
-- after the complete constrained/calibrated predictor.
----------------------------------------------------------------------

tflLoomEncoding : (Γ : TFLGrammar) →
  LE.LoomEncoding tflProjectionCategory (tflProjectionFibre Γ)
tflLoomEncoding Γ = record
  { Strand            = FeatureCarrier
  ; Weave             = FeatureCarrier → FeatureCarrier
  ; weaveId           = λ x _ → x
  ; weaveSeq          = λ g f x → g (f x)
  ; ProjectionSurface = OutputCalibratedCarrier
  ; project           = fPredict Γ
  ; fibreEquivalent   = λ x y → fPredict Γ x ≡ fPredict Γ y
  ; residual          = λ f g → ∀ x → fPredict Γ (f x) ≡ fPredict Γ (g x)
  ; closed            = λ f g → ∀ x → fPredict Γ (f x) ≡ fPredict Γ (g x)
  ; loomReading       = "TFL loom: feature transformations compared by constrained prediction-fibre preservation"
  }

----------------------------------------------------------------------
-- Constructor: TFL training selects an admissible predictor morphism.
----------------------------------------------------------------------

constructTFL : {A B : TFLObj} (Γ : TFLGrammar) → Underlying A → Underlying B
constructTFL {rawFeature} {calibratedFeature} Γ       = calibrate Γ
constructTFL {rawFeature} {latticeCell} Γ             = λ x → latticeInterpolate Γ (calibrate Γ x)
constructTFL {rawFeature} {prediction} Γ              = λ x → constrainedPredict Γ (latticeInterpolate Γ (calibrate Γ x))
constructTFL {rawFeature} {outputCalibrated} Γ         = fPredict Γ
constructTFL {calibratedFeature} {latticeCell} Γ       = latticeInterpolate Γ
constructTFL {calibratedFeature} {prediction} Γ        = λ x → constrainedPredict Γ (latticeInterpolate Γ x)
constructTFL {calibratedFeature} {outputCalibrated} Γ  = λ x → outputCalibrate Γ (constrainedPredict Γ (latticeInterpolate Γ x))
constructTFL {latticeCell} {prediction} Γ              = constrainedPredict Γ
constructTFL {latticeCell} {outputCalibrated} Γ        = λ x → outputCalibrate Γ (constrainedPredict Γ x)
constructTFL {prediction} {outputCalibrated} Γ         = outputCalibrate Γ
constructTFL {A} {B} Γ                                 = λ _ → defaultUnderlying B

tflConstructor : PCON.ProjectionConstructor tflProjectionCategory
tflConstructor = record
  { MethodCarrier = TFLGrammar
  ; construct     = constructTFL
  ; methodKind    = "TFL training: lattice grammar -> admissible predictor"
  }

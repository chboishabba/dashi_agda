module DASHI.Promotion.TFLEncodingCategoricalLoom where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionHomology as PH
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionConstructor as PCON

----------------------------------------------------------------------
-- TensorFlow Lattice: grammar-generated projection category.
--
-- Grammar Γ_TFL generates the admissible constrained predictor class.
-- Training selects a morphism inside the category, not the category
-- itself.
--
--   Γ_TFL = lattice/constraint grammar:
--     { feature calibrators
--     , calibration knots
--     , lattice graph / lattice resolution
--     , interpolation rule
--     , monotonicity constraints
--     , convexity constraints
--     , trust constraints
--     , interaction constraints
--     , regularisers
--     , ensemble wiring
--     , output calibration
--     }
--
-- Objects of 𝓟_TFL:
--   RawFeatureCarrier       : the input feature space
--   CalibratedFeatureSurface: per-feature calibrated space
--   LatticeCellSurface      : the lattice interpolation space
--   InterpolatedSurface     : the continuous interpolated space
--   PredictionSurface       : the raw prediction space
--   OutputCalibratedSurface : the final calibrated output space
--
-- Morphisms (one per pipeline stage):
--   calibrate          : RawFeatureCarrier → CalibratedFeatureSurface
--   latticeInterpolate : CalibratedFeatureSurface → LatticeCellSurface
--   constrainedPredict : LatticeCellSurface → PredictionSurface
--   outputCalibrate    : PredictionSurface → OutputCalibratedSurface
--
-- Learned predictor f = outputCalibrate ∘ constrainedPredict
--                       ∘ latticeInterpolate ∘ calibrate.
--   f : RawFeatureCarrier → OutputCalibratedSurface
--   Γ_TFL ⊢ f admissible
--     meaning f respects monotonicity, calibration, trust, etc.
--
-- Fibre: f⁻¹(y) = { x | f(x) = y }
--   TFL loom = weave encoding of fibres, and how they deform
--   under lattice refinement, calibration changes, or constraint
--   changes.
--
-- Homology: which prediction/fibre structures persist across
--   admissible grammar changes?
----------------------------------------------------------------------

-- Objects of the TFL projection category

data TFLObj : Set where
  rawFeature          : TFLObj
  calibratedFeature   : TFLObj
  latticeCell         : TFLObj
  interpolated        : TFLObj
  prediction          : TFLObj
  outputCalibrated    : TFLObj

-- The feature and prediction carriers are abstract sets

postulate
  FeatureCarrier        : Set
  CalibratedCarrier     : Set
  LatticeCellCarrier    : Set
  InterpolatedCarrier   : Set
  PredictionCarrier     : Set
  OutputCalibratedCarrier : Set

Underlying : TFLObj → Set
Underlying rawFeature        = FeatureCarrier
Underlying calibratedFeature = CalibratedCarrier
Underlying latticeCell       = LatticeCellCarrier
Underlying interpolated      = InterpolatedCarrier
Underlying prediction        = PredictionCarrier
Underlying outputCalibrated  = OutputCalibratedCarrier

-- The TFL constraint grammar (Γ_TFL)

record TFLGrammar : Set where
  field
    calibratorCount        : ⊤
    knotCount              : ⊤
    latticeResolution      : ⊤
    interpolationRule      : ⊤
    monotonicityConstraints : ⊤
    convexityConstraints   : ⊤
    trustConstraints       : ⊤
    interactionConstraints : ⊤
    regulariserWeights     : ⊤
    ensembleWiring         : ⊤
    outputCalibrationSpec  : ⊤
    grammarReading         : String

canonicalTFLGrammar : TFLGrammar
canonicalTFLGrammar = record
  { calibratorCount        = tt
  ; knotCount              = tt
  ; latticeResolution      = tt
  ; interpolationRule      = tt
  ; monotonicityConstraints = tt
  ; convexityConstraints   = tt
  ; trustConstraints       = tt
  ; interactionConstraints = tt
  ; regulariserWeights     = tt
  ; ensembleWiring         = tt
  ; outputCalibrationSpec  = tt
  ; grammarReading         = "Gamma_TFL (canonical lattice grammar)"
  }

-- The projection category: objects are TFL pipeline stages,
-- morphisms are admissible constrained maps between carriers

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

-- Grammar-generated category: Γ_TFL ↦ 𝓟_TFL.
-- Each grammar instance generates the same category structure;
-- the grammar selects which morphisms are admissible.

tflGrammarCategory : GGC.GrammarGeneratedCategory
tflGrammarCategory = record
  { Grammar        = TFLGrammar
  ; 𝓟              = λ _ → tflProjectionCategory
  ; grammarReading = "Gamma_TFL = lattice/constraint grammar"
  }

----------------------------------------------------------------------
-- The four pipeline morphisms (postulated, selected by grammar)
----------------------------------------------------------------------

postulate
  calibrate          : (Γ : TFLGrammar) → FeatureCarrier → CalibratedCarrier
  latticeInterpolate : (Γ : TFLGrammar) → CalibratedCarrier → LatticeCellCarrier
  constrainedPredict : (Γ : TFLGrammar) → LatticeCellCarrier → PredictionCarrier
  outputCalibrate    : (Γ : TFLGrammar) → PredictionCarrier → OutputCalibratedCarrier

-- Composite predictor: f = outputCalibrate ∘ constrainedPredict
--                       ∘ latticeInterpolate ∘ calibrate

fPredict : (Γ : TFLGrammar) → FeatureCarrier → OutputCalibratedCarrier
fPredict Γ x = outputCalibrate Γ (constrainedPredict Γ (latticeInterpolate Γ (calibrate Γ x)))

----------------------------------------------------------------------
-- Fibre of a TFL predictor: f⁻¹(y) = { x | f(x) = y }
----------------------------------------------------------------------

fibreOverPrediction : (Γ : TFLGrammar) (y : OutputCalibratedCarrier) → Set
fibreOverPrediction Γ y = ⊤

----------------------------------------------------------------------
-- Default carrier values for unused morphism branches
----------------------------------------------------------------------

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
-- Constructor: TFL training selects a predictor morphism inside the
-- category
----------------------------------------------------------------------

constructTFL : {A B : TFLObj} (Γ : TFLGrammar)
            → (Underlying A → Underlying B)
constructTFL {rawFeature} {calibratedFeature} Γ = calibrate Γ
constructTFL {rawFeature} {latticeCell} Γ       = λ x → latticeInterpolate Γ (calibrate Γ x)
constructTFL {rawFeature} {prediction} Γ        = λ x → constrainedPredict Γ (latticeInterpolate Γ (calibrate Γ x))
constructTFL {rawFeature} {outputCalibrated} Γ  = fPredict Γ
constructTFL {calibratedFeature} {latticeCell} Γ  = latticeInterpolate Γ
constructTFL {calibratedFeature} {prediction} Γ   = λ x → constrainedPredict Γ (latticeInterpolate Γ x)
constructTFL {calibratedFeature} {outputCalibrated} Γ = λ x → outputCalibrate Γ (constrainedPredict Γ (latticeInterpolate Γ x))
constructTFL {latticeCell} {prediction} Γ          = constrainedPredict Γ
constructTFL {latticeCell} {outputCalibrated} Γ    = λ x → outputCalibrate Γ (constrainedPredict Γ x)
constructTFL {prediction} {outputCalibrated} Γ     = outputCalibrate Γ
constructTFL {A} {B} Γ = λ _ → defaultUnderlying B

tflConstructor : PCON.ProjectionConstructor tflProjectionCategory
tflConstructor = record
  { MethodCarrier = TFLGrammar
  ; construct     = constructTFL
  ; methodKind    = "TFL training: lattice grammar -> admissible predictor"
  }

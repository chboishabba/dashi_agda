module DASHI.Geo.EarthEmbeddingInterpretabilityExact where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Vec.Base using (Vec; []; _∷_)
import DASHI.Geo.EarthEmbeddingWoogarooExact as Earth
import DASHI.Geo.EarthEmbeddingGeometryExact as Geometry

------------------------------------------------------------------------
-- LEARNED COORDINATES ARE NOT DEFINED AS PHYSICAL VARIABLES.
-- A supervised probing map or a derivative estimate does not constitute
-- a causal intervention or an independently verified field observation.
--
-- Literature:
--   Rahman (2026): https://arxiv.org/abs/2602.10354
--   Rahman et al. (2026): https://arxiv.org/abs/2604.18715
--   Feng et al. (2026): https://arxiv.org/abs/2607.03949
--   Public weights/inference: https://github.com/ucam-eo/tessera
------------------------------------------------------------------------

-- Sensor and physical decoder carriers remain polymorphic in the scalar
-- representation. Their analytic derivative hypotheses are separately typed.
record LearnedEncoder (Input Scalar : Set) (d : Nat) : Set where
  constructor learned-encoder
  field
    encode : Input → Vec Scalar d
    checkpointHash : String
    preprocessingReceipt : String
    modelVersion : String

record PhysicalTarget (m : Nat) : Set where
  constructor physical-target
  field
    groundTruthSource : String
    targetUnits : String
    sampledPopulation : String
    observationWindow : String

-- The derivative is *supplied and certified separately*; this type alone
-- does not prove differentiability or even refer to the intended real field.
record DifferentiableEncoder (Scalar : Set) (inputDim embedDim : Nat) : Set₁ where
  constructor differentiable-encoder
  field
    encode : Vec Scalar inputDim → Vec Scalar embedDim
    derivative : Vec Scalar inputDim →
      (Vec Scalar inputDim → Vec Scalar embedDim)
    derivativeProofReceipt : String
    checkpointHash : String

record DifferentiableDecoder (Scalar : Set) (embedDim outputDim : Nat) : Set₁ where
  constructor differentiable-decoder
  field
    predict : Vec Scalar embedDim → Vec Scalar outputDim
    derivative : Vec Scalar embedDim →
      (Vec Scalar embedDim → Vec Scalar outputDim)
    derivativeProofReceipt : String
    calibrationReceipt : String

-- This is the formal compositional candidate for the encoder/decoder
-- derivative. To call it a Jacobian, its two chain-rule premises must be
-- supplied in a constructive real calculus owner, not a string receipt.
chainCandidate : ∀ {Scalar : Set} {p d m : Nat} →
  (e : DifferentiableEncoder Scalar p d) →
  (g : DifferentiableDecoder Scalar d m) →
  (x δ : Vec Scalar p) → Vec Scalar m
chainCandidate e g x δ =
  DifferentiableDecoder.derivative g
    (DifferentiableEncoder.encode e x)
    (DifferentiableEncoder.derivative e x δ)

record LocalTangent (Scalar : Set) (embedDim intrinsicDim : Nat) : Set₁ where
  constructor local-tangent
  field
    center : Vec Scalar embedDim
    tangent : Vec Scalar intrinsicDim → Vec Scalar embedDim
    geometryEstimator : String
    validationReceipt : String

tangentCandidate : ∀ {Scalar : Set} {d k m : Nat} →
  DifferentiableDecoder Scalar d m →
  LocalTangent Scalar d k →
  Vec Scalar k → Vec Scalar m
tangentCandidate g chart v =
  DifferentiableDecoder.derivative g (LocalTangent.center chart)
    (LocalTangent.tangent chart v)

-- Interpretation is relative to model version, labelled independent
-- observations, study population and the geometric locality of the probe.
record ValidatedInterpretation (d m : Nat) : Set where
  constructor validated-interpretation
  field
    physicalTarget : PhysicalTarget m
    labelledTrainingReceipt : String
    spatialHoldoutReceipt : String
    temporalHoldoutReceipt : String
    qualityAndMissingnessReceipt : String
    localGradientReceipt : String
    independentMeasurementReceipt : String
    transferRegionReceipt : String

record SensorAttribution : Set where
  constructor sensor-attribution
  field
    opticalBandAndTime : String
    radarBandAndTime : String
    preprocessingAndMask : String
    integratedGradientOrPerturbationMethod : String
    modelCheckpointHash : String
    physicalValidityReview : String

record InterventionEvidence : Set where
  constructor intervention-evidence
  field
    beforeAcquisition : String
    afterAcquisition : String
    interventionAdmissibility : String
    holdoutAndUncertainty : String

-- Invertible coordinate changes preserve the total composed physical
-- prediction. Therefore a coordinate dictionary is not unique by default.
reparameterisationInvariance :
  ∀ {Input A B Output : Set}
  (encode : Input → A) (change : A → B) (undo : B → A)
  (decode : A → Output) →
  ((a : A) → undo (change a) ≡ a) →
  (x : Input) →
  decode (undo (change (encode x))) ≡ decode (encode x)
reparameterisationInvariance encode change undo decode inverse x =
  cong decode (inverse (encode x))

-- A concrete nested Matryoshka prefix identity independent of scalar type.
prefixOnAppend :
  ∀ {Scalar : Set} {k suffix : Nat}
  (xs : Vec Scalar k) (ys : Vec Scalar suffix) →
  Geometry.take k suffix (Geometry.prefixWhole xs ys) ≡ xs
prefixOnAppend = Geometry.takeAppend

record WoogarooInterpretabilityProtocol : Set where
  constructor woogaroo-interpretability-protocol
  field
    fieldLabelOwner : String
    alphaEarthBlackBoxDecoder : String
    tesseraOpenEncoderVersion : String
    exactSpatialTemporalMatching : String
    perPrefixBenchmark : String
    tangentRestrictedValidation : String
    interventionAdmissibility : String
    lesCanopyAndLidarComparison : String
    nonPromotionBoundary : String

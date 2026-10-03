module DASHI.Geo.EarthEmbeddingGeometryExact where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Vec.Base using (Vec; []; _∷_)
open import DASHI.Geo.EarthEmbeddingWoogarooExact using (Model; alphaEarth; tessera; tesseraV2; embeddingDimension)

-- Source provenance:
-- Rahman 2026 https://arxiv.org/abs/2602.10354
-- Rahman et al. 2026 https://arxiv.org/abs/2604.18715
-- TESSERA v2 https://arxiv.org/abs/2607.03949
-- Ou and Zheng 2026 https://doi.org/10.1029/2025GL121604

Vector : Nat → Set
Vector n = Vec Nat n

-- A total Fin-free prefix operator; the source operator truncates rather
-- than claims any accuracy retention. Its element domain is polymorphic.
take : ∀ {A : Set} (n m : Nat) → Vec A (n + m) → Vec A n
take zero m xs = []
take (suc n) m (x ∷ xs) = x ∷ take n m xs

-- Vectors with an explicit suffix are prefix-coherent by construction.
prefixWhole : ∀ {A : Set} {n m : Nat} →
  Vec A n → Vec A m → Vec A (n + m)
prefixWhole [] ys = ys
prefixWhole (x ∷ xs) ys = x ∷ prefixWhole xs ys

takeAppend : ∀ {A : Set} {n m : Nat} (xs : Vec A n) (ys : Vec A m) →
  take n m (prefixWhole xs ys) ≡ xs
takeAppend [] ys = refl
takeAppend (x ∷ xs) ys rewrite takeAppend xs ys = refl

-- Evidence for a physical field remains a supplied certified observation.
record FiniteEmbedding (m : Model) : Set where
  constructor finiteEmbedding
  field
    location : String
    annualWindow : Nat
    coordinates : Vec Nat (embeddingDimension m)
    sourceReceipt : String

-- Claims about floating point, normalisation and latent coordinates must be
-- implemented with the repository's constructive real-number machinery;
-- Nat-valued vectors here only witness dimension and prefix shape.

record EmpiricalDimensionReport : Set where
  constructor dimensionReport
  field
    ambient : Nat
    effectiveEstimate : String
    localIntrinsicEstimate : String
    physicalVariablesDecoded : Nat
    sampledPopulation : String
    methodAndUncertainty : String
    sourceReference : String

record PhysicalDecoderEvidence : Set where
  constructor decoderEvidence
  field
    geographicHoldout : String
    temporalHoldout : String
    labelProvenance : String
    metricsReceipt : String
    calibrationReceipt : String

record QuantisationEvidence : Set where
  constructor quantisationEvidence
  field
    encoderVersion : String
    storageType : String
    perCoordinateErrorBound : String
    aggregateErrorBound : String
    calibrationReceipt : String

record LocalManifoldHypothesis : Set where
  constructor localManifold
  field
    chosenNeighbourhood : String
    tangentEstimator : String
    smoothnessCondition : String
    rotationDiagnostic : String
    heldOutCheck : String

record CrossModelCorrespondence : Set where
  constructor correspondence
  field
    sameCellAndTimeReceipt : String
    alphaProjection : String
    tesseraProjection : String
    latentSpaceMetric : String
    trainingLossReceipt : String
    heldOutResidualReceipt : String

record TemporalStabilityEvidence : Set where
  constructor stability
  field
    acquisitionSampling : String
    unchangedSurfaceReference : String
    missingnessProtocol : String
    temporalValidation : String

record CitedStudy : Set where
  constructor citedStudy
  field
    paper : String
    population : String
    measuredQuantity : String
    reportedResult : String
    methodologicalScope : String

rahmanPhysical : CitedStudy
rahmanPhysical = citedStudy
  "https://arxiv.org/abs/2602.10354"
  "12.1 million samples, continental US, 2017-2023"
  "26 environmental variables; 12 with R2 > 0.90"
  "temperature/elevation R2 near 0.97"
  "empirical reconstruction and held-out analysis, not an algebraic invariant"

rahmanGeometry : CitedStudy
rahmanGeometry = citedStudy
  "https://arxiv.org/abs/2604.18715"
  "12.1 million continental US samples"
  "spectral participation ratio and local intrinsic dimension"
  "13.3 effective, local intrinsic near 10"
  "does not establish a globally smooth embedding manifold"

australianCatchments : CitedStudy
australianCatchments = citedStudy
  "https://doi.org/10.1029/2025GL121604"
  "455 Australian catchments, 2017-2022"
  "median error reduction in disturbed basins"
  "11.5 percent"
  "published study; no Woogaroo-specific validation"

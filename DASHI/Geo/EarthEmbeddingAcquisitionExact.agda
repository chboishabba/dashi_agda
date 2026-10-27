module DASHI.Geo.EarthEmbeddingAcquisitionExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Vec.Base using (Vec)
open import Data.Fin.Base using (Fin)
import Data.Vec.Base as Vec
import DASHI.Geo.EarthEmbeddingInterpretabilityExact as Interpretation
import DASHI.Geo.EarthEmbeddingWoogarooExact as Earth
import DASHI.Geo.EarthEmbeddingAttributedSourcesExact as Sources
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as ParetoSnowball

-- Frozen input selection follows actual TESSERA student/infer.py binning.
-- Different cloud masks may produce different selections; their discrete
-- dependence is explicitly OUTSIDE the differentiable carrier.
record AcquisitionSelection (n k : Nat) : Set where
  constructor frozen-selection
  field
    indices : Vec (Fin n) k
    bandOrderSource : String
    cloudMaskReceipt : String
    dayOfYearReceipt : String
    selectionAlgorithmRevision : String

selectObservation :
  ∀ {Scalar : Set} {n k : Nat} →
  AcquisitionSelection n k → Vec Scalar n → Vec Scalar k
selectObservation acquisition values =
  Vec.map (Vec.lookup values) (AcquisitionSelection.indices acquisition)

-- A fixed selection cannot observe changes outside its selected coordinates.
selectedInvariant :
  ∀ {Scalar : Set} {n k : Nat}
  (acquisition : AcquisitionSelection n k)
  (xs ys : Vec Scalar n) →
  Vec.map (Vec.lookup xs) (AcquisitionSelection.indices acquisition) ≡
  Vec.map (Vec.lookup ys) (AcquisitionSelection.indices acquisition) →
  selectObservation acquisition xs ≡ selectObservation acquisition ys
selectedInvariant acquisition xs ys selectedAgreement = selectedAgreement

predictionInvariant :
  ∀ {Scalar Output : Set} {n k : Nat}
  (acquisition : AcquisitionSelection n k)
  (decoder : Vec Scalar k → Output)
  (xs ys : Vec Scalar n) →
  selectObservation acquisition xs ≡ selectObservation acquisition ys →
  decoder (selectObservation acquisition xs) ≡
  decoder (selectObservation acquisition ys)
predictionInvariant acquisition decoder xs ys selectionEquality =
  cong decoder selectionEquality

data PreprocessingMode : Set where
  sentinel2Raw reflectanceScale : PreprocessingMode
  sentinel1Ascending sentinel1Descending : PreprocessingMode
  fixedCloudMask fixedDayOfYear fixedBinSelection : PreprocessingMode

record AcquiredGradientReceipt : Set where
  constructor gradient-receipt
  field
    pretrainedCheckpointHash : String
    upstreamInferenceRevision : String
    pixelTimeSeriesHash : String
    selectedS2Indices : String
    selectedS1Indices : String
    physicalProbeHeldoutSource : String
    derivativeOrIGMethod : String
    physicalAdmissibility : String
    nonPromotionBoundary : String


------------------------------------------------------------------------
-- Canonical TOE convergence for learned Earth embeddings.
--
-- This terminal owner reuses the existing acquisition, interpretation,
-- provenance, and Woogaroo surfaces. It creates no physical interpretation
-- from a learned coordinate and no legal authority from a model output.
------------------------------------------------------------------------

data LearnedCoordinateCreatesPhysicalIdentity : Set where

learnedCoordinateDoesNotCreatePhysicalIdentity :
  LearnedCoordinateCreatesPhysicalIdentity → ⊥
learnedCoordinateDoesNotCreatePhysicalIdentity ()

data GradientCreatesCausalEnvironmentalEffect : Set where

gradientDoesNotCreateCausalEnvironmentalEffect :
  GradientCreatesCausalEnvironmentalEffect → ⊥
gradientDoesNotCreateCausalEnvironmentalEffect ()

data ModelOutputCreatesIndependentFieldMeasurement : Set where

modelOutputDoesNotCreateIndependentFieldMeasurement :
  ModelOutputCreatesIndependentFieldMeasurement → ⊥
modelOutputDoesNotCreateIndependentFieldMeasurement ()

data EmbeddingCreatesLegalAuthority : Set where

embeddingDoesNotCreateLegalAuthority :
  EmbeddingCreatesLegalAuthority → ⊥
embeddingDoesNotCreateLegalAuthority ()

canonicalWoogarooInterpretabilityProtocol :
  Interpretation.WoogarooInterpretabilityProtocol
canonicalWoogarooInterpretabilityProtocol =
  Interpretation.woogaroo-interpretability-protocol
    "independent georeferenced field-label source"
    "AlphaEarth published embedding probe; no public encoder backprop authority asserted"
    "verified open TESSERA checkpoint and preprocessing revision"
    "same cell, year, sensor window, CRS, QA mask, and source hash"
    "16/32/64/128 prefixes evaluated on one held-out split"
    "local tangent restriction and held-out error remain separate from physical causality"
    "counterfactual sensor edits require independently justified physical admissibility"
    "reuse existing LES canopy/LiDAR calibration and legal-consumer boundary"
    "learned coordinates, gradients, co-location, model accuracy, and source repetition do not create physical truth, causal effect, legal authority, or statutory significance"

record EarthEmbeddingTOEReceipt : Set₁ where
  constructor earth-embedding-toe-receipt
  field
    alphaEarthDimension : Nat
    tesseraDimension : Nat
    tesseraV2Dimension : Nat
    sourceAtlas : Attribution.AttributedSourceAtlas
    interpretabilityProtocol : Interpretation.WoogarooInterpretabilityProtocol
    learnedCoordinateCreatesPhysicalIdentity : Bool
    gradientCreatesCausalEffect : Bool
    modelOutputCreatesIndependentMeasurement : Bool
    embeddingCreatesLegalAuthority : Bool
    esdSurfaceEdited : Bool

open EarthEmbeddingTOEReceipt public

canonicalEarthEmbeddingTOEReceipt : EarthEmbeddingTOEReceipt
canonicalEarthEmbeddingTOEReceipt =
  earth-embedding-toe-receipt
    (Earth.embeddingDimension Earth.alphaEarth)
    (Earth.embeddingDimension Earth.tessera)
    (Earth.embeddingDimension Earth.tesseraV2)
    Sources.earthEmbeddingSourceAtlas
    canonicalWoogarooInterpretabilityProtocol
    false
    false
    false
    false
    false

alphaEarthDimensionIs64 :
  alphaEarthDimension canonicalEarthEmbeddingTOEReceipt ≡ 64
alphaEarthDimensionIs64 = refl

tesseraDimensionIs128 :
  tesseraDimension canonicalEarthEmbeddingTOEReceipt ≡ 128
tesseraDimensionIs128 = refl

tesseraV2DimensionIs128 :
  tesseraV2Dimension canonicalEarthEmbeddingTOEReceipt ≡ 128
tesseraV2DimensionIs128 = refl

learnedCoordinatePromotionStillFalse :
  learnedCoordinateCreatesPhysicalIdentity canonicalEarthEmbeddingTOEReceipt
  ≡ false
learnedCoordinatePromotionStillFalse = refl

gradientCausalityPromotionStillFalse :
  gradientCreatesCausalEffect canonicalEarthEmbeddingTOEReceipt ≡ false
gradientCausalityPromotionStillFalse = refl

independentMeasurementPromotionStillFalse :
  modelOutputCreatesIndependentMeasurement canonicalEarthEmbeddingTOEReceipt
  ≡ false
independentMeasurementPromotionStillFalse = refl

legalAuthorityPromotionStillFalse :
  embeddingCreatesLegalAuthority canonicalEarthEmbeddingTOEReceipt ≡ false
legalAuthorityPromotionStillFalse = refl

earthEmbeddingESDSurfaceStillReadOnly :
  esdSurfaceEdited canonicalEarthEmbeddingTOEReceipt ≡ false
earthEmbeddingESDSurfaceStillReadOnly = refl

canonicalEarthEmbeddingTOEZKPFrame : ParetoSnowball.TOEZKPFrame
canonicalEarthEmbeddingTOEZKPFrame =
  ParetoSnowball.toe-zkp-frame
    "converge learned Earth-embedding acquisition, physical probing, local geometry, and Woogaroo validation into the DASHI TOE"
    "reuse existing EarthEmbedding, source-atlas, LES/Woogaroo, Pareto/Snowball process, and attribution owners before extending them"
    "normalize one terminal Earth-embedding receipt and expose exact non-promotion eliminators through the TOE aggregates"
    "learned coordinates, gradients, co-location, prefix performance, and model outputs do not create physical identity, causal effect, independent field measurement, legal authority, or continuum physics"
    "one Earth-observation interpretation and evidence lane; Fleet-58 identities remain fail-closed"
    "verified model and preprocessing identity, exact acquisition provenance, independent labels, spatial/temporal holdout, and existing theorem owners are required; ESD surfaces are read-only"
    "original AlphaEarth, TESSERA, Rahman, Ou/Zheng, Woogaroo, Ibrahim, Balaban, and meta-introspector attribution remains separate; standards are process lenses only"
    "TOE root, Unifier, and Unified aggregate reach the same receipt, source atlas, dimensions, and exact non-promotion gates without changing Fleet counts"
    "repository related/discover/lineage audit, forbidden-trust scan, ESD diff scan, source-owner alias check, Python producer tests, and Agda kernel check"
    false
    false
    false
    false

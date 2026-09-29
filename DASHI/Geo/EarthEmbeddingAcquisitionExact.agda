module DASHI.Geo.EarthEmbeddingAcquisitionExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.String using (String)
open import Data.Vec.Base using (Vec)
open import Data.Fin.Base using (Fin)
open import Data.Vec.Base as Vec using (lookup)
import DASHI.Geo.EarthEmbeddingInterpretabilityExact as Interpretation

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

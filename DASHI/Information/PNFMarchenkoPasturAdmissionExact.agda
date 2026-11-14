module DASHI.Information.PNFMarchenkoPasturAdmissionExact where

-- Reuse the existing PNF spectral classifier and the existing MP
-- calibration owner; do not create a second semantic authority.
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality

import DASHI.Information.PNFSpectralGeometry as PNF
import DASHI.Information.PNFMarchenkoPasturFiniteExact as MP
import DASHI.Interop.PNFSpectralNumericABICore as NumericABI

-- An MP null classification is a candidate-only numerical observation.
-- The evidence owners are chosen independently; no new PNF 'truth' is
-- constructible from an eigenvalue or an MP band receipt alone.
record MPPNFCandidate
  (K : PNF.ScalarStructure)
  (C : MP.MPFiniteCalibration K) : Set₁ where
  field
    classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)
    numericalEigenvalue : PNF.ScalarStructure.Scalar K
    spectralClass : PNF.SpectralClass
    classificationCorrect :
      spectralClass ≡
        PNF.NoiseClassifier.classify classifier numericalEigenvalue

open MPPNFCandidate public

mpCandidateAboveEdge :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (candidate : MPPNFCandidate K C) →
  PNF.ScalarStructure._<_ K
    (MP.MPFiniteCalibration.upperEdge C)
    (MPPNFCandidate.numericalEigenvalue candidate) →
  MPPNFCandidate.spectralClass candidate ≡
    PNF.candidateSignal
mpCandidateAboveEdge K C candidate above =
  let eq = MPPNFCandidate.classificationCorrect candidate
      proof = PNF.NoiseClassifier.above-null-band
        (MPPNFCandidate.classifier candidate) above
  in
  Relation.Binary.PropositionalEquality.trans eq proof

mpCandidateCannotPromoteNumericABI :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  MPPNFCandidate K C →
  NumericABI.PNFSpectralNumericABIPromotion → ⊥
mpCandidateCannotPromoteNumericABI K C candidate =
  NumericABI.pnfSpectralNumericABIPromotionImpossible

module DASHI.Reasoning.Trialectic369E6ExteriorSquareBridgeValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.Trialectic369E6ExteriorSquareBridgeExact as Bridge

fourTritProvenanceRetained :
  Bridge.existingFourTritProvenanceRetained Bridge.canonicalTrialectic369E6ExteriorSquareBoundary ≡ true
fourTritProvenanceRetained = refl

derivedCarrierDistinct :
  Bridge.derivedLag80DistinctFromRawPuncturedT4 Bridge.canonicalTrialectic369E6ExteriorSquareBoundary ≡ true
derivedCarrierDistinct = refl

sameActionRequired :
  Bridge.PGSp4WE6ActionRecognitionRequired Bridge.canonicalTrialectic369E6ExteriorSquareBoundary ≡ true
sameActionRequired = refl

cardinalityDoesNotCreateWeld :
  Bridge.cardinality80AloneCreatesWeld Bridge.canonicalTrialectic369E6ExteriorSquareBoundary ≡ false
cardinalityDoesNotCreateWeld = refl

baseCorrectnessDoesNotRequireE6 :
  Bridge.E6OntologyRequiredForBaseHyperformalCorrectness Bridge.canonicalTrialectic369E6ExteriorSquareBoundary ≡ false
baseCorrectnessDoesNotRequireE6 = refl

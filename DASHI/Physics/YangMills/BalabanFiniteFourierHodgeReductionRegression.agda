module DASHI.Physics.YangMills.BalabanFiniteFourierHodgeReductionRegression where

open import Agda.Builtin.Equality using (refl)

import DASHI.Physics.YangMills.BalabanFiniteFourierHodgeReduction as Hodge

------------------------------------------------------------------------
-- A one-point regression exercises the Fourier/Parseval rewrite chain and the
-- resulting uniform Hodge certificate. It proves no physical spectral gap.
------------------------------------------------------------------------

data One : Set where
  one : One

data Holds : Set where
  holds : Holds

oneBinary : One → One → One
oneBinary left right = one

hodgeData : Hodge.FiniteFourierHodgeData One One One One
hodgeData = record
  { fourier = λ state → one
  ; referenceEnergy = λ index state → one
  ; normSq = λ state → one
  ; frequencyNormSq = λ frequency → one
  ; symbolEnergy = λ index frequency → one
  ; scale = oneBinary
  ; LessEqual = λ left right → Holds
  ; Positive = λ value → Holds
  ; Nonnegative = λ value → Holds
  ; cBulk = one
  ; cBulkPositive = holds
  ; GaugeFixedTangent = λ index state → Holds
  ; SymbolKernel = λ index frequency → Holds
  ; ConstantMode = λ frequency → Holds
  ; SymbolKernelRemoved = λ index frequency → Holds
  ; finiteFourierDiagonalizesReferenceLaplacian =
      λ index state → refl
  ; fourierParsevalForBondFields = λ state → refl
  ; referenceSymbolNonnegative = λ index frequency → holds
  ; referenceSymbolKernelCharacterization =
      λ index frequency kernel → holds
  ; constraintsRemoveReferenceSymbolKernel =
      λ index state tangent → holds
  ; constrainedReferenceSymbolHasPositiveGap =
      λ index frequency removed → holds
  ; CBulkIndependentOfVolume = Holds
  ; CBulkIndependentOfLatticeSpacing = Holds
  ; CBulkIndependentOfScale = Holds
  ; CBulkUniformOverAdmissibleBackgrounds = Holds
  ; cBulkIndependentOfVolume = holds
  ; cBulkIndependentOfLatticeSpacing = holds
  ; cBulkIndependentOfScale = holds
  ; cBulkUniformOverAdmissibleBackgrounds = holds
  }

bulkHodgeRegression : Holds
bulkHodgeRegression =
  Hodge.bulkGaugeFixedHodgePoincare hodgeData one one holds

uniformHodgeCertificate : Hodge.UniformBulkHodgeCertificate One One One
uniformHodgeCertificate = Hodge.finiteFourierHodgeCertificate hodgeData

uniformHodgeRegression : Holds
uniformHodgeRegression =
  Hodge.UniformBulkHodgeCertificate.bulkGaugeFixedHodgePoincare
    uniformHodgeCertificate one one holds

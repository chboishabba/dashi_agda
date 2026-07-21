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
  { Hodge.fourier = λ state → one
  ; Hodge.referenceEnergy = λ index state → one
  ; Hodge.normSq = λ state → one
  ; Hodge.frequencyNormSq = λ frequency → one
  ; Hodge.symbolEnergy = λ index frequency → one
  ; Hodge.scale = oneBinary
  ; Hodge.LessEqual = λ left right → Holds
  ; Hodge.Positive = λ value → Holds
  ; Hodge.Nonnegative = λ value → Holds
  ; Hodge.cBulk = one
  ; Hodge.cBulkPositive = holds
  ; Hodge.GaugeFixedTangent = λ index state → Holds
  ; Hodge.SymbolKernel = λ index frequency → Holds
  ; Hodge.ConstantMode = λ frequency → Holds
  ; Hodge.SymbolKernelRemoved = λ index frequency → Holds
  ; Hodge.finiteFourierDiagonalizesReferenceLaplacian =
      λ index state → refl
  ; Hodge.fourierParsevalForBondFields = λ state → refl
  ; Hodge.referenceSymbolNonnegative = λ index frequency → holds
  ; Hodge.referenceSymbolKernelCharacterization =
      λ index frequency kernel → holds
  ; Hodge.constraintsRemoveReferenceSymbolKernel =
      λ index state tangent → holds
  ; Hodge.constrainedReferenceSymbolHasPositiveGap =
      λ index frequency removed → holds
  ; Hodge.CBulkIndependentOfVolume = Holds
  ; Hodge.CBulkIndependentOfLatticeSpacing = Holds
  ; Hodge.CBulkIndependentOfScale = Holds
  ; Hodge.CBulkUniformOverAdmissibleBackgrounds = Holds
  ; Hodge.cBulkIndependentOfVolume = holds
  ; Hodge.cBulkIndependentOfLatticeSpacing = holds
  ; Hodge.cBulkIndependentOfScale = holds
  ; Hodge.cBulkUniformOverAdmissibleBackgrounds = holds
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

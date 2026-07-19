module DASHI.Physics.YangMills.BalabanWeightedGreenKernelDecay where

open import DASHI.Physics.YangMills.BalabanGreenKernelDecayFinite

------------------------------------------------------------------------
-- The weighted operator estimate and the pointwise Green-kernel estimate are
-- different theorem surfaces.  A weighted column norm controls every matrix
-- entry in that column; removing the exponential weight then produces the
-- pointwise decay majorant used by the finite Green-kernel certificate.
------------------------------------------------------------------------

record WeightedGreenColumnControl (Site Scalar Bound : Set) : Set₁ where
  field
    green : Site → Site → Scalar
    distance : Site → Site → Bound
    norm : Scalar → Bound

    prefactor decayRate : Bound
    weight : Bound → Bound → Bound
    multiply : Bound → Bound → Bound
    exponentialMajorant : Bound → Bound → Bound → Bound

    LessEqual : Bound → Bound → Set
    lessEqualTrans : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    weightedColumnNorm : Site → Bound

    entryBelowWeightedColumn : ∀ left right →
      LessEqual
        (multiply
          (weight decayRate (distance left right))
          (norm (green left right)))
        (weightedColumnNorm right)

    weightedColumnBound : ∀ source →
      LessEqual (weightedColumnNorm source) prefactor

    removeWeight : ∀ left right →
      LessEqual
        (multiply
          (weight decayRate (distance left right))
          (norm (green left right)))
        prefactor →
      LessEqual
        (norm (green left right))
        (exponentialMajorant prefactor decayRate (distance left right))

open WeightedGreenColumnControl public

weightedColumnControlImpliesGreenDecay :
  ∀ {Site Scalar Bound} →
  WeightedGreenColumnControl Site Scalar Bound →
  FiniteGreenKernelDecay Site Scalar Bound
weightedColumnControlImpliesGreenDecay control = record
  { green = green control
  ; distance = distance control
  ; norm = norm control
  ; prefactor = prefactor control
  ; decayRate = decayRate control
  ; exponentialMajorant = exponentialMajorant control
  ; LessEqual = LessEqual control
  ; decay = λ left right →
      removeWeight control left right
        (lessEqualTrans control
          (entryBelowWeightedColumn control left right)
          (weightedColumnBound control right))
  }

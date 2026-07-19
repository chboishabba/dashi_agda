module DASHI.Physics.YangMills.BalabanGreenKernelDecayFinite where

record FiniteGreenKernelDecay (Site Scalar Bound : Set) : Set₁ where
  field
    green : Site → Site → Scalar
    distance : Site → Site → Bound
    norm : Scalar → Bound
    prefactor decayRate : Bound
    exponentialMajorant : Bound → Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    decay :
      ∀ left right →
      LessEqual (norm (green left right))
        (exponentialMajorant prefactor decayRate (distance left right))

open FiniteGreenKernelDecay public

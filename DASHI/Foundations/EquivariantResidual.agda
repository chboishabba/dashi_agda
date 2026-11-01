module DASHI.Foundations.EquivariantResidual where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.InvolutiveTernaryDynamics as ITD

------------------------------------------------------------------------
-- Residual is a typed comparison, not a presumed subtraction.  Concrete
-- instances may use ternary cancellation, group difference, chart defect,
-- prediction error, curvature, or another application-specific comparison.

record EquivariantResidual (D : ITD.InvolutiveDynamics) : Set₁ where
  field
    Reference : Set
    referenceι : Reference → Reference
    referenceι-involutive : ∀ e → referenceι (referenceι e) ≡ e

    Residual : Set
    residualι : Residual → Residual
    residualι-involutive : ∀ r → residualι (residualι r) ≡ r

    compare : ITD.State D → Reference → Residual
    compare-equivariant : ∀ s e →
      compare (ITD.stateι D s) (referenceι e) ≡
      residualι (compare s e)

open EquivariantResidual public

record ResidualBaseline
  (D : ITD.InvolutiveDynamics)
  (R : EquivariantResidual D) : Set₁ where
  field
    baseline : Reference R
    baseline-fixed : referenceι R baseline ≡ baseline
    vanishes : Residual R → Set
    baselineLaw : ITD.State D → Set

open ResidualBaseline public

record ResidualBoundary : Set where
  constructor boundary
  field
    subtractionNotAssumed : Set
    baselineMayBeContextual : Set
    vanishingLawRequiresInstance : Set
    applicationMeaningPromoted : Set

canonicalBoundary : ResidualBoundary
canonicalBoundary = boundary Set Set Set Set

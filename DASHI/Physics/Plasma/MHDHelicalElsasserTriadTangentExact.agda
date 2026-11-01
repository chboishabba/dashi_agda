module DASHI.Physics.Plasma.MHDHelicalElsasserTriadTangentExact where

------------------------------------------------------------------------
-- PAIRED MHD TRIAD TANGENT AFTER ELSASSER RECHART
--
-- The momentum and induction equations are carried together on the same
-- ordered p,q amplitude pair.  Their support is the same mixed Elsasser pair,
-- but their parity is different:
--
--   2 T_m = C_m ( z+_p z-_q + z-_p z+_q )
--   2 T_i = C_i ( z-_p z+_q - z+_p z-_q ).
--
-- This module owns the algebraic tangent shape.  A concrete PDE/Galerkin
-- application still owes the literal identification of C_m and C_i.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Plasma.ElsasserAmplitudeRechartAlgebraExact as A

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

  two : ∀ {r} {F : C3.RealField r} → C3.Carrier F
  two {F = F} = C3.add F (C3.one F) (C3.one F)

record PairedTriadCoefficient {r : _} (F : C3.RealField r) : Set r where
  constructor paired-triad-coefficient
  field
    momentumCoefficient : C3.Carrier F
    inductionCoefficient : C3.Carrier F
    literalMomentumCoefficientReceipt : Set
    literalInductionCoefficientReceipt : Set
    sameTriadGeometryReceipt : Set
    coefficientReference : String

open PairedTriadCoefficient public

momentumTangent :
  ∀ {r} {F : C3.RealField r} →
  PairedTriadCoefficient F →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F
momentumTangent {F = F} coefficients up bp uq bq =
  C3.multiply F
    (momentumCoefficient coefficients)
    (A.momentumAmplitude up bp uq bq)

inductionTangent :
  ∀ {r} {F : C3.RealField r} →
  PairedTriadCoefficient F →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F
inductionTangent {F = F} coefficients up bp uq bq =
  C3.multiply F
    (inductionCoefficient coefficients)
    (A.inductionAmplitude up bp uq bq)

momentumTangentElsasserExact :
  ∀ {r} {F : C3.RealField r}
    (coefficients : PairedTriadCoefficient F)
    (up bp uq bq : C3.Carrier F) →
  C3.multiply F two (momentumTangent coefficients up bp uq bq)
  ≡ C3.multiply F
      (momentumCoefficient coefficients)
      (C3.add F
        (A.plusMinusProduct up bp uq bq)
        (A.minusPlusProduct up bp uq bq))
momentumTangentElsasserExact {F = F} coefficients up bp uq bq =
  R.solve 5
    (λ cm up bp uq bq →
      (((R.Κ (C3.one F) R.⊕ R.Κ (C3.one F))
        R.⊗ (cm R.⊗ ((up R.⊗ uq) R.⊕ (R.⊝ (bp R.⊗ bq)))))
      R.⊜
      (cm R.⊗
        (((up R.⊕ bp) R.⊗ (uq R.⊕ (R.⊝ bq)))
          R.⊕ ((up R.⊕ (R.⊝ bp)) R.⊗ (uq R.⊕ bq)))))
    refl (momentumCoefficient coefficients) up bp uq bq
  where module R = Field.Solver F

inductionTangentElsasserExact :
  ∀ {r} {F : C3.RealField r}
    (coefficients : PairedTriadCoefficient F)
    (up bp uq bq : C3.Carrier F) →
  C3.multiply F two (inductionTangent coefficients up bp uq bq)
  ≡ C3.multiply F
      (inductionCoefficient coefficients)
      (sub
        (A.minusPlusProduct up bp uq bq)
        (A.plusMinusProduct up bp uq bq))
inductionTangentElsasserExact {F = F} coefficients up bp uq bq =
  R.solve 5
    (λ ci up bp uq bq →
      (((R.Κ (C3.one F) R.⊕ R.Κ (C3.one F))
        R.⊗ (ci R.⊗ ((up R.⊗ bq) R.⊕ (R.⊝ (bp R.⊗ uq)))))
      R.⊜
      (ci R.⊗
        (((up R.⊕ (R.⊝ bp)) R.⊗ (uq R.⊕ bq))
          R.⊕
          (R.⊝ ((up R.⊕ bp) R.⊗ (uq R.⊕ (R.⊝ bq)))))))
    refl (inductionCoefficient coefficients) up bp uq bq
  where module R = Field.Solver F

record PairedTangentBoundary : Set where
  constructor paired-tangent-boundary
  field
    momentumAndInductionHaveSameElsasserSupport : Bool
    momentumAndInductionHaveSameElsasserSupportIsTrue :
      momentumAndInductionHaveSameElsasserSupport ≡ true

    momentumAndInductionHaveSameMixedPairParity : Bool
    momentumAndInductionHaveSameMixedPairParityIsFalse :
      momentumAndInductionHaveSameMixedPairParity ≡ false

    pairedTangentAlgebraAloneProvesIdealInvariantConservation : Bool
    pairedTangentAlgebraAloneProvesIdealInvariantConservationIsFalse :
      pairedTangentAlgebraAloneProvesIdealInvariantConservation ≡ false

canonicalPairedTangentBoundary : PairedTangentBoundary
canonicalPairedTangentBoundary =
  paired-tangent-boundary true refl false refl false refl

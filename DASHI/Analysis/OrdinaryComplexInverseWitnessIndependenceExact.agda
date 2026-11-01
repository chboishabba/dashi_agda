module DASHI.Analysis.OrdinaryComplexInverseWitnessIndependenceExact where

open import DASHI.Core.Prelude

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar

------------------------------------------------------------------------
-- NONZERO-WITNESS INDEPENDENCE FOR THE EXISTING CONSTRUCTED FIELD OPERATIONS
--
-- Real reciprocal is indexed by a proof that the denominator is nonzero.
-- The field laws already imply uniqueness of the reciprocal value, without
-- requiring proof irrelevance of the Nonzero witness itself.
------------------------------------------------------------------------

realReciprocalWitnessIndependent :
  ∀ {R : Real.ConstructedOrderedCompleteReal} ->
  (D : Polar.RealDivisionAndSquareRoot R) ->
  (x : Real.Real R) ->
  (nx ny : Polar.Nonzero D x) ->
  Polar.reciprocal D x nx ≡ Polar.reciprocal D x ny
realReciprocalWitnessIndependent {R} D x nx ny =
  let
    rx = Polar.reciprocal D x nx
    ry = Polar.reciprocal D x ny
  in
  trans
    (sym (Real.mulOneRight R rx))
    (trans
      (cong (λ u -> Real._*_ R rx u)
        (sym (Polar.reciprocalRight D x ny)))
      (trans
        (sym (Real.mulAssoc R rx x ry))
        (trans
          (cong (λ u -> Real._*_ R u ry)
            (Polar.reciprocalLeft D x nx))
          (Real.mulOneLeft R ry))))

------------------------------------------------------------------------
-- The complex inverse uses the real reciprocal of normSqC.  Therefore the
-- same uniqueness theorem removes dependence on which NonzeroC witness was
-- used to obtain the norm-square nonzero proof.
------------------------------------------------------------------------

complexInverseWitnessIndependent :
  ∀ {R : Real.ConstructedOrderedCompleteReal}
    {D : Polar.RealDivisionAndSquareRoot R} ->
  (F : Polar.ComplexFieldAuthority R D) ->
  (z : Complex.ComplexPair R) ->
  (nz₁ nz₂ : Polar.NonzeroC F z) ->
  Polar.inverseC F z nz₁ ≡ Polar.inverseC F z nz₂
complexInverseWitnessIndependent {R} {D} F (Complex.complex a b) nz₁ nz₂ =
  let
    r₁ = Polar.reciprocal D
      (Complex.normSqC (Complex.complex a b))
      (Polar.nonzeroNormSq F (Complex.complex a b) nz₁)
    r₂ = Polar.reciprocal D
      (Complex.normSqC (Complex.complex a b))
      (Polar.nonzeroNormSq F (Complex.complex a b) nz₂)
    r₁≡r₂ =
      realReciprocalWitnessIndependent D
        (Complex.normSqC (Complex.complex a b))
        (Polar.nonzeroNormSq F (Complex.complex a b) nz₁)
        (Polar.nonzeroNormSq F (Complex.complex a b) nz₂)
  in
  cong₂ Complex.complex
    (cong (λ r -> Real._*_ R r a) r₁≡r₂)
    (cong (λ r -> Real._*_ R r (Real.neg R b)) r₁≡r₂)

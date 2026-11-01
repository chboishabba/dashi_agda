module DASHI.Physics.Closure.NSTriadKNLuoFiniteCascadeSpeedFluxNoGoExact where

------------------------------------------------------------------------
-- SOURCE UNDER AUDIT
--
-- Author: Rod Higgins.
-- Title: "Global Regularity of 3D Navier-Stokes: An Energy Argument".
-- DOI: 10.5281/zenodo.19601371.
-- Status: web/repository paper; not used as proof authority.
--
-- AUDITED STEP
--
-- A displayed cascade estimate has the schematic form
--
--   Pi_K <= alpha * K * E_K^(3/2).
--
-- That upper bound alone does not force the flux to vanish at high frequency.
-- In radical-free variables choose a positive scale s with reciprocal r,
--
--   K = s^3,
--   E_K = r^2,
--   E_K^(3/2) = r^3,
--   s r = 1.
--
-- Then K E_K^(3/2) = s^3 r^3 = 1.  Hence alpha=1 permits a unit flux at every
-- supplied reciprocal scale.  Additional dynamical information is required:
-- a decaying tail, residence/variation control, an integrable flux budget, or
-- a strict comparison with viscosity.  This module refutes only the inference
-- from the schematic upper bound by itself.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary.Negation using (¬_)

record ReciprocalScale : Set where
  constructor reciprocalScale
  field
    scale : ℚ
    inverse : ℚ
    scaleTimesInverse : scale * inverse ≡ 1ℚ

open ReciprocalScale public

unitReciprocalScale : ReciprocalScale
unitReciprocalScale =
  reciprocalScale 1ℚ 1ℚ (ℚRing.solve [])

cube : ℚ → ℚ
cube x = x * x * x

cascadeRightHandSide : ReciprocalScale → ℚ
cascadeRightHandSide reciprocal =
  cube (scale reciprocal) * cube (inverse reciprocal)

cubeProductRearrangement :
  (s r : ℚ) →
  cube s * cube r ≡ (s * r) * (s * r) * (s * r)
cubeProductRearrangement s r =
  ℚRing.solve (s ∷ r ∷ [])

reciprocalCascadeIdentity :
  (reciprocal : ReciprocalScale) →
  cascadeRightHandSide reciprocal ≡ 1ℚ
reciprocalCascadeIdentity reciprocal =
  trans
    (cubeProductRearrangement
      (scale reciprocal)
      (inverse reciprocal))
    (let sr = scaleTimesInverse reciprocal
     in
     trans
       (congThreeProducts sr)
       (ℚRing.solve []))
  where
  congThreeProducts :
    ∀ {x y : ℚ} →
    x ≡ y →
    x * x * x ≡ y * y * y
  congThreeProducts refl = refl

unitFluxAllowedByCascadeBound :
  (reciprocal : ReciprocalScale) →
  1ℚ ≤ cascadeRightHandSide reciprocal
unitFluxAllowedByCascadeBound reciprocal
  rewrite reciprocalCascadeIdentity reciprocal =
  ℚP.≤-refl

unitFluxIsNotStrictlyBelowItsBound :
  ¬ (1ℚ < 1ℚ)
unitFluxIsNotStrictlyBelowItsBound =
  ℚP.<-irrefl refl

record FiniteCascadeSpeedNoGoWitness
    (reciprocal : ReciprocalScale) : Set where
  constructor finiteCascadeSpeedNoGoWitness
  field
    exactScaleTailBalance :
      cascadeRightHandSide reciprocal ≡ 1ℚ
    unitFluxSatisfiesDisplayedBound :
      1ℚ ≤ cascadeRightHandSide reciprocal
    displayedBoundDoesNotForceStrictDecay :
      ¬ (1ℚ < 1ℚ)

canonicalFiniteCascadeSpeedNoGoWitness :
  (reciprocal : ReciprocalScale) →
  FiniteCascadeSpeedNoGoWitness reciprocal
canonicalFiniteCascadeSpeedNoGoWitness reciprocal =
  finiteCascadeSpeedNoGoWitness
    (reciprocalCascadeIdentity reciprocal)
    (unitFluxAllowedByCascadeBound reciprocal)
    unitFluxIsNotStrictlyBelowItsBound

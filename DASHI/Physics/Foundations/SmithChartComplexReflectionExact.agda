module DASHI.Physics.Foundations.SmithChartComplexReflectionExact where

------------------------------------------------------------------------
-- SMITH-CHART / COMPLEX-REFLECTION CORE
--
-- Electrical-engineering notation:
--
--   j_EE^2 = -1
--
-- uses "j" for the imaginary unit because "i" is conventionally available
-- for current.  This object is NOT the modular j-invariant.
--
-- For normalized impedance z = Z/Z0, the Smith-chart reflection coordinate is
--
--   Gamma(z) = (z - 1) / (z + 1).
--
-- The normalized admittance involution z |-> 1/z acts by
--
--   Gamma(1/z) = - Gamma(z),
--
-- under the ordinary field-safety assumptions.  Complex conjugation commutes
-- with the same fractional-linear map.
--
-- This module keeps those statements abstract over a complex field interface
-- so the geometry can be reused by ConcreteComplex/Bishop/Lean backends
-- without asserting an unsafe division implementation here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

record SmithComplexField : Set₁ where
  field
    C : Set

    zero one jEE : C
    neg : C → C
    add sub mul div : C → C → C
    conjugate : C → C

    jSquaredIsMinusOne :
      mul jEE jEE ≡ neg one

    conjugateOne :
      conjugate one ≡ one

    conjugateSub :
      ∀ x y →
      conjugate (sub x y)
      ≡ sub (conjugate x) (conjugate y)

    conjugateAdd :
      ∀ x y →
      conjugate (add x y)
      ≡ add (conjugate x) (conjugate y)

    conjugateDiv :
      ∀ x y →
      conjugate (div x y)
      ≡ div (conjugate x) (conjugate y)

    reciprocal : C → C

    smithAdmittanceLaw :
      ∀ z →
      div
        (sub (reciprocal z) one)
        (add (reciprocal z) one)
      ≡
      neg
        (div
          (sub z one)
          (add z one))

open SmithComplexField public

normalizedReflection :
  (F : SmithComplexField) →
  C F → C F
normalizedReflection F z =
  div F
    (sub F z (one F))
    (add F z (one F))

normalizedAdmittance :
  (F : SmithComplexField) →
  C F → C F
normalizedAdmittance F =
  reciprocal F

smithAdmittanceRotatesReflectionByHalfTurn :
  (F : SmithComplexField) →
  (z : C F) →
  normalizedReflection F (normalizedAdmittance F z)
  ≡
  neg F (normalizedReflection F z)
smithAdmittanceRotatesReflectionByHalfTurn F z =
  smithAdmittanceLaw F z

smithReflectionConjugates :
  (F : SmithComplexField) →
  (z : C F) →
  conjugate F (normalizedReflection F z)
  ≡
  normalizedReflection F (conjugate F z)
smithReflectionConjugates F z
  rewrite conjugateDiv F
            (sub F z (one F))
            (add F z (one F))
        | conjugateSub F z (one F)
        | conjugateAdd F z (one F)
        | conjugateOne F = refl

------------------------------------------------------------------------
-- Observation layers.
--
-- Full Gamma retains a complex reflection coordinate.  Phase-only and
-- finite-sector observers may forget radial/magnitude information.
------------------------------------------------------------------------

record SmithPhaseObserver (F : SmithComplexField) : Set₁ where
  field
    Phase : Set
    phaseOf : C F → Phase

open SmithPhaseObserver public

record SameSmithPhaseCollision
    {F : SmithComplexField}
    (O : SmithPhaseObserver F) : Set₁ where
  field
    leftGamma rightGamma : C F
    samePhase :
      phaseOf O leftGamma
      ≡
      phaseOf O rightGamma
    differentReflection :
      leftGamma ≡ rightGamma → ⊥

open SameSmithPhaseCollision public

SmithPhaseDeterminesExactReflection :
  ∀ {F} →
  SmithPhaseObserver F →
  Set
SmithPhaseDeterminesExactReflection {F} O =
  (x y : C F) →
  phaseOf O x ≡ phaseOf O y →
  x ≡ y

smithPhaseCollisionRefutesExactRecovery :
  ∀ {F}
    {O : SmithPhaseObserver F} →
  SameSmithPhaseCollision O →
  ¬ SmithPhaseDeterminesExactReflection O
smithPhaseCollisionRefutesExactRecovery collision exact =
  differentReflection collision
    (exact
      (leftGamma collision)
      (rightGamma collision)
      (samePhase collision))

------------------------------------------------------------------------
-- Naming / role firewall.
------------------------------------------------------------------------

record SmithChartNotationFirewall : Set where
  constructor smith-chart-notation-firewall
  field
    engineeringJIsImaginaryUnit : Bool
    smithGammaIsReflectionCoordinate : Bool
    smithTransformIsFractionalLinear : Bool
    admittanceIsHalfTurnOnGamma : Bool
    conjugationCommutesWithSmithTransform : Bool

    engineeringJIsModularJInvariant : Bool
    smithGammaIsModularJInvariant : Bool
    smithPhaseIsPhasedArrayBearing : Bool
    phaseOnlySmithObserverRecoversFullGammaGenerally : Bool

open SmithChartNotationFirewall public

canonicalSmithChartNotationFirewall :
  SmithChartNotationFirewall
canonicalSmithChartNotationFirewall =
  smith-chart-notation-firewall
    true true true true true
    false false false false

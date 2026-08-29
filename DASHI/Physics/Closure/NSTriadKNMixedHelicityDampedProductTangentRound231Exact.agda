module DASHI.Physics.Closure.NSTriadKNMixedHelicityDampedProductTangentRound231Exact where

------------------------------------------------------------------------
-- ROUND231 / EXACT DAMPED-FORCED TANGENT OF ONE MIXED-HELICITY PRODUCT
--
-- For one + / - pair c = uP+ x uQ-, if
--
--   d uP+ = -rhoP uP+ + fP+,
--   d uQ- = -rhoQ uQ- + fQ-,
--
-- then bilinearity gives exactly
--
--   d c
--     = -(rhoP+rhoQ) c
--       + fP+ x uQ-
--       + uP+ x fQ-.
--
-- This is the local dynamic equation behind the Round228 spacetime quantity.
-- Round230 proves that after complete fixed-output summation the two forcing
-- terms reduce to one signed mixed-helicity commutator; Round229 proves that
-- the variable viscous rates cannot be replaced by their cellwise lower bound
-- after coherent summation without another covariance estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94

mixedProduct :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
mixedProduct = Cross.complex3Cross

mixedProductTangent :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
mixedProductTangent uP uQ dP dQ =
  C3.complex3Add
    (Cross.complex3Cross dP uQ)
    (Cross.complex3Cross uP dQ)

mixedProductForcing :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
mixedProductForcing uP uQ fP fQ =
  C3.complex3Add
    (Cross.complex3Cross fP uQ)
    (Cross.complex3Cross uP fQ)

twoModeNegativeDecay :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Complex F
twoModeNegativeDecay rhoP rhoQ =
  C3.complexAdd (R94.negativeReal rhoP) (R94.negativeReal rhoQ)

complex3ScaleScalarAdd :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F) (v : C3.Complex3 F) →
  C3.complex3Add (C3.complex3Scale a v) (C3.complex3Scale b v)
  ≡ C3.complex3Scale (C3.complexAdd a b) v
complex3ScaleScalarAdd {F = F} a b (C3.complex3 x y z) =
  Algebra.complex3Ext
    (R.solve 3 (λ a b x → (a R.⊗ x) R.⊕ (b R.⊗ x) R.⊜ (a R.⊕ b) R.⊗ x) refl a b x)
    (R.solve 3 (λ a b y → (a R.⊗ y) R.⊕ (b R.⊗ y) R.⊜ (a R.⊕ b) R.⊗ y) refl a b y)
    (R.solve 3 (λ a b z → (a R.⊗ z) R.⊕ (b R.⊗ z) R.⊜ (a R.⊕ b) R.⊗ z) refl a b z)
  where module R = Ring.Solver F

complex3RegroupFour :
  ∀ {r} {F : C3.RealField r}
    (a b c d : C3.Complex3 F) →
  C3.complex3Add
    (C3.complex3Add a b)
    (C3.complex3Add c d)
  ≡ C3.complex3Add
      (C3.complex3Add a c)
      (C3.complex3Add b d)
complex3RegroupFour {F = F}
    (C3.complex3 ax ay az) (C3.complex3 bx by bz)
    (C3.complex3 cx cy cz) (C3.complex3 dx dy dz) =
  Algebra.complex3Ext
    (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl ax bx cx dx)
    (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl ay by cy dy)
    (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl az bz cz dz)
  where module R = Ring.Solver F

mixedProductDampedNetworkEquation :
  ∀ {r} {F : C3.RealField r}
    (rhoP rhoQ : C3.Carrier F)
    (uP uQ fP fQ : C3.Complex3 F) →
  mixedProductTangent uP uQ
    (R94.dampedPlusForcing rhoP uP fP)
    (R94.dampedPlusForcing rhoQ uQ fQ)
  ≡
  C3.complex3Add
    (C3.complex3Scale (twoModeNegativeDecay rhoP rhoQ)
      (mixedProduct uP uQ))
    (mixedProductForcing uP uQ fP fQ)
mixedProductDampedNetworkEquation {F = F}
    rhoP rhoQ uP uQ fP fQ =
  let
    sP = R94.negativeReal rhoP
    sQ = R94.negativeReal rhoQ
    c = mixedProduct uP uQ
    fp = Cross.complex3Cross fP uQ
    fq = Cross.complex3Cross uP fQ
  in
  trans
    (cong₂ C3.complex3Add
      (trans
        (R94.crossAddLeft (C3.complex3Scale sP uP) fP uQ)
        (cong₂ C3.complex3Add (R94.crossScaleLeft sP uP uQ) refl))
      (trans
        (R94.crossAddRight uP (C3.complex3Scale sQ uQ) fQ)
        (cong₂ C3.complex3Add (R94.crossScaleRight sQ uP uQ) refl)))
    (trans
      (complex3RegroupFour
        (C3.complex3Scale sP c) fp
        (C3.complex3Scale sQ c) fq)
      (cong₂ C3.complex3Add
        (complex3ScaleScalarAdd sP sQ c)
        refl))

round231MixedHelicityDampedProductEquationClosed : Bool
round231MixedHelicityDampedProductEquationClosed = true

round231CellwiseDampingBecomesCoherentDampingAutomatically : Bool
round231CellwiseDampingBecomesCoherentDampingAutomatically = false

round231FixedOutputForcingVanishesAutomatically : Bool
round231FixedOutputForcingVanishesAutomatically = false

round231PackageAClosed : Bool
round231PackageAClosed = false

round231ClayPromotion : Bool
round231ClayPromotion = false

round231MixedHelicityDampedProductEquationClosedIsTrue :
  round231MixedHelicityDampedProductEquationClosed ≡ true
round231MixedHelicityDampedProductEquationClosedIsTrue = refl

round231CellwiseDampingBecomesCoherentDampingAutomaticallyIsFalse :
  round231CellwiseDampingBecomesCoherentDampingAutomatically ≡ false
round231CellwiseDampingBecomesCoherentDampingAutomaticallyIsFalse = refl

round231FixedOutputForcingVanishesAutomaticallyIsFalse :
  round231FixedOutputForcingVanishesAutomatically ≡ false
round231FixedOutputForcingVanishesAutomaticallyIsFalse = refl

round231PackageAClosedIsFalse : round231PackageAClosed ≡ false
round231PackageAClosedIsFalse = refl

round231ClayPromotionIsFalse : round231ClayPromotion ≡ false
round231ClayPromotionIsFalse = refl

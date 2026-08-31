module DASHI.Physics.Closure.NSTriadKNHelicalDampedProjectorLinearityRound381Exact where

------------------------------------------------------------------------
-- ROUND381 / BIDI: CONSTRUCT R292 PROJECTOR LINEARITY FROM OLD EXACT ALGEBRA
--
-- R292 left `HelicalDampedProjectorLinearity` as a small same-object seam.
-- The needed algebra was already in-repo:
--
--   R82  : Leray is additive,
--   R73  : Leray commutes with complex scalars,
--   R157 : normalized curl is additive/scalar-linear and therefore commutes
--          with damped-plus-forcing.
--
-- Since P_+/- are literally half times (P +/- normalizedCurl), the remaining
-- proof is only commutative-ring regrouping on the exact C3 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as R82
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCellDampedTangentRound292Exact as R292

F : C3.RealField _
F = Rational.rationalRealField

lerayDampedPlusForcing :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (mode : Z3.FourierMode)
  (rho : ℚ)
  (u f : C3.Complex3 F) →
  C3.lerayProject3 E I mode (R94.dampedPlusForcing rho u f)
  ≡ R94.dampedPlusForcing rho
      (C3.lerayProject3 E I mode u)
      (C3.lerayProject3 E I mode f)
lerayDampedPlusForcing E I mode rho u f =
  trans
    (R82.lerayProjectAdd E I mode
      (C3.complex3Scale (R94.negativeReal rho) u) f)
    (cong₂ C3.complex3Add
      (R73.lerayProjectComplexScale E I mode (R94.negativeReal rho) u)
      refl)

plusRegroup :
  (h r : C3.Complex F)
  (a b c d : C3.Complex3 F) →
  C3.complex3Scale h
    (C3.complex3Add
      (C3.complex3Add (C3.complex3Scale r a) c)
      (C3.complex3Add (C3.complex3Scale r b) d))
  ≡
  C3.complex3Add
    (C3.complex3Scale r
      (C3.complex3Scale h (C3.complex3Add a b)))
    (C3.complex3Scale h (C3.complex3Add c d))
plusRegroup h r
    (C3.complex3 ax ay az) (C3.complex3 bx by bz)
    (C3.complex3 cx cy cz) (C3.complex3 dx dy dz) =
  Field.complex3Ext
    (solveCoord h r ax bx cx dx)
    (solveCoord h r ay by cy dy)
    (solveCoord h r az bz cz dz)
  where
  solveCoord :
    (h r a b c d : C3.Complex F) →
    C3.complexMultiply h
      (C3.complexAdd
        (C3.complexAdd (C3.complexMultiply r a) c)
        (C3.complexAdd (C3.complexMultiply r b) d))
    ≡ C3.complexAdd
        (C3.complexMultiply r
          (C3.complexMultiply h (C3.complexAdd a b)))
        (C3.complexMultiply h (C3.complexAdd c d))
  solveCoord h r a b c d =
    R.solve 6
      (λ h r a b c d →
        h R.⊗ (((r R.⊗ a) R.⊕ c) R.⊕ ((r R.⊗ b) R.⊕ d))
        R.⊜ (r R.⊗ (h R.⊗ (a R.⊕ b)))
              R.⊕ (h R.⊗ (c R.⊕ d)))
      refl h r a b c d
    where module R = Ring.Solver F

minusRegroup :
  (h r : C3.Complex F)
  (a b c d : C3.Complex3 F) →
  C3.complex3Scale h
    (C3.complex3Subtract
      (C3.complex3Add (C3.complex3Scale r a) c)
      (C3.complex3Add (C3.complex3Scale r b) d))
  ≡
  C3.complex3Add
    (C3.complex3Scale r
      (C3.complex3Scale h (C3.complex3Subtract a b)))
    (C3.complex3Scale h (C3.complex3Subtract c d))
minusRegroup h r
    (C3.complex3 ax ay az) (C3.complex3 bx by bz)
    (C3.complex3 cx cy cz) (C3.complex3 dx dy dz) =
  Field.complex3Ext
    (solveCoord h r ax bx cx dx)
    (solveCoord h r ay by cy dy)
    (solveCoord h r az bz cz dz)
  where
  solveCoord :
    (h r a b c d : C3.Complex F) →
    C3.complexMultiply h
      (C3.complexSubtract
        (C3.complexAdd (C3.complexMultiply r a) c)
        (C3.complexAdd (C3.complexMultiply r b) d))
    ≡ C3.complexAdd
        (C3.complexMultiply r
          (C3.complexMultiply h (C3.complexSubtract a b)))
        (C3.complexMultiply h (C3.complexSubtract c d))
  solveCoord h r a b c d =
    R.solve 6
      (λ h r a b c d →
        h R.⊗ ((((r R.⊗ a) R.⊕ c)
          R.⊕ (R.⊝ ((r R.⊗ b) R.⊕ d))))
        R.⊜ (r R.⊗ (h R.⊗ (a R.⊕ (R.⊝ b))))
              R.⊕ (h R.⊗ (c R.⊕ (R.⊝ d))))
      refl h r a b c d
    where module R = Ring.Solver F

canonicalHelicalDampedProjectorLinearity :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (S : Helical.HelicalModeScalars F) →
  R292.HelicalDampedProjectorLinearity E I S
canonicalHelicalDampedProjectorLinearity E I S = record
  { R292.plusDamped = plusLaw
  ; R292.minusDamped = minusLaw
  }
  where
  plusLaw :
    (mode : Z3.FourierMode) (rho : ℚ)
    (u f : C3.Complex3 F) →
    Helical.helicalProjectorPlus E I S mode
      (R94.dampedPlusForcing rho u f)
    ≡ R94.dampedPlusForcing rho
        (Helical.helicalProjectorPlus E I S mode u)
        (Helical.helicalProjectorPlus E I S mode f)
  plusLaw mode rho u f =
    let
      P-u = C3.lerayProject3 E I mode u
      P-f = C3.lerayProject3 E I mode f
      C-u = R157.R142.normalizedCurl E S mode u
      C-f = R157.R142.normalizedCurl E S mode f
      h = C3.realEmbed F (Helical.half S)
      r = R94.negativeReal rho
    in
    trans
      (cong
        (C3.complex3Scale h)
        (cong₂ C3.complex3Add
          (lerayDampedPlusForcing E I mode rho u f)
          (R157.normalizedCurlDampedPlusForcing E S mode rho u f)))
      (plusRegroup h r P-u C-u P-f C-f)

  minusLaw :
    (mode : Z3.FourierMode) (rho : ℚ)
    (u f : C3.Complex3 F) →
    Helical.helicalProjectorMinus E I S mode
      (R94.dampedPlusForcing rho u f)
    ≡ R94.dampedPlusForcing rho
        (Helical.helicalProjectorMinus E I S mode u)
        (Helical.helicalProjectorMinus E I S mode f)
  minusLaw mode rho u f =
    let
      P-u = C3.lerayProject3 E I mode u
      P-f = C3.lerayProject3 E I mode f
      C-u = R157.R142.normalizedCurl E S mode u
      C-f = R157.R142.normalizedCurl E S mode f
      h = C3.realEmbed F (Helical.half S)
      r = R94.negativeReal rho
    in
    trans
      (cong
        (C3.complex3Scale h)
        (cong₂ C3.complex3Subtract
          (lerayDampedPlusForcing E I mode rho u f)
          (R157.normalizedCurlDampedPlusForcing E S mode rho u f)))
      (minusRegroup h r P-u C-u P-f C-f)

round381R292ProjectorLinearityConstructed : Bool
round381R292ProjectorLinearityConstructed = true

round381UsesOnlyExistingFiniteAlgebra : Bool
round381UsesOnlyExistingFiniteAlgebra = true

round381NoAnalyticAuthorityIntroduced : Bool
round381NoAnalyticAuthorityIntroduced = true

round381R292ProjectorLinearityConstructedIsTrue :
  round381R292ProjectorLinearityConstructed ≡ true
round381R292ProjectorLinearityConstructedIsTrue = refl

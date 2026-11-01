{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CommutatorSwapPairProductRuleRound761Exact where

------------------------------------------------------------------------
-- ROUND761 / P/Q-SWAP-PAIRED R230 COMMUTATOR = SWAP-PAIRED PRODUCT RULE
--
-- Write, for one physical incidence beta,
--
--   A = F_p^+ x u_q^-,
--   D = u_p^+ x F_q^-,
--   B = F_p^- x u_q^+,
--   C = u_p^- x F_q^+.
--
-- Then
--
--   Comm(beta)      = A - B,
--   Product(beta)   = A + D.
--
-- Physical p/q swap plus cross anti-commutativity gives
--
--   A(swap beta) = -C,
--   B(swap beta) = -D,
--   D(swap beta) = -B.
--
-- Hence exactly
--
--   Comm(beta) + Comm(swap beta)
--     = Product(beta) + Product(swap beta).
--
-- This is pointwise vector algebra on the literal R230 carrier.  No fold,
-- estimate, norm, or PDE hypothesis is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeSelectedSwapAntisymmetryRound118Exact as R118
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230

minusVelocityPlusForce :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
minusVelocityPlusForce {E = E} {I = I} S velocity forcing tau =
  Cross.complex3Cross
    (Helical.helicalProjectorMinus E I S
      (Physical.p tau) (velocity (Physical.p tau)))
    (Helical.helicalProjectorPlus E I S
      (Physical.q tau) (forcing (Physical.q tau)))

firstForcingAfterSwapIsNegativeMinusVelocityPlusForce :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  R230.plusForceMinusVelocity S velocity forcing (Symmetry.swapTriad tau)
  ≡ C3.complex3Negate
      (minusVelocityPlusForce S velocity forcing tau)
firstForcingAfterSwapIsNegativeMinusVelocityPlusForce
    S velocity forcing tau =
  R118.crossAnticommutative
    (Helical.helicalProjectorMinus _ _ S
      (Physical.p tau) (velocity (Physical.p tau)))
    (Helical.helicalProjectorPlus _ _ S
      (Physical.q tau) (forcing (Physical.q tau)))

oppositeForcingAfterSwapIsNegativePlusVelocityMinusForce :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  R230.minusForcePlusVelocity S velocity forcing (Symmetry.swapTriad tau)
  ≡ C3.complex3Negate
      (R230.plusVelocityMinusForce S velocity forcing tau)
oppositeForcingAfterSwapIsNegativePlusVelocityMinusForce
    S velocity forcing tau =
  R118.crossAnticommutative
    (Helical.helicalProjectorPlus _ _ S
      (Physical.p tau) (velocity (Physical.p tau)))
    (Helical.helicalProjectorMinus _ _ S
      (Physical.q tau) (forcing (Physical.q tau)))

commProductPairAlgebra :
  ∀ {r} {F : C3.RealField r}
    (A B C D : C3.Complex3 F) →
  C3.complex3Add
    (C3.complex3Subtract A B)
    (C3.complex3Subtract
      (C3.complex3Negate C)
      (C3.complex3Negate D))
  ≡
  C3.complex3Add
    (C3.complex3Add A D)
    (C3.complex3Add
      (C3.complex3Negate C)
      (C3.complex3Negate B))
commProductPairAlgebra {F = F}
    (C3.complex3 ax ay az)
    (C3.complex3 bx by bz)
    (C3.complex3 cx cy cz)
    (C3.complex3 dx dy dz) =
  Field.complex3Ext
    (R.solve 4
      (λ a b c d →
        ((a R.⊕ (R.⊝ b)) R.⊕
          ((R.⊝ c) R.⊕ (R.⊝ (R.⊝ d))))
        R.⊜
        ((a R.⊕ d) R.⊕ ((R.⊝ c) R.⊕ (R.⊝ b))))
      refl ax bx cx dx)
    (R.solve 4
      (λ a b c d →
        ((a R.⊕ (R.⊝ b)) R.⊕
          ((R.⊝ c) R.⊕ (R.⊝ (R.⊝ d))))
        R.⊜
        ((a R.⊕ d) R.⊕ ((R.⊝ c) R.⊕ (R.⊝ b))))
      refl ay by cy dy)
    (R.solve 4
      (λ a b c d →
        ((a R.⊕ (R.⊝ b)) R.⊕
          ((R.⊝ c) R.⊕ (R.⊝ (R.⊝ d))))
        R.⊜
        ((a R.⊕ d) R.⊕ ((R.⊝ c) R.⊕ (R.⊝ b))))
      refl az bz cz dz)
  where
  module R = Ring.Solver F

commutatorSwapPairIsProductRuleSwapPair :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  C3.complex3Add
    (R230.forcingCommutatorCell S velocity forcing tau)
    (R230.forcingCommutatorCell
      S velocity forcing (Symmetry.swapTriad tau))
  ≡
  C3.complex3Add
    (R230.productRuleForcingCell S velocity forcing tau)
    (R230.productRuleForcingCell
      S velocity forcing (Symmetry.swapTriad tau))
commutatorSwapPairIsProductRuleSwapPair
    S velocity forcing tau =
  let
    A = R230.plusForceMinusVelocity S velocity forcing tau
    B = R230.minusForcePlusVelocity S velocity forcing tau
    C = minusVelocityPlusForce S velocity forcing tau
    D = R230.plusVelocityMinusForce S velocity forcing tau

    firstSwap =
      firstForcingAfterSwapIsNegativeMinusVelocityPlusForce
        S velocity forcing tau
    oppositeSwap =
      oppositeForcingAfterSwapIsNegativePlusVelocityMinusForce
        S velocity forcing tau
    secondSwap =
      R230.secondForcingAfterSwapIsNegativeMinusPlus
        S velocity forcing tau
  in
  trans
    (cong₂ C3.complex3Add
      refl
      (cong₂ C3.complex3Subtract firstSwap oppositeSwap))
    (trans
      (commProductPairAlgebra A B C D)
      (cong₂ C3.complex3Add
        refl
        (cong₂ C3.complex3Add
          (sym firstSwap)
          (sym secondSwap))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round761FirstForcingSwapLawClosed : Bool
round761FirstForcingSwapLawClosed = true

round761OppositeForcingSwapLawClosed : Bool
round761OppositeForcingSwapLawClosed = true

round761CommutatorSwapPairIsProductRuleSwapPair : Bool
round761CommutatorSwapPairIsProductRuleSwapPair = true

round761IntroducesEstimate : Bool
round761IntroducesEstimate = false

round761IntroducesNormOrAbsoluteValue : Bool
round761IntroducesNormOrAbsoluteValue = false

round761ClayPromotion : Bool
round761ClayPromotion = false

round761FirstForcingSwapLawClosedIsTrue :
  round761FirstForcingSwapLawClosed ≡ true
round761FirstForcingSwapLawClosedIsTrue = refl

round761OppositeForcingSwapLawClosedIsTrue :
  round761OppositeForcingSwapLawClosed ≡ true
round761OppositeForcingSwapLawClosedIsTrue = refl

round761CommutatorSwapPairIsProductRuleSwapPairIsTrue :
  round761CommutatorSwapPairIsProductRuleSwapPair ≡ true
round761CommutatorSwapPairIsProductRuleSwapPairIsTrue = refl

round761IntroducesEstimateIsFalse :
  round761IntroducesEstimate ≡ false
round761IntroducesEstimateIsFalse = refl

round761IntroducesNormOrAbsoluteValueIsFalse :
  round761IntroducesNormOrAbsoluteValue ≡ false
round761IntroducesNormOrAbsoluteValueIsFalse = refl

round761ClayPromotionIsFalse :
  round761ClayPromotion ≡ false
round761ClayPromotionIsFalse = refl

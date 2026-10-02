{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650NestedSwapPairProductRuleRound762Exact where

------------------------------------------------------------------------
-- ROUND762 / SWAP-PAIRED R694 NESTED CELL = FOUR COPIES OF THE
--            SWAP-PAIRED R230 PRODUCT-RULE CELL
--
-- R694:
--
--   Nested(beta) = 4 * Comm(beta)
--
-- in literal division-free four-copy form.
--
-- R761:
--
--   Comm(beta)+Comm(swap beta)
--     = Product(beta)+Product(swap beta).
--
-- Therefore exactly
--
--   Nested(beta)+Nested(swap beta)
--     = FourCopies(Product(beta)+Product(swap beta)).
--
-- This is still vector algebra before the coherent-work consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650CommutatorSwapPairProductRuleRound761Exact as R761

fourCopies :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F
fourCopies value =
  C3.complex3Add
    (C3.complex3Add value value)
    (C3.complex3Add value value)

fourCopiesPairDistributes :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Complex3 F) →
  C3.complex3Add (fourCopies left) (fourCopies right)
  ≡ fourCopies (C3.complex3Add left right)
fourCopiesPairDistributes {F = F}
    (C3.complex3 lx ly lz)
    (C3.complex3 rx ry rz) =
  Field.complex3Ext
    (R.solve 2
      (λ l r →
        (((l R.⊕ l) R.⊕ (l R.⊕ l))
          R.⊕ ((r R.⊕ r) R.⊕ (r R.⊕ r)))
        R.⊜
        (((l R.⊕ r) R.⊕ (l R.⊕ r))
          R.⊕ ((l R.⊕ r) R.⊕ (l R.⊕ r))))
      refl lx rx)
    (R.solve 2
      (λ l r →
        (((l R.⊕ l) R.⊕ (l R.⊕ l))
          R.⊕ ((r R.⊕ r) R.⊕ (r R.⊕ r)))
        R.⊜
        (((l R.⊕ r) R.⊕ (l R.⊕ r))
          R.⊕ ((l R.⊕ r) R.⊕ (l R.⊕ r))))
      refl ly ry)
    (R.solve 2
      (λ l r →
        (((l R.⊕ l) R.⊕ (l R.⊕ l))
          R.⊕ ((r R.⊕ r) R.⊕ (r R.⊕ r)))
        R.⊜
        (((l R.⊕ r) R.⊕ (l R.⊕ r))
          R.⊕ ((l R.⊕ r) R.⊕ (l R.⊕ r))))
      refl lz rz)
  where
  module R = Ring.Solver F

module NestedSwapPair
    {r} {F : C3.RealField r}
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module N =
    R694.NestedExpansion
      physicalSystem S L H velocityTransverse

  pairedProductRuleCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  pairedProductRuleCell beta =
    C3.complex3Add
      (R230.productRuleForcingCell
        S N.Base.velocity N.Base.forcing beta)
      (R230.productRuleForcingCell
        S N.Base.velocity N.Base.forcing (Symmetry.swapTriad beta))

  nestedSwapPairIsFourProductRuleCopies :
    (beta : Physical.PhysicalTriadIncidence) →
    C3.complex3Add
      (N.nestedCell beta)
      (N.nestedCell (Symmetry.swapTriad beta))
    ≡ fourCopies (pairedProductRuleCell beta)
  nestedSwapPairIsFourProductRuleCopies beta =
    let
      comm = N.Base.commutatorCell beta
      commSwap = N.Base.commutatorCell (Symmetry.swapTriad beta)
      pairComm = C3.complex3Add comm commSwap
    in
    trans
      (cong₂ C3.complex3Add
        (N.nestedCellIsFourCommutatorCopies beta)
        (N.nestedCellIsFourCommutatorCopies
          (Symmetry.swapTriad beta)))
      (trans
        (fourCopiesPairDistributes comm commSwap)
        (cong fourCopies
          (R761.commutatorSwapPairIsProductRuleSwapPair
            S N.Base.velocity N.Base.forcing beta)))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round762NestedSwapPairIsFourProductRuleCopies : Bool
round762NestedSwapPairIsFourProductRuleCopies = true

round762StillBeforeCoherentWorkConsumer : Bool
round762StillBeforeCoherentWorkConsumer = true

round762IntroducesEstimate : Bool
round762IntroducesEstimate = false

round762IntroducesNormOrAbsoluteValue : Bool
round762IntroducesNormOrAbsoluteValue = false

round762ClayPromotion : Bool
round762ClayPromotion = false

round762NestedSwapPairIsFourProductRuleCopiesIsTrue :
  round762NestedSwapPairIsFourProductRuleCopies ≡ true
round762NestedSwapPairIsFourProductRuleCopiesIsTrue = refl

round762StillBeforeCoherentWorkConsumerIsTrue :
  round762StillBeforeCoherentWorkConsumer ≡ true
round762StillBeforeCoherentWorkConsumerIsTrue = refl

round762IntroducesEstimateIsFalse :
  round762IntroducesEstimate ≡ false
round762IntroducesEstimateIsFalse = refl

round762IntroducesNormOrAbsoluteValueIsFalse :
  round762IntroducesNormOrAbsoluteValue ≡ false
round762IntroducesNormOrAbsoluteValueIsFalse = refl

round762ClayPromotionIsFalse :
  round762ClayPromotion ≡ false
round762ClayPromotionIsFalse = refl

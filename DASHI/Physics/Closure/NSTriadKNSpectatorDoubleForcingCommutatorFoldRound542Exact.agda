module DASHI.Physics.Closure.NSTriadKNSpectatorDoubleForcingCommutatorFoldRound542Exact where

------------------------------------------------------------------------
-- ROUND542 / SPECTATOR-WEIGHTED R388 DOUBLE FORCING -> FOUR R294 FOLDS
--
-- R388 gives pointwise
--
--   Gdouble(tau) = 2 F(tau) + 2 F(swap tau),
--
-- where F is the literal R230 product-rule forcing cell.  For any R294
-- swap-invariant weight W, the complete physical output fibre is itself
-- swap-permuted (R224).  Hence after folding the swapped half equals the
-- unswapped half exactly:
--
--   fold [ W Gdouble ] = P + P + P + P,
--
-- where P = fold [W F].  R294 then replaces P by the weighted mixed-commutator
-- fold before norms.  No Laplace factorization or estimate is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNDoubleMixedAsSwapPairedPlusMinusRound387Exact as R387
import DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact as R388

module Fold
    {r} {F : C3.RealField r}
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (W : R294.SwapInvariantCellWeight F) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem

  module D = R388.PhysicalDoubleMixed physicalSystem S

  system : Audit.FiniteComplex3GalerkinSystem F E I
  system = Field30.finiteSystem physicalSystem

  velocity = Audit.velocity system
  forcing = Audit.projectedNonlinearity system

  product : Physical.PhysicalTriadIncidence → C3.Complex3 F
  product = R294.weightedProductRuleCell {E = E} {I = I} W S velocity forcing

  commutator : Physical.PhysicalTriadIncidence → C3.Complex3 F
  commutator = R294.weightedCommutatorCell {E = E} {I = I} W S velocity forcing

  weightedDouble : Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedDouble tau =
    C3.complex3Scale (R294.weight W tau) (D.doubleForcing tau)

  weightedSwapProduct : Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedSwapProduct tau =
    C3.complex3Scale (R294.weight W tau)
      (D.Pair.mixedCellForcing (Symmetry.swapTriad tau))

  weightedSwapProductIsProductAfterSwap :
    (tau : Physical.PhysicalTriadIncidence) →
    weightedSwapProduct tau ≡ product (Symmetry.swapTriad tau)
  weightedSwapProductIsProductAfterSwap tau =
    cong
      (λ selectedWeight →
        C3.complex3Scale selectedWeight
          (D.Pair.mixedCellForcing (Symmetry.swapTriad tau)))
      (sym (R294.swapInvariant W tau))

  weightedDoublePointwise :
    (tau : Physical.PhysicalTriadIncidence) →
    weightedDouble tau
    ≡ C3.complex3Add
        (C3.complex3Add (product tau) (product tau))
        (C3.complex3Add
          (weightedSwapProduct tau) (weightedSwapProduct tau))
  weightedDoublePointwise tau =
    let
      w = R294.weight W tau
      f = D.Pair.mixedCellForcing tau
      fs = D.Pair.mixedCellForcing (Symmetry.swapTriad tau)
    in
    trans
      (R73.complex3ScaleAdd w (R387.doublePlus f) (R387.doublePlus fs))
      (cong₂ C3.complex3Add
        (R73.complex3ScaleAdd w f f)
        (R73.complex3ScaleAdd w fs fs))

  foldPointwise :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector weightedDouble items
    ≡ R224.foldVector
        (λ tau → C3.complex3Add
          (C3.complex3Add (product tau) (product tau))
          (C3.complex3Add
            (weightedSwapProduct tau) (weightedSwapProduct tau))) items
  foldPointwise [] = refl
  foldPointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (weightedDoublePointwise tau)
      (foldPointwise rest)

  foldSwapProductIsFoldProduct :
    (cutoff : Nat) (output : Z3.FourierMode) →
    R224.foldVector weightedSwapProduct
      (Output.physicalOutputFiber cutoff output)
    ≡ R224.foldVector product
      (Output.physicalOutputFiber cutoff output)
  foldSwapProductIsFoldProduct cutoff output =
    trans
      (foldSwapPointwise (Output.physicalOutputFiber cutoff output))
      (trans
        (sym
          (R224.foldMap product Symmetry.swapTriad
            (Output.physicalOutputFiber cutoff output)))
        (R224.foldPermutationInvariant product
          (R224.swapOutputFibrePermutation cutoff output)))
    where
    foldSwapPointwise :
      (items : List Physical.PhysicalTriadIncidence) →
      R224.foldVector weightedSwapProduct items
      ≡ R224.foldVector (λ tau → product (Symmetry.swapTriad tau)) items
    foldSwapPointwise [] = refl
    foldSwapPointwise (tau ∷ rest) =
      cong₂ C3.complex3Add
        (weightedSwapProductIsProductAfterSwap tau)
        (foldSwapPointwise rest)

  foldFourComponents :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector
      (λ tau → C3.complex3Add
        (C3.complex3Add (product tau) (product tau))
        (C3.complex3Add
          (weightedSwapProduct tau) (weightedSwapProduct tau))) items
    ≡ C3.complex3Add
        (C3.complex3Add
          (R224.foldVector product items)
          (R224.foldVector product items))
        (C3.complex3Add
          (R224.foldVector weightedSwapProduct items)
          (R224.foldVector weightedSwapProduct items))
  foldFourComponents items =
    trans
      (R230.foldAdd
        (λ tau → C3.complex3Add (product tau) (product tau))
        (λ tau → C3.complex3Add
          (weightedSwapProduct tau) (weightedSwapProduct tau))
        items)
      (cong₂ C3.complex3Add
        (R230.foldAdd product product items)
        (R230.foldAdd weightedSwapProduct weightedSwapProduct items))

  fixedOutputWeightedDoubleIsFourProductFolds :
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output
        P = R224.foldVector product items
    in
    R224.foldVector weightedDouble items
    ≡ C3.complex3Add (C3.complex3Add P P) (C3.complex3Add P P)
  fixedOutputWeightedDoubleIsFourProductFolds output =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      P = R224.foldVector product items
    in
    trans
      (foldPointwise items)
      (trans
        (foldFourComponents items)
        (cong
          (λ Sfold → C3.complex3Add (C3.complex3Add P P)
            (C3.complex3Add Sfold Sfold))
          (foldSwapProductIsFoldProduct (Audit.cutoff system) output)))

  fixedOutputWeightedDoubleIsFourCommutatorFolds :
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output
        C = R224.foldVector commutator items
    in
    R224.foldVector weightedDouble items
    ≡ C3.complex3Add (C3.complex3Add C C) (C3.complex3Add C C)
  fixedOutputWeightedDoubleIsFourCommutatorFolds output =
    let
      productToCommutator =
        R294.fixedOutputWeightedProductRuleIsCommutator
          {E = E} {I = I}
          W S velocity forcing (Audit.cutoff system) output
    in
    trans
      (fixedOutputWeightedDoubleIsFourProductFolds output)
      (cong
        (λ P → C3.complex3Add (C3.complex3Add P P)
          (C3.complex3Add P P))
        productToCommutator)

round542WeightedDoubleForcingFoldNormalizationClosed : Bool
round542WeightedDoubleForcingFoldNormalizationClosed = true

round542R294CommutatorFoldWeldClosed : Bool
round542R294CommutatorFoldWeldClosed = true

round542LaplaceFactorizationRequired : Bool
round542LaplaceFactorizationRequired = false

round542SignedSpacetimeEstimateClosed : Bool
round542SignedSpacetimeEstimateClosed = false

round542ClayPromotion : Bool
round542ClayPromotion = false

round542R294CommutatorFoldWeldClosedIsTrue :
  round542R294CommutatorFoldWeldClosed ≡ true
round542R294CommutatorFoldWeldClosedIsTrue = refl

round542LaplaceFactorizationRequiredIsFalse :
  round542LaplaceFactorizationRequired ≡ false
round542LaplaceFactorizationRequiredIsFalse = refl

round542ClayPromotionIsFalse : round542ClayPromotion ≡ false
round542ClayPromotionIsFalse = refl

module DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact where

------------------------------------------------------------------------
-- ROUND294 / SWAP-INVARIANT WEIGHTS PRESERVE THE R230 COMMUTATOR COLLAPSE
--
-- The R290 resolvent suggests one-cell factors such as exp(-s lambda_pq), with
-- lambda_pq = nu(|p|^2+|q|^2).  The decisive structural property for the R230
-- p/q reindexing is not the exponential formula itself but simply
--
--   w(swap tau) = w(tau).
--
-- This file proves the generic finite theorem: any scalar weight with that
-- exact symmetry may be inserted into the complete fixed-output product-rule
-- forcing and the same swap/antisymmetry still collapses it to the weighted
-- mixed commutator before absolute values.
--
-- Hence the future heat/resolvent realization does not destroy the strongest
-- signed algebra already present in R230.
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
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230

record SwapInvariantCellWeight
    {r} (F : C3.RealField r) : Set r where
  field
    weight : Physical.PhysicalTriadIncidence → C3.Complex F
    swapInvariant :
      (tau : Physical.PhysicalTriadIncidence) →
      weight (Symmetry.swapTriad tau) ≡ weight tau

open SwapInvariantCellWeight public

weightedCell :
  ∀ {r} {F : C3.RealField r} →
  SwapInvariantCellWeight F →
  (Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedCell W cell tau = C3.complex3Scale (weight W tau) (cell tau)

weightedFirst :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedFirst W S velocity forcing =
  weightedCell W (R230.plusForceMinusVelocity S velocity forcing)

weightedSecond :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedSecond W S velocity forcing =
  weightedCell W (R230.plusVelocityMinusForce S velocity forcing)

weightedOpposite :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedOpposite W S velocity forcing =
  weightedCell W (R230.minusForcePlusVelocity S velocity forcing)

weightedProductRuleCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedProductRuleCell W S velocity forcing tau =
  C3.complex3Add
    (weightedFirst W S velocity forcing tau)
    (weightedSecond W S velocity forcing tau)

weightedCommutatorCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedCommutatorCell W S velocity forcing tau =
  C3.complex3Subtract
    (weightedFirst W S velocity forcing tau)
    (weightedOpposite W S velocity forcing tau)

weightedSecondAfterSwapIsNegativeOpposite :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  weightedSecond W S velocity forcing (Symmetry.swapTriad tau)
  ≡ C3.complex3Negate (weightedOpposite W S velocity forcing tau)
weightedSecondAfterSwapIsNegativeOpposite W S velocity forcing tau =
  trans
    (cong
      (λ selectedWeight →
        C3.complex3Scale selectedWeight
          (R230.plusVelocityMinusForce S velocity forcing
            (Symmetry.swapTriad tau)))
      (swapInvariant W tau))
    (trans
      (cong (C3.complex3Scale (weight W tau))
        (R230.secondForcingAfterSwapIsNegativeMinusPlus
          S velocity forcing tau))
      (R73.complex3ScaleNegate
        (weight W tau)
        (R230.minusForcePlusVelocity S velocity forcing tau)))

fixedOutputWeightedSecondReindexesNegative :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (weightedSecond W S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
  ≡
  R224.foldVector
    (λ tau → C3.complex3Negate
      (weightedOpposite W S velocity forcing tau))
    (Output.physicalOutputFiber cutoff output)
fixedOutputWeightedSecondReindexesNegative W S velocity forcing cutoff output =
  trans
    (sym
      (R224.foldPermutationInvariant
        (weightedSecond W S velocity forcing)
        (R224.swapOutputFibrePermutation cutoff output)))
    (trans
      (R224.foldMap
        (weightedSecond W S velocity forcing)
        Symmetry.swapTriad
        (Output.physicalOutputFiber cutoff output))
      (pointwise (Output.physicalOutputFiber cutoff output)))
  where
  pointwise :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector
      (λ tau → weightedSecond W S velocity forcing
        (Symmetry.swapTriad tau)) items
    ≡
    R224.foldVector
      (λ tau → C3.complex3Negate
        (weightedOpposite W S velocity forcing tau)) items
  pointwise [] = refl
  pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (weightedSecondAfterSwapIsNegativeOpposite W S velocity forcing tau)
      (pointwise rest)

fixedOutputWeightedProductRuleIsCommutator :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (weightedProductRuleCell W S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
  ≡
  R224.foldVector (weightedCommutatorCell W S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
fixedOutputWeightedProductRuleIsCommutator
    W S velocity forcing cutoff output =
  let
    fibre = Output.physicalOutputFiber cutoff output
    first = weightedFirst W S velocity forcing
    second = weightedSecond W S velocity forcing
    opposite = weightedOpposite W S velocity forcing
  in
  trans
    (R230.foldAdd first second fibre)
    (trans
      (cong₂ C3.complex3Add refl
        (fixedOutputWeightedSecondReindexesNegative
          W S velocity forcing cutoff output))
      (sym (R230.foldSubtract first opposite fibre)))

round294GenericSwapInvariantWeightedCollapseClosed : Bool
round294GenericSwapInvariantWeightedCollapseClosed = true

round294HeatResolventWeightInstantiated : Bool
round294HeatResolventWeightInstantiated = false

round294WeightedNonlinearCommutatorPaid : Bool
round294WeightedNonlinearCommutatorPaid = false

round294SignedIntegratedGramBudgetClosed : Bool
round294SignedIntegratedGramBudgetClosed = false

round294PackageAClosed : Bool
round294PackageAClosed = false

round294ClayPromotion : Bool
round294ClayPromotion = false

round294GenericSwapInvariantWeightedCollapseClosedIsTrue :
  round294GenericSwapInvariantWeightedCollapseClosed ≡ true
round294GenericSwapInvariantWeightedCollapseClosedIsTrue = refl

module DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact where

------------------------------------------------------------------------
-- ROUND230 / PRODUCT-RULE FORCING COLLAPSES TO ONE MIXED COMMUTATOR
--
-- Let G be any modal forcing and u the velocity.  The tangent of the
-- mixed-helicity product u_p+ x u_q- contains
--
--   G_p+ x u_q- + u_p+ x G_q-.
--
-- On the complete fixed-output fibre, the second term reindexes under
-- p <-> q and cross-product antisymmetry to
--
--   - G_p- x u_q+.
--
-- Hence the complete forcing sum is exactly
--
--   sum [ G_p+ x u_q- - G_p- x u_q+ ].
--
-- This is another signed collapse before absolute values, but it is NOT zero.
-- For the physical NS choice G = projected nonlinearity it is a genuine cubic
-- mixed-helicity forcing and therefore the next analytic object to pay.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeSelectedSwapAntisymmetryRound118Exact as R118
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224

plusForceMinusVelocity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
plusForceMinusVelocity {E = E} {I = I} S velocity forcing tau =
  Cross.complex3Cross
    (Helical.helicalProjectorPlus E I S
      (Physical.p tau) (forcing (Physical.p tau)))
    (Helical.helicalProjectorMinus E I S
      (Physical.q tau) (velocity (Physical.q tau)))

plusVelocityMinusForce :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
plusVelocityMinusForce {E = E} {I = I} S velocity forcing tau =
  Cross.complex3Cross
    (Helical.helicalProjectorPlus E I S
      (Physical.p tau) (velocity (Physical.p tau)))
    (Helical.helicalProjectorMinus E I S
      (Physical.q tau) (forcing (Physical.q tau)))

minusForcePlusVelocity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
minusForcePlusVelocity {E = E} {I = I} S velocity forcing tau =
  Cross.complex3Cross
    (Helical.helicalProjectorMinus E I S
      (Physical.p tau) (forcing (Physical.p tau)))
    (Helical.helicalProjectorPlus E I S
      (Physical.q tau) (velocity (Physical.q tau)))

secondForcingAfterSwapIsNegativeMinusPlus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  plusVelocityMinusForce S velocity forcing (Symmetry.swapTriad tau)
  ≡ C3.complex3Negate (minusForcePlusVelocity S velocity forcing tau)
secondForcingAfterSwapIsNegativeMinusPlus S velocity forcing tau =
  R118.crossAnticommutative
    (Helical.helicalProjectorMinus _ _ S
      (Physical.p tau) (forcing (Physical.p tau)))
    (Helical.helicalProjectorPlus _ _ S
      (Physical.q tau) (velocity (Physical.q tau)))

fixedOutputSecondForcingReindexesNegative :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (plusVelocityMinusForce S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
  ≡
  R224.foldVector
    (λ tau → C3.complex3Negate
      (minusForcePlusVelocity S velocity forcing tau))
    (Output.physicalOutputFiber cutoff output)
fixedOutputSecondForcingReindexesNegative S velocity forcing cutoff output =
  trans
    (sym
      (R224.foldPermutationInvariant
        (plusVelocityMinusForce S velocity forcing)
        (R224.swapOutputFibrePermutation cutoff output)))
    (trans
      (R224.foldMap
        (plusVelocityMinusForce S velocity forcing)
        Symmetry.swapTriad
        (Output.physicalOutputFiber cutoff output))
      (pointwise (Output.physicalOutputFiber cutoff output)))
  where
  pointwise :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector
      (λ tau → plusVelocityMinusForce S velocity forcing
        (Symmetry.swapTriad tau)) items
    ≡
    R224.foldVector
      (λ tau → C3.complex3Negate
        (minusForcePlusVelocity S velocity forcing tau)) items
  pointwise [] = refl
  pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (secondForcingAfterSwapIsNegativeMinusPlus S velocity forcing tau)
      (pointwise rest)

forcingCommutatorCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
forcingCommutatorCell S velocity forcing tau =
  C3.complex3Subtract
    (plusForceMinusVelocity S velocity forcing tau)
    (minusForcePlusVelocity S velocity forcing tau)

productRuleForcingCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
productRuleForcingCell S velocity forcing tau =
  C3.complex3Add
    (plusForceMinusVelocity S velocity forcing tau)
    (plusVelocityMinusForce S velocity forcing tau)

complex3AddZeroLeft :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complex3Add (C3.complex3Zero F) v ≡ v
complex3AddZeroLeft (C3.complex3 x y z) =
  Algebra.complex3Ext
    (Algebra.complexAddZeroLeft x)
    (Algebra.complexAddZeroLeft y)
    (Algebra.complexAddZeroLeft z)

complex3Shuffle :
  ∀ {r} {F : C3.RealField r}
    (a b c d : C3.Complex3 F) →
  C3.complex3Add (C3.complex3Add a b) (C3.complex3Add c d)
  ≡ C3.complex3Add (C3.complex3Add a c) (C3.complex3Add b d)
complex3Shuffle {F = F}
    (C3.complex3 ax ay az) (C3.complex3 bx by bz)
    (C3.complex3 cx cy cz) (C3.complex3 dx dy dz) =
  Algebra.complex3Ext
    (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl ax bx cx dx)
    (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl ay by cy dy)
    (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl az bz cz dz)
  where module R = Ring.Solver F

foldAdd :
  ∀ {r} {F : C3.RealField r}
    (left right : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (λ tau → C3.complex3Add (left tau) (right tau)) items
  ≡ C3.complex3Add (R224.foldVector left items) (R224.foldVector right items)
foldAdd {F = F} left right [] = sym (complex3AddZeroLeft (C3.complex3Zero F))
foldAdd left right (tau ∷ rest) =
  trans
    (cong₂ C3.complex3Add refl (foldAdd left right rest))
    (complex3Shuffle
      (left tau) (right tau)
      (R224.foldVector left rest) (R224.foldVector right rest))

foldSubtract :
  ∀ {r} {F : C3.RealField r}
    (left right : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (λ tau → C3.complex3Subtract (left tau) (right tau)) items
  ≡ C3.complex3Add
      (R224.foldVector left items)
      (R224.foldVector (λ tau → C3.complex3Negate (right tau)) items)
foldSubtract left right items = foldAdd left (λ tau → C3.complex3Negate (right tau)) items

fixedOutputProductRuleForcingIsMixedCommutator :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (productRuleForcingCell S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
  ≡
  R224.foldVector (forcingCommutatorCell S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
fixedOutputProductRuleForcingIsMixedCommutator
    S velocity forcing cutoff output =
  let fibre = Output.physicalOutputFiber cutoff output
      first = plusForceMinusVelocity S velocity forcing
      second = plusVelocityMinusForce S velocity forcing
      opposite = minusForcePlusVelocity S velocity forcing
  in
  trans
    (foldAdd first second fibre)
    (trans
      (cong₂ C3.complex3Add refl
        (fixedOutputSecondForcingReindexesNegative
          S velocity forcing cutoff output))
      (sym (foldSubtract first opposite fibre)))

round230FixedOutputProductRuleForcingCollapseClosed : Bool
round230FixedOutputProductRuleForcingCollapseClosed = true

round230ProductRuleForcingCancelsCompletely : Bool
round230ProductRuleForcingCancelsCompletely = false

round230PhysicalNSCubicMixedForcingPaid : Bool
round230PhysicalNSCubicMixedForcingPaid = false

round230PackageAClosed : Bool
round230PackageAClosed = false

round230ClayPromotion : Bool
round230ClayPromotion = false

round230FixedOutputProductRuleForcingCollapseClosedIsTrue :
  round230FixedOutputProductRuleForcingCollapseClosed ≡ true
round230FixedOutputProductRuleForcingCollapseClosedIsTrue = refl

round230ProductRuleForcingCancelsCompletelyIsFalse :
  round230ProductRuleForcingCancelsCompletely ≡ false
round230ProductRuleForcingCancelsCompletelyIsFalse = refl

round230PhysicalNSCubicMixedForcingPaidIsFalse :
  round230PhysicalNSCubicMixedForcingPaid ≡ false
round230PhysicalNSCubicMixedForcingPaidIsFalse = refl

round230PackageAClosedIsFalse : round230PackageAClosed ≡ false
round230PackageAClosedIsFalse = refl

round230ClayPromotionIsFalse : round230ClayPromotion ≡ false
round230ClayPromotionIsFalse = refl

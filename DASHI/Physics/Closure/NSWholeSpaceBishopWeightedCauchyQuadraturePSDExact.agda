module DASHI.Physics.Closure.NSWholeSpaceBishopWeightedCauchyQuadraturePSDExact where

------------------------------------------------------------------------
-- A / WEIGHTED FINITE CAUCHY QUADRATURE PSD
--
-- A finite quadrature approximation of a double Cauchy/Hermitian integral has
-- atoms
--
--   w_i w_j K(r_i,r_j) Re <v_i,v_j>.
--
-- Do NOT prove a second weighted PSD theorem.  Absorb w_i into v_i:
--
--   v_i^w = w_i v_i.
--
-- Then the weighted quadrature is definitionally the already-proved finite
-- Bishop C^3 Cauchy form on the scaled vectors.  Since that theorem permits
-- arbitrary real vector coordinates, quadrature weights need not be positive
-- for this algebraic PSD fact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (map)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output
import DASHI.Physics.Closure.NSWholeSpaceBishopComplex3CauchyPSDExact as ComplexPSD

record WeightedPositiveRateComplex3Cell : Set where
  constructor weighted-positive-rate-complex3-cell
  field
    rate : BishopReal.ℝ
    value : Physical.BishopComplex3
    weight : BishopReal.ℝ
    ratePositive : BishopReal._<_ BishopReal.0ℝ rate

open WeightedPositiveRateComplex3Cell public

weightedValue :
  WeightedPositiveRateComplex3Cell →
  Physical.BishopComplex3
weightedValue cell =
  Physical.bishop-complex3
    (Output.realScaleComplex
      (weight cell)
      (Physical.cx (value cell)))
    (Output.realScaleComplex
      (weight cell)
      (Physical.cy (value cell)))
    (Output.realScaleComplex
      (weight cell)
      (Physical.cz (value cell)))

toPositiveRateComplex3Cell :
  WeightedPositiveRateComplex3Cell →
  ComplexPSD.PositiveRateComplex3Cell
toPositiveRateComplex3Cell cell =
  ComplexPSD.positive-rate-complex3-cell
    (rate cell)
    (weightedValue cell)
    (ratePositive cell)

weightedCells :
  List WeightedPositiveRateComplex3Cell →
  List ComplexPSD.PositiveRateComplex3Cell
weightedCells = map toPositiveRateComplex3Cell

weightedHermitianCauchyForm :
  List WeightedPositiveRateComplex3Cell →
  BishopReal.ℝ
weightedHermitianCauchyForm cells =
  ComplexPSD.hermitianCauchyForm (weightedCells cells)

weightedHermitianCauchyFormNonnegative :
  (cells : List WeightedPositiveRateComplex3Cell) →
  BishopReal.NonNegative (weightedHermitianCauchyForm cells)
weightedHermitianCauchyFormNonnegative cells =
  ComplexPSD.hermitianCauchyFormNonnegative
    (weightedCells cells)

weightedFiniteQuadraturePSDClosed : Bool
weightedFiniteQuadraturePSDClosed = true

quadratureWeightPositivityRequiredForPSD : Bool
quadratureWeightPositivityRequiredForPSD = false

newKernelPSDArgumentRequired : Bool
newKernelPSDArgumentRequired = false

continuousLimitTakenHere : Bool
continuousLimitTakenHere = false

clayPromotion : Bool
clayPromotion = false

weightedFiniteQuadraturePSDClosedIsTrue :
  weightedFiniteQuadraturePSDClosed ≡ true
weightedFiniteQuadraturePSDClosedIsTrue = refl

quadratureWeightPositivityRequiredForPSDIsFalse :
  quadratureWeightPositivityRequiredForPSD ≡ false
quadratureWeightPositivityRequiredForPSDIsFalse = refl

newKernelPSDArgumentRequiredIsFalse :
  newKernelPSDArgumentRequired ≡ false
newKernelPSDArgumentRequiredIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

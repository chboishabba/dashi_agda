module DASHI.Physics.YangMills.BalabanClayGate4CMP109Equation012GroupAverageAdapterExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageAxiomsExact as Average

------------------------------------------------------------------------
-- Equation-(0.12) adapter from the source-exact group average.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Equation (0.11) defines U(y,x) by applying the analytic group average M to
-- the finite set of contour holonomies.  Equation (0.12) must therefore not be
-- instantiated with unrelated source and target contour values.  The adapter
-- below constructs both values definitionally from one CMP109 group-average
-- witness and the selected finite path families.
------------------------------------------------------------------------

record Equation012GroupAverageInputs
    (Field CoarseBond FineSite Path Group Lie Scalar : Set) : Set₁ where
  field
    groupAverage : Average.CMP109GroupAverageAxioms Group Lie Scalar

    blockSites : CoarseBond → List FineSite
    blockWeight : CoarseBond → Scalar

    sourcePaths targetReversePaths :
      CoarseBond → FineSite → List Path

    sourcePathHolonomy :
      Field → CoarseBond → FineSite → Path → Group
    targetReversePathHolonomy :
      Field → CoarseBond → FineSite → Path → Group

    crossingValue : Field → CoarseBond → FineSite → Group
    reversedCoarseBondValue : Field → CoarseBond → Group
    coarseBondValue : Field → CoarseBond → Group

    antiHermitianLogCoordinate : Group → Lie
    outerExponential : Lie → Group

open Equation012GroupAverageInputs public

sourceContourAverage :
  ∀ {Field CoarseBond FineSite Path Group Lie Scalar} →
  Equation012GroupAverageInputs
    Field CoarseBond FineSite Path Group Lie Scalar →
  Field → CoarseBond → FineSite → Group
sourceContourAverage inputs field coarse fine =
  Average.average (groupAverage inputs)
    (Average.mapList
      (sourcePathHolonomy inputs field coarse fine)
      (sourcePaths inputs coarse fine))

targetReverseContourAverage :
  ∀ {Field CoarseBond FineSite Path Group Lie Scalar} →
  Equation012GroupAverageInputs
    Field CoarseBond FineSite Path Group Lie Scalar →
  Field → CoarseBond → FineSite → Group
targetReverseContourAverage inputs field coarse fine =
  Average.average (groupAverage inputs)
    (Average.mapList
      (targetReversePathHolonomy inputs field coarse fine)
      (targetReversePaths inputs coarse fine))

asPrintedEquation012Data :
  ∀ {Field CoarseBond FineSite Path Group Lie Scalar} →
  Equation012GroupAverageInputs
    Field CoarseBond FineSite Path Group Lie Scalar →
  Printed.PrintedCMP109Equation012Data
    Field CoarseBond FineSite Group Lie Scalar
asPrintedEquation012Data inputs = record
  { Printed.PrintedCMP109Equation012Data.blockSites = blockSites inputs
  ; Printed.PrintedCMP109Equation012Data.blockWeight = blockWeight inputs
  ; Printed.PrintedCMP109Equation012Data.zeroLie =
      Average.zeroLie (groupAverage inputs)
  ; Printed.PrintedCMP109Equation012Data.addLie =
      Average.addLie (groupAverage inputs)
  ; Printed.PrintedCMP109Equation012Data.scaleLie =
      Average.scaleLie (groupAverage inputs)
  ; Printed.PrintedCMP109Equation012Data.multiplyGroup =
      Average.multiply (groupAverage inputs)
  ; Printed.PrintedCMP109Equation012Data.sourceAveragedContour =
      sourceContourAverage inputs
  ; Printed.PrintedCMP109Equation012Data.crossingValue = crossingValue inputs
  ; Printed.PrintedCMP109Equation012Data.targetAveragedContourReverse =
      targetReverseContourAverage inputs
  ; Printed.PrintedCMP109Equation012Data.reversedCoarseBondValue =
      reversedCoarseBondValue inputs
  ; Printed.PrintedCMP109Equation012Data.coarseBondValue =
      coarseBondValue inputs
  ; Printed.PrintedCMP109Equation012Data.antiHermitianLogCoordinate =
      antiHermitianLogCoordinate inputs
  ; Printed.PrintedCMP109Equation012Data.outerExponential =
      outerExponential inputs
  }

sourceContourIsEquation011Average :
  ∀ {Field CoarseBond FineSite Path Group Lie Scalar}
    (inputs : Equation012GroupAverageInputs
      Field CoarseBond FineSite Path Group Lie Scalar)
    field coarse fine →
  Printed.sourceAveragedContour (asPrintedEquation012Data inputs)
    field coarse fine
  ≡ Average.average (groupAverage inputs)
      (Average.mapList
        (sourcePathHolonomy inputs field coarse fine)
        (sourcePaths inputs coarse fine))
sourceContourIsEquation011Average inputs field coarse fine = refl

targetContourIsEquation011Average :
  ∀ {Field CoarseBond FineSite Path Group Lie Scalar}
    (inputs : Equation012GroupAverageInputs
      Field CoarseBond FineSite Path Group Lie Scalar)
    field coarse fine →
  Printed.targetAveragedContourReverse (asPrintedEquation012Data inputs)
    field coarse fine
  ≡ Average.average (groupAverage inputs)
      (Average.mapList
        (targetReversePathHolonomy inputs field coarse fine)
        (targetReversePaths inputs coarse fine))
targetContourIsEquation011Average inputs field coarse fine = refl

cmp109Equation011SourceContourInstantiationLevel : ProofLevel
cmp109Equation011SourceContourInstantiationLevel = computed

cmp109Equation011TargetContourInstantiationLevel : ProofLevel
cmp109Equation011TargetContourInstantiationLevel = computed

cmp109Equation012GroupAverageAdapterLevel : ProofLevel
cmp109Equation012GroupAverageAdapterLevel = machineChecked

physicalCMP109FiniteContourFamilyInputsLevel : ProofLevel
physicalCMP109FiniteContourFamilyInputsLevel = conditional

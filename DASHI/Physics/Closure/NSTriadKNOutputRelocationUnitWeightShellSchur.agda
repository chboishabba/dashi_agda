module DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightShellSchur where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Jean-Michel Bony; Hajer
-- Bahouri; Jean-Yves Chemin; Raphael Danchin; DASHI repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators"; "Calcul
-- symbolique et propagation des singularites pour les equations aux derivees
-- partielles non lineaires"; "Fourier Analysis and Nonlinear Partial
-- Differential Equations"; and "Three unit-weight shell Schur bounds for
-- output relocation".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Annales
-- scientifiques de l'Ecole Normale Superieure 14 (1981); Springer, 2011;
-- DASHI formal development, 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.24033/asens.1404;
-- 10.1007/978-3-642-16830-7; the repository shell theorem has no DOI.
-- Uses: Grafakos--Torres Theorem 1(c), the proved unit-weight symbolic Check A,
-- and the canonical positive shell kernel with exact mass bound 128/93.
-- Relationship: closes the output, first-partial-adjoint and
-- second-partial-adjoint conditions at the normalized shell-majorant level.
-- Mapping the literal Navier--Stokes coefficient to this normalized kernel and
-- constructing the full operator carrier remain separate bridge obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresThreeFunctionSchurProgram as GT
import DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightCheckA as Unit
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

data SchurOrientation : Set where
  outputCondition firstAdjointCondition secondAdjointCondition : SchurOrientation

orientationKernel : SchurOrientation → Nat → Nat → ℚ
orientationKernel outputCondition = Majorant.canonicalKernel
orientationKernel firstAdjointCondition = Majorant.canonicalKernel
orientationKernel secondAdjointCondition = Majorant.canonicalKernel

orientationCutoffSum : SchurOrientation → Nat → Nat → ℚ
orientationCutoffSum orientation lowCutoff gapCutoff =
  Majorant.rectangleSum
    (orientationKernel orientation) lowCutoff gapCutoff

orientationCutoffBound : ∀ orientation lowCutoff gapCutoff →
  orientationCutoffSum orientation lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
orientationCutoffBound outputCondition =
  Majorant.canonicalKernelCutoffUniformBound
orientationCutoffBound firstAdjointCondition =
  Majorant.canonicalKernelCutoffUniformBound
orientationCutoffBound secondAdjointCondition =
  Majorant.canonicalKernelCutoffUniformBound

outputUnitWeightShellSchurBound : ∀ lowCutoff gapCutoff →
  orientationCutoffSum outputCondition lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
outputUnitWeightShellSchurBound =
  orientationCutoffBound outputCondition

firstAdjointUnitWeightShellSchurBound : ∀ lowCutoff gapCutoff →
  orientationCutoffSum firstAdjointCondition lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
firstAdjointUnitWeightShellSchurBound =
  orientationCutoffBound firstAdjointCondition

secondAdjointUnitWeightShellSchurBound : ∀ lowCutoff gapCutoff →
  orientationCutoffSum secondAdjointCondition lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
secondAdjointUnitWeightShellSchurBound =
  orientationCutoffBound secondAdjointCondition

record ThreeUnitWeightShellSchurReceipt : Set where
  constructor receipt
  field
    threeFunctionFrameworkPrimary :
      GT.threeFunctionSchurPrimaryFramework ≡ true
    unitWeightCheckAClosed :
      Unit.outputRelocationUnitWeightSymbolicCheckA ≡ true
    positiveKernelConstructed :
      Majorant.outputRelocationPositiveKernelConstructed ≡ true
    positiveKernelSummable :
      Majorant.outputRelocationPositiveKernelCutoffUniformlySummable ≡ true

open ThreeUnitWeightShellSchurReceipt public

threeUnitWeightShellSchurReceipt : ThreeUnitWeightShellSchurReceipt
threeUnitWeightShellSchurReceipt = receipt
  GT.threeFunctionSchurPrimaryFrameworkIsTrue
  Unit.outputRelocationUnitWeightSymbolicCheckAIsTrue
  Majorant.outputRelocationPositiveKernelConstructedIsTrue
  Majorant.outputRelocationPositiveKernelCutoffUniformlySummableIsTrue

outputRelocationOutputShellSchurConditionClosed : Bool
outputRelocationOutputShellSchurConditionClosed = true

outputRelocationFirstAdjointShellSchurConditionClosed : Bool
outputRelocationFirstAdjointShellSchurConditionClosed = true

outputRelocationSecondAdjointShellSchurConditionClosed : Bool
outputRelocationSecondAdjointShellSchurConditionClosed = true

outputRelocationThreeUnitWeightShellSchurConditionsClosed : Bool
outputRelocationThreeUnitWeightShellSchurConditionsClosed = true

outputRelocationConcreteOperatorGTConditionClosed : Bool
outputRelocationConcreteOperatorGTConditionClosed = false

outputRelocationOutputShellSchurConditionClosedIsTrue :
  outputRelocationOutputShellSchurConditionClosed ≡ true
outputRelocationOutputShellSchurConditionClosedIsTrue = refl

outputRelocationFirstAdjointShellSchurConditionClosedIsTrue :
  outputRelocationFirstAdjointShellSchurConditionClosed ≡ true
outputRelocationFirstAdjointShellSchurConditionClosedIsTrue = refl

outputRelocationSecondAdjointShellSchurConditionClosedIsTrue :
  outputRelocationSecondAdjointShellSchurConditionClosed ≡ true
outputRelocationSecondAdjointShellSchurConditionClosedIsTrue = refl

outputRelocationThreeUnitWeightShellSchurConditionsClosedIsTrue :
  outputRelocationThreeUnitWeightShellSchurConditionsClosed ≡ true
outputRelocationThreeUnitWeightShellSchurConditionsClosedIsTrue = refl

outputRelocationConcreteOperatorGTConditionClosedIsFalse :
  outputRelocationConcreteOperatorGTConditionClosed ≡ false
outputRelocationConcreteOperatorGTConditionClosedIsFalse = refl

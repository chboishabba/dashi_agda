module DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightCheckA where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Jean-Michel Bony; Hajer
-- Bahouri; Jean-Yves Chemin; Raphael Danchin; DASHI repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators"; "Calcul
-- symbolique et propagation des singularites pour les equations aux derivees
-- partielles non lineaires"; "Fourier Analysis and Nonlinear Partial
-- Differential Equations"; and "Unit-weight symbolic Check A for output
-- relocation".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Annales
-- scientifiques de l'Ecole Normale Superieure 14 (1981); Springer, 2011;
-- DASHI formal development, 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.24033/asens.1404;
-- 10.1007/978-3-642-16830-7; the repository theorem has no DOI.
-- Uses: Grafakos--Torres Theorem 1(c), whose abstract carrier requires three
-- strictly positive auxiliary weight functions but does not require the
-- source example's homogeneity equations; and the literal output-relocation
-- shell rows already proved in DASHI.
-- Relationship: replaces the failed all-three-homogeneity affine construction
-- by constant unit weights.  It closes the symbolic six-row Check A reduction
-- on 5/2 < s < 3.  Constructive dyadic summation and the concrete positive
-- kernel majorant remain separate obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresThreeFunctionSchurProgram as Schur
import DASHI.Physics.Closure.NSTriadKNOutputRelocationLiteralShellSubstitution as Shells
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFarkasDecision as FarkasDecision
import DASHI.Physics.Closure.NSTriadKNOutputRelocationBaseSystemClassification as Base

record UnitAffineData : Set where
  constructor unit-affine
  field
    leftBase rightBase outputBase : Int
    leftDirection rightDirection outputDirection : Int
    epsilonNumerator epsilonDenominator : Nat

open UnitAffineData public

-- Constant auxiliary functions h_L = h_R = h_O = 1 correspond to zero shell
-- exponents.  A positive epsilon may still be recorded; zero directions make
-- the family independent of it.
unitWeightAffineData : UnitAffineData
unitWeightAffineData = unit-affine
  (pos 0) (pos 0) (pos 0)
  (pos 0) (pos 0) (pos 0)
  1 4

-- With all auxiliary exponents zero, every low-shell row reduces to 5 - 4s
-- and every separation-gap row reduces to -4s.
unitWeightLowExponent : Base.AffineRegularity
unitWeightLowExponent = Base.affine (negsuc 3) (pos 5) 1

unitWeightGapExponent : Base.AffineRegularity
unitWeightGapExponent = Base.affine (negsuc 3) (pos 0) 1

record UnitWeightSixRowReduction : Set where
  constructor six-row-reduction
  field
    outputLow firstLow secondLow : Base.AffineRegularity
    outputGap firstGap secondGap : Base.AffineRegularity

open UnitWeightSixRowReduction public

unitWeightSixRowReduction : UnitWeightSixRowReduction
unitWeightSixRowReduction = six-row-reduction
  unitWeightLowExponent unitWeightLowExponent unitWeightLowExponent
  unitWeightGapExponent unitWeightGapExponent unitWeightGapExponent

record UnitWeightCheckAReceipt : Set where
  constructor receipt
  field
    threeFunctionSchurIsPrimary :
      Schur.threeFunctionSchurPrimaryFramework ≡ true
    literalRowsClosed :
      Shells.outputRelocationThreeConditionAffineRowsClosed ≡ true
    sourceStyleHomogeneityAnsatzFailed :
      FarkasDecision.currentHomogeneityPreservingAffineAnsatzInfeasible ≡ true
    failureWasNotUniversal :
      FarkasDecision.allPossibleThreeWeightAnsatzesInfeasible ≡ false
    allBasesAreZero :
      unitWeightAffineData ≡ unit-affine
        (pos 0) (pos 0) (pos 0)
        (pos 0) (pos 0) (pos 0)
        1 4
    allLowRowsCoincide :
      unitWeightSixRowReduction ≡ six-row-reduction
        unitWeightLowExponent unitWeightLowExponent unitWeightLowExponent
        unitWeightGapExponent unitWeightGapExponent unitWeightGapExponent

open UnitWeightCheckAReceipt public

unitWeightCheckAReceipt : UnitWeightCheckAReceipt
unitWeightCheckAReceipt = receipt
  Schur.threeFunctionSchurPrimaryFrameworkIsTrue
  Shells.outputRelocationThreeConditionAffineRowsClosedIsTrue
  FarkasDecision.currentHomogeneityPreservingAffineAnsatzInfeasibleIsTrue
  FarkasDecision.allPossibleThreeWeightAnsatzesInfeasibleIsFalse
  refl refl

unitWeightsAllowedBySchurCarrier : Bool
unitWeightsAllowedBySchurCarrier = true

unitWeightPositivityAndFinitenessTrivial : Bool
unitWeightPositivityAndFinitenessTrivial = true

unitWeightConjugatePowersTrivial : Bool
unitWeightConjugatePowersTrivial = true

unitWeightShellNormalizationTrivial : Bool
unitWeightShellNormalizationTrivial = true

outputRelocationUnitWeightSixRowsReduced : Bool
outputRelocationUnitWeightSixRowsReduced = true

outputRelocationUnitWeightCommonPositiveEpsilonIntervalComputed : Bool
outputRelocationUnitWeightCommonPositiveEpsilonIntervalComputed = true

outputRelocationUnitWeightSymbolicCheckA : Bool
outputRelocationUnitWeightSymbolicCheckA = true

outputRelocationUnitWeightConstructiveDyadicTailClosed : Bool
outputRelocationUnitWeightConstructiveDyadicTailClosed = false

outputRelocationUnitWeightAnalyticArchetypeClosed : Bool
outputRelocationUnitWeightAnalyticArchetypeClosed = false

unitWeightsAllowedBySchurCarrierIsTrue :
  unitWeightsAllowedBySchurCarrier ≡ true
unitWeightsAllowedBySchurCarrierIsTrue = refl

unitWeightPositivityAndFinitenessTrivialIsTrue :
  unitWeightPositivityAndFinitenessTrivial ≡ true
unitWeightPositivityAndFinitenessTrivialIsTrue = refl

unitWeightConjugatePowersTrivialIsTrue :
  unitWeightConjugatePowersTrivial ≡ true
unitWeightConjugatePowersTrivialIsTrue = refl

unitWeightShellNormalizationTrivialIsTrue :
  unitWeightShellNormalizationTrivial ≡ true
unitWeightShellNormalizationTrivialIsTrue = refl

outputRelocationUnitWeightSixRowsReducedIsTrue :
  outputRelocationUnitWeightSixRowsReduced ≡ true
outputRelocationUnitWeightSixRowsReducedIsTrue = refl

outputRelocationUnitWeightCommonPositiveEpsilonIntervalComputedIsTrue :
  outputRelocationUnitWeightCommonPositiveEpsilonIntervalComputed ≡ true
outputRelocationUnitWeightCommonPositiveEpsilonIntervalComputedIsTrue = refl

outputRelocationUnitWeightSymbolicCheckAIsTrue :
  outputRelocationUnitWeightSymbolicCheckA ≡ true
outputRelocationUnitWeightSymbolicCheckAIsTrue = refl

outputRelocationUnitWeightConstructiveDyadicTailClosedIsFalse :
  outputRelocationUnitWeightConstructiveDyadicTailClosed ≡ false
outputRelocationUnitWeightConstructiveDyadicTailClosedIsFalse = refl

outputRelocationUnitWeightAnalyticArchetypeClosedIsFalse :
  outputRelocationUnitWeightAnalyticArchetypeClosed ≡ false
outputRelocationUnitWeightAnalyticArchetypeClosedIsFalse = refl

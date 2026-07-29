module DASHI.Physics.Closure.NSTriadKNOutputRelocationCutoffUniformArchetypeProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Jean-Michel Bony; Hajer
-- Bahouri; Jean-Yves Chemin; Raphael Danchin; Errett Bishop; Douglas Bridges;
-- Zachary Murray; DASHI repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators"; "Calcul
-- symbolique et propagation des singularites pour les equations aux derivees
-- partielles non lineaires"; "Fourier Analysis and Nonlinear Partial
-- Differential Equations"; "Constructive Analysis"; "Constructive Analysis
-- in the Agda Proof Assistant"; and "Final cutoff-uniform output-relocation
-- archetype program".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Annales
-- scientifiques de l'Ecole Normale Superieure 14 (1981); Springer, 1985 and
-- 2011; arXiv, 2022; DASHI formal development, 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.24033/asens.1404;
-- 10.1007/978-3-642-16830-7; 10.1007/978-3-642-61667-9;
-- 10.48550/arXiv.2205.08354; the repository program has no DOI.
-- Uses: unit auxiliary weights, the exact integer geometric envelope with
-- constant 128/93, the minimal base-two power antitonicity bridge, the three
-- Grafakos--Torres conditions, and domination of the signed trilinear form by
-- its positive kernel majorant.
-- Relationship: names every remaining inhabitant needed to promote symbolic
-- Check A to the cutoff-uniform output-relocation archetype.  It does not
-- claim the constructive power bridge, the positive-kernel summation, or the
-- signed-majorant identification are already closed.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresThreeFunctionSchurProgram as Schur
import DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightCheckA as Unit
import DASHI.Physics.Closure.NSTriadKNOutputRelocationIntegerGeometricEnvelope as Envelope
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPowerMonotonicityBridge as PowerBridge

record OutputRelocationCutoffUniformArchetypeCutset {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s

    concretePowerEnvelopeBridge : Set s
    positiveKernelMajorant : Set s
    kernelMajorantNonnegative : Set s

    lowShellSeriesBoundedByFourThirds : Set s
    gapSeriesBoundedByThirtyTwoThirtyFirsts : Set s
    doubleSeriesBoundedByOneTwentyEightOverNinetyThree : Set s
    doubleSeriesBoundIndependentOfCutoff : Set s

    outputSchurConditionWithUnitWeights : Set s
    firstAdjointSchurConditionWithUnitWeights : Set s
    secondAdjointSchurConditionWithUnitWeights : Set s
    grafakosTorresConditionCInstantiated : Set s

    signedFormDominatedByPositiveMajorant : Set s
    outputRelocationCutoffUniformDualBound : Set s

open OutputRelocationCutoffUniformArchetypeCutset public

record OutputRelocationArchetypeProgramReceipt : Set where
  constructor receipt
  field
    threeFunctionSchurPrimary :
      Schur.threeFunctionSchurPrimaryFramework ≡ true
    unitWeightSymbolicCheckAClosed :
      Unit.outputRelocationUnitWeightSymbolicCheckA ≡ true
    integerEnvelopeClosed :
      Envelope.outputRelocationIntegerEnvelopeExponentsClosed ≡ true
    exactRationalGeometricConstantsClosed :
      Envelope.outputRelocationRationalGeometricConstantsClosed ≡ true
    minimalPowerBridgeSpecified :
      PowerBridge.outputRelocationMinimalPowerBridgeSpecified ≡ true
    onlyTwoPowerDominationLemmasRequired :
      PowerBridge.outputRelocationOnlyTwoPowerDominationLemmasRequired ≡ true
    concretePowerBridgeStillOpen :
      PowerBridge.outputRelocationConcretePowerEnvelopeBridgeClosed ≡ false

open OutputRelocationArchetypeProgramReceipt public

outputRelocationArchetypeProgramReceipt : OutputRelocationArchetypeProgramReceipt
outputRelocationArchetypeProgramReceipt = receipt
  Schur.threeFunctionSchurPrimaryFrameworkIsTrue
  Unit.outputRelocationUnitWeightSymbolicCheckAIsTrue
  Envelope.outputRelocationIntegerEnvelopeExponentsClosedIsTrue
  Envelope.outputRelocationRationalGeometricConstantsClosedIsTrue
  PowerBridge.outputRelocationMinimalPowerBridgeSpecifiedIsTrue
  PowerBridge.outputRelocationOnlyTwoPowerDominationLemmasRequiredIsTrue
  PowerBridge.outputRelocationConcretePowerEnvelopeBridgeClosedIsFalse

outputRelocationFinalArchetypeCutsetSpecified : Bool
outputRelocationFinalArchetypeCutsetSpecified = true

outputRelocationKernelMajorantSummable : Bool
outputRelocationKernelMajorantSummable = false

outputRelocationThreeConcreteSchurConditionsClosed : Bool
outputRelocationThreeConcreteSchurConditionsClosed = false

outputRelocationSignedFormDominatedByPositiveMajorant : Bool
outputRelocationSignedFormDominatedByPositiveMajorant = false

outputRelocationCutoffUniformArchetypeTheoremClosed : Bool
outputRelocationCutoffUniformArchetypeTheoremClosed = false

outputRelocationFinalArchetypeCutsetSpecifiedIsTrue :
  outputRelocationFinalArchetypeCutsetSpecified ≡ true
outputRelocationFinalArchetypeCutsetSpecifiedIsTrue = refl

outputRelocationKernelMajorantSummableIsFalse :
  outputRelocationKernelMajorantSummable ≡ false
outputRelocationKernelMajorantSummableIsFalse = refl

outputRelocationThreeConcreteSchurConditionsClosedIsFalse :
  outputRelocationThreeConcreteSchurConditionsClosed ≡ false
outputRelocationThreeConcreteSchurConditionsClosedIsFalse = refl

outputRelocationSignedFormDominatedByPositiveMajorantIsFalse :
  outputRelocationSignedFormDominatedByPositiveMajorant ≡ false
outputRelocationSignedFormDominatedByPositiveMajorantIsFalse = refl

outputRelocationCutoffUniformArchetypeTheoremClosedIsFalse :
  outputRelocationCutoffUniformArchetypeTheoremClosed ≡ false
outputRelocationCutoffUniformArchetypeTheoremClosedIsFalse = refl

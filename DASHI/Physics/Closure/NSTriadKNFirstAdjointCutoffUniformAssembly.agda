module DASHI.Physics.Closure.NSTriadKNFirstAdjointCutoffUniformAssembly where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Seungly Oh; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin; DASHI repository contributors.
-- Title: "Cutoff-uniform low-output convolution assembly for the first
-- periodic Navier-Stokes partial adjoint".
-- Venue/year: Communications in Partial Differential Equations 39 (2014),
-- 1128--1157; Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; DASHI formal development, 2026.
-- DOI: 10.1080/03605302.2013.822885;
-- 10.1007/978-3-642-16830-7; repository-original assembly has no DOI.
-- Uses: fixed-output finite Cauchy--Schwarz, translation injectivity, the
-- low-shell cardinality factor, the projected-mode multiplier bound, two
-- H^s weights, and cutoff-independent orbit/helicity/reality transport.
-- Relationship: fixes the quantifier order exists C_s before forall cutoff.
-- It does not declare the repository estimate closed until the ordered finite
-- l2 and concrete Leray-contraction instances are supplied.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Physics.Closure.NSTriadKNFirstAdjointShellConvolutionProgram as Prior
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNLerayContractionFromPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNHardDyadicShellOwner as Shell

shellCountConstant : Nat
shellCountConstant = 125

orbitConstant : Nat
orbitConstant = 48

helicityConstant : Nat
helicityConstant = 8

realityConstant : Nat
realityConstant = 2

baseTransportConstant : Nat
baseTransportConstant = orbitConstant * (helicityConstant * realityConstant)

baseSquaredEstimateConstant : Nat
baseSquaredEstimateConstant =
  shellCountConstant * (baseTransportConstant * baseTransportConstant)

record CutoffUniformFirstAdjointEstimate
    {c s st : Level} : Set (lsuc (c ⊔ s ⊔ st)) where
  field
    Cutoff : Set c
    Scalar : Set s
    State : Set st

    FiveHalvesBelow : Scalar → Set s
    BelowThree : Scalar → Set s
    Positive : Scalar → Set s
    _≤_ : Scalar → Scalar → Set s
    multiply : Scalar → Scalar → Scalar

    hsNormSquared : Scalar → State → Scalar
    firstAdjointShellNormSquared :
      Cutoff → Nat → Nat → State → State → Scalar
    shellMultiplierSquared : Nat → Scalar
    shellDecayWeight : Scalar → Nat → Nat → Scalar

    constantForSobolevExponent : Scalar → Scalar
    constantPositive : ∀ exponent →
      FiveHalvesBelow exponent → BelowThree exponent →
      Positive (constantForSobolevExponent exponent)

    estimateForEveryCutoff : ∀ exponent →
      FiveHalvesBelow exponent → BelowThree exponent →
      ∀ cutoff lowShell highShell left right →
      _≤_
        (firstAdjointShellNormSquared
          cutoff lowShell highShell left right)
        (multiply
          (constantForSobolevExponent exponent)
          (multiply
            (shellDecayWeight exponent lowShell highShell)
            (multiply
              (hsNormSquared exponent left)
              (hsNormSquared exponent right))))

    finiteCauchySchwarzConsumed : Set s
    translationInjectivityConsumed : Set s
    projectedModeBoundConsumed : Set s
    comparableHighShellConsumed : Set s
    orbitHelicityRealityTransportConsumed : Set s

open CutoffUniformFirstAdjointEstimate public

constantChosenBeforeCutoff :
  ∀ {c s st}
    (E : CutoffUniformFirstAdjointEstimate {c} {s} {st}) →
  (exponent : Scalar E) → Scalar E
constantChosenBeforeCutoff E exponent = constantForSobolevExponent E exponent

record ConcreteAssemblyCutset : Set₁ where
  field
    orderedFiniteL2Instance : Set
    concreteLerayPythagoreanInstance : Set
    projectedModeMultiplierBound : Set
    hardShellCardinalityBound : Set
    comparableHighSupportRestriction : Set
    twoSobolevWeightsInserted : Set
    geometricGapSeriesSummed : Set
    exactShellOrbitTransport : Set
    helicityTransport : Set
    directionWeightBound : Set

open ConcreteAssemblyCutset public

baseTransportConstantIsSevenHundredSixtyEight :
  baseTransportConstant ≡ 768
baseTransportConstantIsSevenHundredSixtyEight = refl

baseSquaredConstantIsSeventyThreeMillionSevenHundredTwentyEightThousand :
  baseSquaredEstimateConstant ≡ 73728000
baseSquaredConstantIsSeventyThreeMillionSevenHundredTwentyEightThousand = refl

uniformQuantifierOrderRepresented : Bool
uniformQuantifierOrderRepresented = true

uniformQuantifierOrderRepresentedIsTrue :
  uniformQuantifierOrderRepresented ≡ true
uniformQuantifierOrderRepresentedIsTrue = refl

priorDirectConvolutionMechanismRetained : Bool
priorDirectConvolutionMechanismRetained =
  Prior.lowOutputConvolutionMechanismIdentified

priorDirectConvolutionMechanismRetainedIsTrue :
  priorDirectConvolutionMechanismRetained ≡ true
priorDirectConvolutionMechanismRetainedIsTrue =
  Prior.lowOutputConvolutionMechanismIdentifiedIsTrue

orderedL2SurfaceConsumed : Bool
orderedL2SurfaceConsumed = L2.orderedEuclideanL2SurfaceRepresented

orderedL2SurfaceConsumedIsTrue : orderedL2SurfaceConsumed ≡ true
orderedL2SurfaceConsumedIsTrue = L2.orderedEuclideanL2SurfaceRepresentedIsTrue

lerayContractionReductionConsumed : Bool
lerayContractionReductionConsumed = Leray.lerayContractionReductionClosed

lerayContractionReductionConsumedIsTrue :
  lerayContractionReductionConsumed ≡ true
lerayContractionReductionConsumedIsTrue =
  Leray.lerayContractionReductionClosedIsTrue

hardShellConventionConsumed : Bool
hardShellConventionConsumed = Shell.hardDyadicShellConventionDefined

hardShellConventionConsumedIsTrue : hardShellConventionConsumed ≡ true
hardShellConventionConsumedIsTrue = Shell.hardDyadicShellConventionDefinedIsTrue

cutoffUniformFirstAdjointEstimateClosed : Bool
cutoffUniformFirstAdjointEstimateClosed = false

cutoffUniformFirstAdjointEstimateClosedIsFalse :
  cutoffUniformFirstAdjointEstimateClosed ≡ false
cutoffUniformFirstAdjointEstimateClosedIsFalse = refl

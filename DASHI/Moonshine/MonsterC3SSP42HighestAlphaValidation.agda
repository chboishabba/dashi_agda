module DASHI.Moonshine.MonsterC3SSP42HighestAlphaValidation where

------------------------------------------------------------------------
-- Focused cumulative root for the C3 / SSP15 / reduced-nonary tranche.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_; _*_)
open import Data.Empty using (⊥)
open import Data.Nat using (_%_)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as Xi
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.C3CyclotomicRealDescentExact as RealDescent
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as Amplitude
import DASHI.Moonshine.C3RiemannConjugationBridgeExact as RiemannBridge
import DASHI.Moonshine.SSP15AffineC3TranslationExact as SSP
import DASHI.Moonshine.SSP15CMModSevenExact as CM7
import DASHI.Moonshine.SSP15PhaseClosure54Exact as Closure54
import DASHI.Moonshine.MonsterReducedNonaryBoundaryExact as Reduced
import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as Monster
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM

zetaSquareInverseRegression :
  C3.multiplyPhase Fourier.zeta Fourier.zeta
  ≡ Fourier.inversePhase Fourier.zeta
zetaSquareInverseRegression = refl

fourierConjugateRowRegression :
  Fourier.conjugateRow Fourier.chi1 ≡ Fourier.chi2
fourierConjugateRowRegression = Fourier.chi1ConjugateIsChi2

c3ConjugationFixedPhaseIsTrivial :
  (phase : C3.C3Phase) →
  Fourier.inversePhase phase ≡ phase → phase ≡ Fourier.one
c3ConjugationFixedPhaseIsTrivial =
  RiemannBridge.conjugationFixedPhaseIsTrivial

criticalLineIsReflectionConjugationCoincidence :
  (point : Xi.ComplexCoordinate) →
  Xi.CriticalLine point →
  Xi.functionalReflection point ≡ Xi.conjugateCoordinate point
criticalLineIsReflectionConjugationCoincidence =
  RiemannBridge.criticalLineImpliesFunctionalEqualsConjugate

reflectionConjugationCoincidenceImpliesCriticalLine :
  (point : Xi.ComplexCoordinate) →
  Xi.functionalReflection point ≡ Xi.conjugateCoordinate point →
  Xi.CriticalLine point
reflectionConjugationCoincidenceImpliesCriticalLine =
  RiemannBridge.functionalEqualsConjugateImpliesCriticalLine

sspHorizontalAndVerticalTranslationsAreInverse :
  (mode : SSP.MobileComplementMode3) →
  SSP.advance12 (SSP.advance42 mode) ≡ mode
sspHorizontalAndVerticalTranslationsAreInverse = SSP.advance12After42

sspVerticalTranslationIsInverseZeta :
  (mode : SSP.MobileComplementMode3) →
  SSP.mobileModePhase (SSP.advance42 mode)
  ≡ C3.multiplyPhase (Fourier.inversePhase Fourier.zeta)
      (SSP.mobileModePhase mode)
sspVerticalTranslationIsInverseZeta = SSP.advance42IsMultiplyByInverseZeta

sspFortyTwoGridHitsLargestMonsterTriple :
  47 * 59 * 71 ≡ 196883
sspFortyTwoGridHitsLargestMonsterTriple =
  SSP.largestThreeOggProductIsMonsterDimension

sspCMObserverAgreesWithModSevenCharacter :
  (prime : Lane.MonsterPrimeLane) →
  SSP.cmClass prime
  ≡ CM7.cmClassFromModSeven (Lane.monsterPrimeLaneToNat prime % 7)
sspCMObserverAgreesWithModSevenCharacter =
  CM7.sspCMClassAgreesWithModSevenCharacter

fortyTwoIsCMCharacterPeriodOnAffineEdges : 42 % 7 ≡ 0
fortyTwoIsCMCharacterPeriodOnAffineEdges = CM7.fortyTwoModSevenIsZero

phaseNeutralClosureUsesFiftyFour : 12 + 42 ≡ 54
phaseNeutralClosureUsesFiftyFour = Closure54.horizontalPlusVerticalIsFiftyFour

phaseNeutralClosureActsAsIdentity :
  (mode : SSP.MobileComplementMode3) →
  SSP.mobileModePhase (SSP.advance12 (SSP.advance42 mode))
  ≡ SSP.mobileModePhase mode
phaseNeutralClosureActsAsIdentity = Closure54.fiftyFourClosureMatchesC3Identity

------------------------------------------------------------------------
-- Genuine observer non-factorability on SSP15.  p2 and p47 occupy the same
-- nonary complement fibre (mode27) but Q(sqrt(-7)) sees split vs inert, hence
-- no function of ComplementMode5 alone can recover the CM observer globally.

splitAndInertCannotBeSame :
  {x : CM.CMPrimeSplittingClass} →
  x ≡ CM.split → x ≡ CM.inert → ⊥
splitAndInertCannotBeSame refl ()

cmClassDoesNotDescendThroughComplementMode :
  (reconstruct : Nonary.ComplementMode5 → CM.CMPrimeSplittingClass) →
  ((prime : Lane.MonsterPrimeLane) →
    reconstruct (SSP.primeComplementMode prime) ≡ SSP.cmClass prime) →
  ⊥
cmClassDoesNotDescendThroughComplementMode reconstruct agrees =
  splitAndInertCannotBeSame (agrees Lane.p2) (agrees Lane.p47)

mode27OccupancyIsNotThree : SSP.mode27Occupancy ≡ 3 → ⊥
mode27OccupancyIsNotThree ()

reducedFiftyThreeRegression : 45 + 8 ≡ 53
reducedFiftyThreeRegression = Reduced.fiftyThreeIsFortyFivePlusEight

monsterDimensionRegression :
  Reduced.monsterDimensionFromLocalisedBoundary ≡ 196883
monsterDimensionRegression =
  Reduced.monsterDimensionFromLocalisedBoundaryIs196883

traceConjugationRegression :
  (phase : C3.C3Phase) →
  RealDescent.cyclotomicTrace (Fourier.inversePhase phase)
  ≡ RealDescent.cyclotomicTrace phase
traceConjugationRegression = RealDescent.traceIsConjugationInvariant

amplitudeNormLandsOnRationalAxis :
  (value : Amplitude.Cyclotomic3) →
  Amplitude.multiply value (Amplitude.conjugate value)
  ≡ Amplitude.embedRational (Amplitude.norm value)
amplitudeNormLandsOnRationalAxis =
  Amplitude.multiplyByConjugateLandsOnNorm

amplitudeTraceIsConjugationInvariant :
  (value : Amplitude.Cyclotomic3) →
  Amplitude.trace (Amplitude.conjugate value) ≡ Amplitude.trace value
amplitudeTraceIsConjugationInvariant =
  Amplitude.traceConjugationInvariant

balancedRegularBulkStillMatchesMonsterOwner :
  Monster.balancedRegularBulkDimension ≡ Reduced.monsterBulk
balancedRegularBulkStillMatchesMonsterOwner = refl

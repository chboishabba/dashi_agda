module DASHI.Physics.Closure.R2P227729FourGridRetainedQuadraticParetoExact where

------------------------------------------------------------------------
-- PARETO: 3 vs 4 vs 5 samples per axis, for a *quadratic* band K=1.
--
-- Original Fourier/dealiasing priority:
--   Patterson and Orszag (1971), Orszag 2/3 rule;
--   Lambert, Reneuve and Augier (2026), arXiv:2603.08892.
-- Original DASHI source: 27x27 integer-mode pair and 125-output owners,
-- as well as exact C3^3 cyclic Fourier mathematics.
--
-- NEW finite result: four periodic RESIDUE labels (-1,0,1,2~-2) are
-- sufficient for an exact *retained* quadratic product in [-1,1]^3,
-- even though the output +2 and -2 frequencies collide at N=4.
-- Five labels per axis are sufficient for the FULL [-2,2]^3 output.
-- Three labels per axis are not sufficient even for the retained modes.
--
-- A real 4^3 sampled-field DFT/operator is not built here. This proves
-- the discrete pair-incidence / output-projection identity for all Nat
-- coefficients, not complex FFT or NS time evolution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Conv
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Core

-- The fourth residue class represents both +/-2 (modulo 4).
data FourGridMode : Set where
  fourMinusOne fourZero fourPlusOne fourOuterTwo : FourGridMode

foldFour : M.FiveMode → FourGridMode
foldFour M.wideMinusTwo = fourOuterTwo
foldFour M.wideMinusOne = fourMinusOne
foldFour M.wideZero = fourZero
foldFour M.widePlusOne = fourPlusOne
foldFour M.widePlusTwo = fourOuterTwo

retainedAsWideMode : M.ThreeMode → M.FiveMode
retainedAsWideMode M.modeMinus = M.wideMinusOne
retainedAsWideMode M.modeZero = M.wideZero
retainedAsWideMode M.modePlus = M.widePlusOne

eqFour : FourGridMode → FourGridMode → Bool
eqFour fourMinusOne fourMinusOne = true
eqFour fourZero fourZero = true
eqFour fourPlusOne fourPlusOne = true
eqFour fourOuterTwo fourOuterTwo = true
eqFour _ _ = false

-- Four-grid only has to distinguish the retained classes from EVERY
-- input quadratic output. It need not distinguish +2 from -2.
fourGridRetainedMembership :
  (wide : M.FiveMode) (retained : M.ThreeMode) →
  eqFour (foldFour wide) (foldFour (retainedAsWideMode retained))
    ≡ Conv.eqWideMode wide (retainedAsWideMode retained)
fourGridRetainedMembership M.wideMinusTwo M.modeMinus = refl
fourGridRetainedMembership M.wideMinusTwo M.modeZero = refl
fourGridRetainedMembership M.wideMinusTwo M.modePlus = refl
fourGridRetainedMembership M.wideMinusOne M.modeMinus = refl
fourGridRetainedMembership M.wideMinusOne M.modeZero = refl
fourGridRetainedMembership M.wideMinusOne M.modePlus = refl
fourGridRetainedMembership M.wideZero M.modeMinus = refl
fourGridRetainedMembership M.wideZero M.modeZero = refl
fourGridRetainedMembership M.wideZero M.modePlus = refl
fourGridRetainedMembership M.widePlusOne M.modeMinus = refl
fourGridRetainedMembership M.widePlusOne M.modeZero = refl
fourGridRetainedMembership M.widePlusOne M.modePlus = refl
fourGridRetainedMembership M.widePlusTwo M.modeMinus = refl
fourGridRetainedMembership M.widePlusTwo M.modeZero = refl
fourGridRetainedMembership M.widePlusTwo M.modePlus = refl

record FourGridCube64 : Set where
  constructor fourCube
  field x y z : FourGridMode
open FourGridCube64 public

wideToFourGrid : Conv.WideCube125 → FourGridCube64
wideToFourGrid (Conv.wideCube a b c) =
  fourCube (foldFour a) (foldFour b) (foldFour c)

eqFourCube : FourGridCube64 → FourGridCube64 → Bool
eqFourCube (fourCube a b c) (fourCube x y z) =
  Conv._&&B_
    (Conv._&&B_ (eqFour a x) (eqFour b y))
    (eqFour c z)

------------------------------------------------------------------------
-- This IS the group addition table for Z/4, not merely a custom
-- comparison of residues after already knowing the integer result.
-- Encoding each input first and adding in this group gives the same
-- four-residue label as taking the true integer Fourier sum and folding.
------------------------------------------------------------------------

fourGroupAdd : FourGridMode → FourGridMode → FourGridMode
fourGroupAdd fourZero x = x
fourGroupAdd fourMinusOne fourZero = fourMinusOne
fourGroupAdd fourMinusOne fourMinusOne = fourOuterTwo
fourGroupAdd fourMinusOne fourPlusOne = fourZero
fourGroupAdd fourMinusOne fourOuterTwo = fourPlusOne
fourGroupAdd fourPlusOne fourZero = fourPlusOne
fourGroupAdd fourPlusOne fourMinusOne = fourZero
fourGroupAdd fourPlusOne fourPlusOne = fourOuterTwo
fourGroupAdd fourPlusOne fourOuterTwo = fourMinusOne
fourGroupAdd fourOuterTwo fourZero = fourOuterTwo
fourGroupAdd fourOuterTwo fourMinusOne = fourPlusOne
fourGroupAdd fourOuterTwo fourPlusOne = fourMinusOne
fourGroupAdd fourOuterTwo fourOuterTwo = fourZero

fourGroupMatchesTrueSignedPairSum :
  (a b : M.ThreeMode) →
  fourGroupAdd
    (foldFour (retainedAsWideMode a))
    (foldFour (retainedAsWideMode b))
    ≡ foldFour (M.exactQuadraticModeSum a b)
fourGroupMatchesTrueSignedPairSum M.modeMinus M.modeMinus = refl
fourGroupMatchesTrueSignedPairSum M.modeMinus M.modeZero = refl
fourGroupMatchesTrueSignedPairSum M.modeMinus M.modePlus = refl
fourGroupMatchesTrueSignedPairSum M.modeZero M.modeMinus = refl
fourGroupMatchesTrueSignedPairSum M.modeZero M.modeZero = refl
fourGroupMatchesTrueSignedPairSum M.modeZero M.modePlus = refl
fourGroupMatchesTrueSignedPairSum M.modePlus M.modeMinus = refl
fourGroupMatchesTrueSignedPairSum M.modePlus M.modeZero = refl
fourGroupMatchesTrueSignedPairSum M.modePlus M.modePlus = refl

inputToFourGrid : I.ModeCube27 → FourGridCube64
inputToFourGrid (I.modeCube a b c) =
  fourCube
    (foldFour (retainedAsWideMode a))
    (foldFour (retainedAsWideMode b))
    (foldFour (retainedAsWideMode c))

fourGridGroupSum :
  FourGridCube64 → FourGridCube64 → FourGridCube64
fourGridGroupSum (fourCube a b c) (fourCube d e f) =
  fourCube (fourGroupAdd a d) (fourGroupAdd b e) (fourGroupAdd c f)

fourGridGroupSumMatchesIntegerPair :
  (p q : I.ModeCube27) →
  fourGridGroupSum (inputToFourGrid p) (inputToFourGrid q)
    ≡ wideToFourGrid (Conv.exactPairOutput p q)
fourGridGroupSumMatchesIntegerPair
  (I.modeCube a b c) (I.modeCube d e f)
  rewrite fourGroupMatchesTrueSignedPairSum a d
        | fourGroupMatchesTrueSignedPairSum b e
        | fourGroupMatchesTrueSignedPairSum c f = refl

fourGridRetainedCubeMembership :
  (wide : Conv.WideCube125) (retained : I.ModeCube27) →
  eqFourCube (wideToFourGrid wide)
    (wideToFourGrid (Conv.retainedToWide retained))
    ≡ Conv.eqWideCube wide (Conv.retainedToWide retained)
fourGridRetainedCubeMembership (Conv.wideCube a b c)
  (I.modeCube x y z)
  rewrite fourGridRetainedMembership a x
        | fourGridRetainedMembership b y
        | fourGridRetainedMembership c z = refl

fourGridPairContribution :
  (target : I.ModeCube27) →
  (amplitude : I.ModeCube27 → Nat) →
  I.ModePair729 → Nat
fourGridPairContribution target amplitude (p , q) =
  Conv.weightIf
    (eqFourCube
      (fourGridGroupSum (inputToFourGrid p) (inputToFourGrid q))
      (wideToFourGrid (Conv.retainedToWide target)))
    (amplitude p * amplitude q)

fourGridPairCorrect :
  (target : I.ModeCube27) →
  (amplitude : I.ModeCube27 → Nat) →
  (pair : I.ModePair729) →
  fourGridPairContribution target amplitude pair
    ≡ Conv.exactPairContribution (Conv.retainedToWide target) amplitude pair
fourGridPairCorrect target amplitude (p , q)
  rewrite fourGridGroupSumMatchesIntegerPair p q
        | fourGridRetainedCubeMembership
            (Conv.exactPairOutput p q) target = refl

fourGridRetainedConvolutionAt :
  (amplitude : I.ModeCube27 → Nat) →
  I.ModeCube27 → Nat
fourGridRetainedConvolutionAt amplitude target =
  Conv.sumPairWeights I.pair729 (fourGridPairContribution target amplitude)

fourGridRetainedConvolutionOnAnyPairList :
  (target : I.ModeCube27) →
  (amplitude : I.ModeCube27 → Nat) →
  (pairs : List I.ModePair729) →
  Conv.sumPairWeights pairs (fourGridPairContribution target amplitude)
    ≡ Conv.sumPairWeights pairs
        (Conv.exactPairContribution (Conv.retainedToWide target) amplitude)
fourGridRetainedConvolutionOnAnyPairList target amplitude [] = refl
fourGridRetainedConvolutionOnAnyPairList target amplitude (p ∷ ps)
  rewrite fourGridPairCorrect target amplitude p
        | fourGridRetainedConvolutionOnAnyPairList target amplitude ps = refl

-- For every Nat-valued amplitude on 27 modes, at every retained output.
-- This is operator equality of *finite index aggregations*, not a 4^3 DFT.
fourGridMatchesExactRetainedForAllCoefficients :
  (amplitude : I.ModeCube27 → Nat)
  (target : I.ModeCube27) →
  fourGridRetainedConvolutionAt amplitude target
    ≡ Conv.exactConvolutionAt amplitude (Conv.retainedToWide target)
fourGridMatchesExactRetainedForAllCoefficients amplitude target =
  fourGridRetainedConvolutionOnAnyPairList target amplitude I.pair729

-- The same true output can be fully recovered from N=5 indices.
fiveGridMatchesExactFullForAllCoefficients :
  (amplitude : I.ModeCube27 → Nat)
  (target : Conv.WideCube125) →
  Conv.fiveIndexRecoveredConvolutionAt amplitude target
    ≡ Conv.exactConvolutionAt amplitude target
fiveGridMatchesExactFullForAllCoefficients =
  Conv.all729PairsFiveIndexRecoveryIsExact

-- N=4 is NOT sufficient to reconstruct the FULL 125-output spectrum.
outerFrequencyCollisionAtFour :
  foldFour M.wideMinusTwo ≡ foldFour M.widePlusTwo
outerFrequencyCollisionAtFour = refl

outerFrequenciesReallyDiffer :
  M.wideMinusTwo ≡ M.widePlusTwo →
  ⊥
outerFrequenciesReallyDiffer ()

------------------------------------------------------------------------
-- Source generic consumer nonfactorability, instantiated to the N=4
-- full-wide-output collision. N=4 IS precise enough for retained K=1,
-- but CANNOT recover the original signed +/-2 spectral coefficients.
------------------------------------------------------------------------

outerMinusTwoX : Conv.WideCube125
outerMinusTwoX = Conv.wideCube M.wideMinusTwo M.wideZero M.wideZero

outerPlusTwoX : Conv.WideCube125
outerPlusTwoX = Conv.wideCube M.widePlusTwo M.wideZero M.wideZero

fourGridOuterOutputsCollide :
  wideToFourGrid outerMinusTwoX ≡ wideToFourGrid outerPlusTwoX
fourGridOuterOutputsCollide = refl

distinctWideOuterOutputs : outerMinusTwoX ≡ outerPlusTwoX → ⊥
distinctWideOuterOutputs ()

fourGridFullOutputCollision :
  Core.ConsumerCollision wideToFourGrid (λ w → w)
fourGridFullOutputCollision =
  NF.nonFactorabilityWitness
    outerMinusTwoX outerPlusTwoX
    fourGridOuterOutputsCollide
    distinctWideOuterOutputs

fourGridCannotRecoverFullIntegerSpectrum :
  Core.ConsumerSufficient wideToFourGrid (λ w → w) → ⊥
fourGridCannotRecoverFullIntegerSpectrum =
  Core.collisionRefutesSufficiency fourGridFullOutputCollision

fourGridPostprocessingCannotRestoreFullSpectrum :
  ∀ {Chart : Set} (chart : FourGridCube64 → Chart) →
  Core.ConsumerSufficient (λ w → chart (wideToFourGrid w)) (λ w → w)
    → ⊥
fourGridPostprocessingCannotRestoreFullSpectrum chart =
  Core.collisionSurvivesRechart chart fourGridFullOutputCollision

-- N=3 is insufficient even at a RETAINED index.
threeGridFalseRetainedNegativeFrequency :
  M.periodicQuadraticModeSum M.modePlus M.modePlus ≡ M.modeMinus
threeGridFalseRetainedNegativeFrequency =
  M.positivePositiveAliasesToNegative

-- Pareto capacities, not asymptotic runtime benchmarks.
threeGridSampleCount : 3 * 3 * 3 ≡ 27
threeGridSampleCount = refl

fourGridSampleCount : 4 * 4 * 4 ≡ 64
fourGridSampleCount = refl

fiveGridSampleCount : 5 * 5 * 5 ≡ 125
fiveGridSampleCount = refl

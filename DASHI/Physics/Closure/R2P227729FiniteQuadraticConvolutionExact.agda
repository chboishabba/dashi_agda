module DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact where

------------------------------------------------------------------------
-- FINITE THREE-DIMENSIONAL QUADRATIC CONVOLUTION / FIVE-MODE LABEL
-- RECOVERY. This is a NEW application of the existing 27-mode carrier.
--
-- There are 729 ordered input pairs. Each pair has its true integer
-- coordinatewise sum in [-2..2]^3. A five-point RESIDUE LABEL per axis
-- uniquely records such an output. A three-point residue does not.
--
-- Main statement is for ARBITRARY natural-number coefficients on all 27
-- input modes, and EACH of the 125 wide outputs. No choice of synthetic
-- binary/ternary amplitude vectors is built into the theorem.
--
-- IMPORTANT LIMIT: the five-grid "encode/decode" is a typed five-point
-- INDEX bijection here. This does NOT yet construct a DFT, prove Parseval,
-- derive a sampled physical-space product or model actual complex NS fields.
-- The result is a finite coefficient-wise index/aggregation equality.
--
-- Mathematics/provenance:
--   Orszag/Patterson historical pseudo-spectral dealiasing;
--   Lambert, Reneuve, Augier 2026 arXiv:2603.08892.
--   DASHI source original: Integer Fourier lattice, ternary-27 cube,
--   codec and 729-pair incidence. No ESD or Monster 3B modifications.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Core
import DASHI.Core.IntersectionalNonFactorability as NF
open import Data.Empty using (⊥)
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I

record WideCube125 : Set where
  constructor wideCube
  field
    x y z : M.FiveMode
open WideCube125 public

record GridCube125 : Set where
  constructor gridCube
  field
    x y z : I.FiveGridMode
open GridCube125 public

exactPairOutput :
  I.ModeCube27 → I.ModeCube27 → WideCube125
exactPairOutput (I.modeCube a b c) (I.modeCube d e f) =
  wideCube
    (M.exactQuadraticModeSum a d)
    (M.exactQuadraticModeSum b e)
    (M.exactQuadraticModeSum c f)

wideToFiveGrid : WideCube125 → GridCube125
wideToFiveGrid (wideCube a b c) =
  gridCube (I.toGridFive a) (I.toGridFive b) (I.toGridFive c)

fiveGridToWide : GridCube125 → WideCube125
fiveGridToWide (gridCube a b c) =
  wideCube (I.fromGridFive a) (I.fromGridFive b) (I.fromGridFive c)

wideFiveRoundTrip :
  (w : WideCube125) → fiveGridToWide (wideToFiveGrid w) ≡ w
wideFiveRoundTrip (wideCube a b c)
  rewrite I.fiveGridModeRoundTrip a
        | I.fiveGridModeRoundTrip b
        | I.fiveGridModeRoundTrip c = refl

fiveWideRoundTrip :
  (g : GridCube125) → wideToFiveGrid (fiveGridToWide g) ≡ g
fiveWideRoundTrip (gridCube a b c) =
  gridAll a b c
  where
    gridOne : (v : I.FiveGridMode) → I.toGridFive (I.fromGridFive v) ≡ v
    gridOne I.gridMinusTwo = refl
    gridOne I.gridMinusOne = refl
    gridOne I.gridZero = refl
    gridOne I.gridPlusOne = refl
    gridOne I.gridPlusTwo = refl

    gridAll :
      (a b c : I.FiveGridMode) →
      wideToFiveGrid (fiveGridToWide (gridCube a b c))
        ≡ gridCube a b c
    gridAll a b c rewrite gridOne a | gridOne b | gridOne c = refl

------------------------------------------------------------------------
-- Explicit cyclic Z/5 addition, so the padded index consumer computes
-- the same residues directly from input labels, WITHOUT first observing
-- their full Z^3 sum. This is finite GROUP CONVOLUTION incidence.
------------------------------------------------------------------------

fiveGroupAdd : I.FiveGridMode → I.FiveGridMode → I.FiveGridMode
fiveGroupAdd I.gridZero x = x
fiveGroupAdd I.gridMinusTwo I.gridMinusTwo = I.gridPlusOne
fiveGroupAdd I.gridMinusTwo I.gridMinusOne = I.gridPlusTwo
fiveGroupAdd I.gridMinusTwo I.gridZero = I.gridMinusTwo
fiveGroupAdd I.gridMinusTwo I.gridPlusOne = I.gridMinusOne
fiveGroupAdd I.gridMinusTwo I.gridPlusTwo = I.gridZero
fiveGroupAdd I.gridMinusOne I.gridMinusTwo = I.gridPlusTwo
fiveGroupAdd I.gridMinusOne I.gridMinusOne = I.gridMinusTwo
fiveGroupAdd I.gridMinusOne I.gridZero = I.gridMinusOne
fiveGroupAdd I.gridMinusOne I.gridPlusOne = I.gridZero
fiveGroupAdd I.gridMinusOne I.gridPlusTwo = I.gridPlusOne
fiveGroupAdd I.gridPlusOne I.gridMinusTwo = I.gridMinusOne
fiveGroupAdd I.gridPlusOne I.gridMinusOne = I.gridZero
fiveGroupAdd I.gridPlusOne I.gridZero = I.gridPlusOne
fiveGroupAdd I.gridPlusOne I.gridPlusOne = I.gridPlusTwo
fiveGroupAdd I.gridPlusOne I.gridPlusTwo = I.gridMinusTwo
fiveGroupAdd I.gridPlusTwo I.gridMinusTwo = I.gridZero
fiveGroupAdd I.gridPlusTwo I.gridMinusOne = I.gridPlusOne
fiveGroupAdd I.gridPlusTwo I.gridZero = I.gridPlusTwo
fiveGroupAdd I.gridPlusTwo I.gridPlusOne = I.gridMinusTwo
fiveGroupAdd I.gridPlusTwo I.gridPlusTwo = I.gridMinusOne

inputToFiveAxis : M.ThreeMode → I.FiveGridMode
inputToFiveAxis M.modeMinus = I.gridMinusOne
inputToFiveAxis M.modeZero = I.gridZero
inputToFiveAxis M.modePlus = I.gridPlusOne

fiveGroupMatchesTrueSignedPairSum :
  (a b : M.ThreeMode) →
  fiveGroupAdd (inputToFiveAxis a) (inputToFiveAxis b)
    ≡ I.toGridFive (M.exactQuadraticModeSum a b)
fiveGroupMatchesTrueSignedPairSum M.modeMinus M.modeMinus = refl
fiveGroupMatchesTrueSignedPairSum M.modeMinus M.modeZero = refl
fiveGroupMatchesTrueSignedPairSum M.modeMinus M.modePlus = refl
fiveGroupMatchesTrueSignedPairSum M.modeZero M.modeMinus = refl
fiveGroupMatchesTrueSignedPairSum M.modeZero M.modeZero = refl
fiveGroupMatchesTrueSignedPairSum M.modeZero M.modePlus = refl
fiveGroupMatchesTrueSignedPairSum M.modePlus M.modeMinus = refl
fiveGroupMatchesTrueSignedPairSum M.modePlus M.modeZero = refl
fiveGroupMatchesTrueSignedPairSum M.modePlus M.modePlus = refl

inputToFiveGrid : I.ModeCube27 → GridCube125
inputToFiveGrid (I.modeCube a b c) =
  gridCube (inputToFiveAxis a) (inputToFiveAxis b) (inputToFiveAxis c)

fiveGridGroupSum : GridCube125 → GridCube125 → GridCube125
fiveGridGroupSum (gridCube a b c) (gridCube d e f) =
  gridCube (fiveGroupAdd a d) (fiveGroupAdd b e) (fiveGroupAdd c f)

fiveGridGroupSumMatchesIntegerPair :
  (p q : I.ModeCube27) →
  fiveGridGroupSum (inputToFiveGrid p) (inputToFiveGrid q)
    ≡ wideToFiveGrid (exactPairOutput p q)
fiveGridGroupSumMatchesIntegerPair
  (I.modeCube a b c) (I.modeCube d e f)
  rewrite fiveGroupMatchesTrueSignedPairSum a d
        | fiveGroupMatchesTrueSignedPairSum b e
        | fiveGroupMatchesTrueSignedPairSum c f = refl

pairOutputFivePointRecovered :
  (p q : I.ModeCube27) →
  fiveGridToWide (wideToFiveGrid (exactPairOutput p q))
    ≡ exactPairOutput p q
pairOutputFivePointRecovered p q =
  wideFiveRoundTrip (exactPairOutput p q)

-- No 3-grid or generic codec can repair the true wavevector after folding:
-- inherited no-factor proof remains the lower-level information gate.
threePointFoldingCannotRecoverEveryTrueIndex :
  Core.ConsumerSufficient M.periodicThreePointFold (λ w → w)
    → ⊥
threePointFoldingCannotRecoverEveryTrueIndex =
  M.foldedThreePointModeCannotRecoverExactFourierIndex

------------------------------------------------------------------------
-- The FULL 27-C3 DFT does not restore integer indices discarded
-- BEFORE it receives the cyclic Fourier coefficient array.
------------------------------------------------------------------------

wideIntegerOutputToThreeResidues : WideCube125 → I.ModeCube27
wideIntegerOutputToThreeResidues (wideCube a b c) =
  I.modeCube
    (M.periodicThreePointFold a)
    (M.periodicThreePointFold b)
    (M.periodicThreePointFold c)

realWidePlusTwoX : WideCube125
realWidePlusTwoX = wideCube M.widePlusTwo M.wideZero M.wideZero

realWideMinusOneX : WideCube125
realWideMinusOneX = wideCube M.wideMinusOne M.wideZero M.wideZero

wideOutputsCollideOnCyclic27Residue :
  wideIntegerOutputToThreeResidues realWidePlusTwoX
    ≡ wideIntegerOutputToThreeResidues realWideMinusOneX
wideOutputsCollideOnCyclic27Residue = refl

differentActualIntegerWideOutputs :
  realWidePlusTwoX ≡ realWideMinusOneX → ⊥
differentActualIntegerWideOutputs ()

threeAxisCyclicIndexCollision :
  Core.ConsumerCollision wideIntegerOutputToThreeResidues (λ w → w)
threeAxisCyclicIndexCollision =
  NF.nonFactorabilityWitness
    realWidePlusTwoX realWideMinusOneX
    wideOutputsCollideOnCyclic27Residue
    differentActualIntegerWideOutputs

noDecoderOfActualWideModeFromCyclic27 :
  Core.ConsumerSufficient wideIntegerOutputToThreeResidues (λ w → w) → ⊥
noDecoderOfActualWideModeFromCyclic27 =
  Core.collisionRefutesSufficiency threeAxisCyclicIndexCollision

cyclic27RechartCannotUndoWideFrequencyLoss :
  ∀ {Chart : Set} (chart : I.ModeCube27 → Chart) →
  Core.ConsumerSufficient
    (λ w → chart (wideIntegerOutputToThreeResidues w))
    (λ w → w) → ⊥
cyclic27RechartCannotUndoWideFrequencyLoss chart =
  Core.collisionSurvivesRechart chart threeAxisCyclicIndexCollision

------------------------------------------------------------------------
-- Explicit five-label equality. It is equality of mathematical indices,
-- not equality of discretized field values or physical spectra.
------------------------------------------------------------------------

eqWideMode : M.FiveMode → M.FiveMode → Bool
eqWideMode M.wideMinusTwo M.wideMinusTwo = true
eqWideMode M.wideMinusOne M.wideMinusOne = true
eqWideMode M.wideZero M.wideZero = true
eqWideMode M.widePlusOne M.widePlusOne = true
eqWideMode M.widePlusTwo M.widePlusTwo = true
eqWideMode _ _ = false

_&&B_ : Bool → Bool → Bool
true &&B b = b
false &&B b = false

eqWideCube : WideCube125 → WideCube125 → Bool
eqWideCube (wideCube a b c) (wideCube x y z) =
  (eqWideMode a x &&B eqWideMode b y) &&B eqWideMode c z

weightIf : Bool → Nat → Nat
weightIf true n = n
weightIf false n = 0

Pair729 : Set
Pair729 = I.ModePair729

-- Each coefficient is a general, arbitrarily chosen natural number,
-- not a trit. This is a bona fide all-input finite bilinear sum.
exactPairContribution :
  (target : WideCube125) →
  (amplitude : I.ModeCube27 → Nat) →
  Pair729 → Nat
exactPairContribution target amplitude (p , q) =
  weightIf (eqWideCube (exactPairOutput p q) target)
    (amplitude p * amplitude q)

fiveGridPairContribution :
  (target : WideCube125) →
  (amplitude : I.ModeCube27 → Nat) →
  Pair729 → Nat
fiveGridPairContribution target amplitude (p , q) =
  weightIf
    (eqWideCube
      (fiveGridToWide
        (fiveGridGroupSum (inputToFiveGrid p) (inputToFiveGrid q)))
      target)
    (amplitude p * amplitude q)

fiveGridPairContributionEqualsExact :
  (target : WideCube125) →
  (amplitude : I.ModeCube27 → Nat) →
  (pair : Pair729) →
  fiveGridPairContribution target amplitude pair
    ≡ exactPairContribution target amplitude pair
fiveGridPairContributionEqualsExact target amplitude (p , q)
  rewrite fiveGridGroupSumMatchesIntegerPair p q
        | pairOutputFivePointRecovered p q = refl

sumPairWeights :
  (pairs : List Pair729) → (weight : Pair729 → Nat) → Nat
sumPairWeights [] weight = 0
sumPairWeights (pair ∷ pairs) weight =
  weight pair + sumPairWeights pairs weight

sumFiveEqualsExactOnAnyPairList :
  (target : WideCube125) →
  (amplitude : I.ModeCube27 → Nat) →
  (pairs : List Pair729) →
  sumPairWeights pairs (fiveGridPairContribution target amplitude)
    ≡ sumPairWeights pairs (exactPairContribution target amplitude)
sumFiveEqualsExactOnAnyPairList target amplitude [] = refl
sumFiveEqualsExactOnAnyPairList target amplitude (p ∷ ps)
  rewrite fiveGridPairContributionEqualsExact target amplitude p
        | sumFiveEqualsExactOnAnyPairList target amplitude ps = refl

exactConvolutionAt :
  (amplitude : I.ModeCube27 → Nat) →
  WideCube125 → Nat
exactConvolutionAt amplitude target =
  sumPairWeights I.pair729 (exactPairContribution target amplitude)

fiveIndexRecoveredConvolutionAt :
  (amplitude : I.ModeCube27 → Nat) →
  WideCube125 → Nat
fiveIndexRecoveredConvolutionAt amplitude target =
  sumPairWeights I.pair729 (fiveGridPairContribution target amplitude)

-- EVERY one of the 125 wide indices, and ALL assignments of natural
-- input amplitudes; no 27 synthetic input-profile restriction.
all729PairsFiveIndexRecoveryIsExact :
  (amplitude : I.ModeCube27 → Nat) (target : WideCube125) →
  fiveIndexRecoveredConvolutionAt amplitude target
    ≡ exactConvolutionAt amplitude target
all729PairsFiveIndexRecoveryIsExact amplitude target =
  sumFiveEqualsExactOnAnyPairList target amplitude I.pair729

-- The retained cube is a subcarrier of the 125 exact integer outputs.
retainedToWide : I.ModeCube27 → WideCube125
retainedToWide (I.modeCube a b c) =
  wideCube (embed a) (embed b) (embed c)
  where
    embed : M.ThreeMode → M.FiveMode
    embed M.modeMinus = M.wideMinusOne
    embed M.modeZero = M.wideZero
    embed M.modePlus = M.widePlusOne

retainedFiveIndexConvolutionExact :
  (amplitude : I.ModeCube27 → Nat) (k : I.ModeCube27) →
  fiveIndexRecoveredConvolutionAt amplitude (retainedToWide k)
    ≡ exactConvolutionAt amplitude (retainedToWide k)
retainedFiveIndexConvolutionExact amplitude k =
  all729PairsFiveIndexRecoveryIsExact amplitude (retainedToWide k)

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
fiveWideRoundTrip (gridCube I.gridMinusTwo I.gridMinusTwo I.gridMinusTwo) = refl
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
      (fiveGridToWide (wideToFiveGrid (exactPairOutput p q)))
      target)
    (amplitude p * amplitude q)

fiveGridPairContributionEqualsExact :
  (target : WideCube125) →
  (amplitude : I.ModeCube27 → Nat) →
  (pair : Pair729) →
  fiveGridPairContribution target amplitude pair
    ≡ exactPairContribution target amplitude pair
fiveGridPairContributionEqualsExact target amplitude (p , q)
  rewrite pairOutputFivePointRecovered p q = refl

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

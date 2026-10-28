module DASHI.Physics.Closure.R2P2C4C5NyquistAntipodalFixedPointExact where

------------------------------------------------------------------------
-- C2 GLOBAL ANTIPODE ON THE REAL C4^3 AND C5^3 CYCLIC GRID LABELS
--
-- Source owners: Original BalancedTernaryAntipodalOrbitExact and
-- BalancedTernaryHypercubeAntipodalOrbitCountExact own the C3 odd-grid
-- rank hierarchy (3 -> 2, 9 -> 5, 27 -> 14). Source C3^3 DFT lives in
-- Biology.Physical.C3CubeCyclotomicFourierExact.
--
-- Distinct index-space extension for CURRENT FOUR/ FIVE-GRID
-- quadratic Fourier Pareto (not a C4 or C5 physical-space FFT):
--
--      N=3: 27 =  1 fixed zero + 13 * 2     => 14 classes
--      N=4: 64 =  8 fixed Nyquist corners + 28 * 2 => 36 classes
--      N=5:125 =  1 fixed zero + 62 * 2     => 63 classes
--
-- The three-dimensional C4 grid has EIGHT fixed antipodal residues,
-- coordinates independently 0 or 2 (Nyquist); do not reuse odd-grid
-- "unique zero" representation for a four-point Fourier grid.
--
-- Agda source-written; kernel validation pending. These are cyclic
-- index and orbit counts, not C4/5 DFT/Parseval, Qω 4th/5th roots,
-- real NS velocity/Clay, optical clock or Monster representation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Full
import DASHI.Physics.Closure.R2P227729FourGridRetainedQuadraticParetoExact as Four
import DASHI.Physics.Closure.R2P227729AntipodalThirteenFiveOrbitFourierCutExact as Ant
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Source

fourGroupAntipode : Four.FourGridMode → Four.FourGridMode
fourGroupAntipode Four.fourMinusOne = Four.fourPlusOne
fourGroupAntipode Four.fourZero = Four.fourZero
fourGroupAntipode Four.fourPlusOne = Four.fourMinusOne
fourGroupAntipode Four.fourOuterTwo = Four.fourOuterTwo

fourGroupAntipodeInvolutive :
  (x : Four.FourGridMode) → fourGroupAntipode (fourGroupAntipode x) ≡ x
fourGroupAntipodeInvolutive Four.fourMinusOne = refl
fourGroupAntipodeInvolutive Four.fourZero = refl
fourGroupAntipodeInvolutive Four.fourPlusOne = refl
fourGroupAntipodeInvolutive Four.fourOuterTwo = refl

fourGridAntipode : Four.FourGridCube64 → Four.FourGridCube64
fourGridAntipode (Four.fourCube a b c) =
  Four.fourCube
    (fourGroupAntipode a)
    (fourGroupAntipode b)
    (fourGroupAntipode c)

fourGridAntipodeInvolutive :
  (g : Four.FourGridCube64) →
  fourGridAntipode (fourGridAntipode g) ≡ g
fourGridAntipodeInvolutive (Four.fourCube a b c)
  rewrite fourGroupAntipodeInvolutive a
        | fourGroupAntipodeInvolutive b
        | fourGroupAntipodeInvolutive c = refl

fourGroupAntipodeMatchesSignedFrequency :
  (k : M.FiveMode) →
  fourGroupAntipode (Four.foldFour k)
    ≡ Four.foldFour (Ant.negateWideAxis k)
fourGroupAntipodeMatchesSignedFrequency M.wideMinusTwo = refl
fourGroupAntipodeMatchesSignedFrequency M.wideMinusOne = refl
fourGroupAntipodeMatchesSignedFrequency M.wideZero = refl
fourGroupAntipodeMatchesSignedFrequency M.widePlusOne = refl
fourGroupAntipodeMatchesSignedFrequency M.widePlusTwo = refl

fourNyquistResidueIsSelfAntipodal :
  fourGroupAntipode Four.fourOuterTwo ≡ Four.fourOuterTwo
fourNyquistResidueIsSelfAntipodal = refl

fourGridCornerAtNyquistIsSelfAntipodal :
  fourGridAntipode
    (Four.fourCube Four.fourOuterTwo Four.fourZero Four.fourZero)
  ≡ Four.fourCube Four.fourOuterTwo Four.fourZero Four.fourZero
fourGridCornerAtNyquistIsSelfAntipodal = refl

fourFixedAxis : Four.FourGridMode → Bool
fourFixedAxis Four.fourMinusOne = false
fourFixedAxis Four.fourZero = true
fourFixedAxis Four.fourPlusOne = false
fourFixedAxis Four.fourOuterTwo = true

fourFixedCube : Four.FourGridCube64 → Bool
fourFixedCube (Four.fourCube a b c) =
  Full._&&B_ (Full._&&B_ (fourFixedAxis a) (fourFixedAxis b))
             (fourFixedAxis c)

allFourAxes : List Four.FourGridMode
allFourAxes = Four.fourMinusOne ∷ Four.fourZero ∷
              Four.fourPlusOne ∷ Four.fourOuterTwo ∷ []

allFourGridCubes : List Four.FourGridCube64
allFourGridCubes =
  I.concatMapL (λ a →
    I.concatMapL (λ b →
      I.mapL (λ c → Four.fourCube a b c) allFourAxes)
      allFourAxes) allFourAxes

fourCubeHas64Elements : I.lengthL allFourGridCubes ≡ 64
fourCubeHas64Elements = refl

fourCubeHasEightFixedAntipodes :
  I.countWhereL fourFixedCube allFourGridCubes ≡ 8
fourCubeHasEightFixedAntipodes = refl

fourCubeHas28NonfixedAntipodalPairs :
  64 ≡ 8 + 28 * 2
fourCubeHas28NonfixedAntipodalPairs = refl

fourCubeOrbitClasses36 : 8 + 28 ≡ 36
fourCubeOrbitClasses36 = refl

------------------------------------------------------------------------
-- C5^3: unlike C4, only the group identity k=0 is its own negative.
------------------------------------------------------------------------

fiveGroupAntipode : I.FiveGridMode → I.FiveGridMode
fiveGroupAntipode I.gridMinusTwo = I.gridPlusTwo
fiveGroupAntipode I.gridMinusOne = I.gridPlusOne
fiveGroupAntipode I.gridZero = I.gridZero
fiveGroupAntipode I.gridPlusOne = I.gridMinusOne
fiveGroupAntipode I.gridPlusTwo = I.gridMinusTwo

fiveGroupAntipodeInvolutive :
  (x : I.FiveGridMode) → fiveGroupAntipode (fiveGroupAntipode x) ≡ x
fiveGroupAntipodeInvolutive I.gridMinusTwo = refl
fiveGroupAntipodeInvolutive I.gridMinusOne = refl
fiveGroupAntipodeInvolutive I.gridZero = refl
fiveGroupAntipodeInvolutive I.gridPlusOne = refl
fiveGroupAntipodeInvolutive I.gridPlusTwo = refl

fiveGridAntipode : Full.GridCube125 → Full.GridCube125
fiveGridAntipode (Full.gridCube a b c) =
  Full.gridCube
    (fiveGroupAntipode a)
    (fiveGroupAntipode b)
    (fiveGroupAntipode c)

fiveGridAntipodeInvolutive :
  (g : Full.GridCube125) →
  fiveGridAntipode (fiveGridAntipode g) ≡ g
fiveGridAntipodeInvolutive (Full.gridCube a b c)
  rewrite fiveGroupAntipodeInvolutive a
        | fiveGroupAntipodeInvolutive b
        | fiveGroupAntipodeInvolutive c = refl

fiveGroupAntipodeMatchesSignedFrequency :
  (k : M.FiveMode) →
  fiveGroupAntipode (I.toGridFive k)
    ≡ I.toGridFive (Ant.negateWideAxis k)
fiveGroupAntipodeMatchesSignedFrequency M.wideMinusTwo = refl
fiveGroupAntipodeMatchesSignedFrequency M.wideMinusOne = refl
fiveGroupAntipodeMatchesSignedFrequency M.wideZero = refl
fiveGroupAntipodeMatchesSignedFrequency M.widePlusOne = refl
fiveGroupAntipodeMatchesSignedFrequency M.widePlusTwo = refl

fiveFixedAxis : I.FiveGridMode → Bool
fiveFixedAxis I.gridMinusTwo = false
fiveFixedAxis I.gridMinusOne = false
fiveFixedAxis I.gridZero = true
fiveFixedAxis I.gridPlusOne = false
fiveFixedAxis I.gridPlusTwo = false

fiveFixedCube : Full.GridCube125 → Bool
fiveFixedCube (Full.gridCube a b c) =
  Full._&&B_ (Full._&&B_ (fiveFixedAxis a) (fiveFixedAxis b))
             (fiveFixedAxis c)

allFiveAxes : List I.FiveGridMode
allFiveAxes = I.gridMinusTwo ∷ I.gridMinusOne ∷ I.gridZero ∷
              I.gridPlusOne ∷ I.gridPlusTwo ∷ []

allFiveGridCubes : List Full.GridCube125
allFiveGridCubes =
  I.concatMapL (λ a →
    I.concatMapL (λ b →
      I.mapL (λ c → Full.gridCube a b c) allFiveAxes)
      allFiveAxes) allFiveAxes

fiveCubeHas125Elements : I.lengthL allFiveGridCubes ≡ 125
fiveCubeHas125Elements = refl

fiveCubeHasOneFixedAntipode :
  I.countWhereL fiveFixedCube allFiveGridCubes ≡ 1
fiveCubeHasOneFixedAntipode = refl

fiveCubeHas62AntipodalPairs :
  125 ≡ 1 + 62 * 2
fiveCubeHas62AntipodalPairs = refl

fiveCubeOrbitClasses63 : 1 + 62 ≡ 63
fiveCubeOrbitClasses63 = refl

------------------------------------------------------------------------
-- Original odd-grid 13/27 source is inherited unchanged.
------------------------------------------------------------------------

originalC3CubeThirteenPairs :
  27 ≡ 1 + 13 * 2
originalC3CubeThirteenPairs =
  Source.ternaryCubeCountDecomposesAsCentrePlusThirteenPairs

-- CRITICAL physics gate: self-antipodal Fourier classes require real
-- coefficients for a real sampled field. This module proves only
-- the index-side fixed-point structure, not field reality/FFT.

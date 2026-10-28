module DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact where

------------------------------------------------------------------------
-- 2026-10-28: exact *finite* 27x27 mode-pair incidence max-cut.
--
-- REUSE, NOT DUPLICATE:
--   NSIntegerFourierLattice               actual integer Z^3 triads
--   NSTriadKNPeriodicIntegerTernary27SignChartRound529Exact  SIGN of Z^3
--   NSTriadKNPeriodicFourierTernaryTorusFibreBidiRound530Exact
--   Base369Ternary27HypervoxelFabricGeometryExact    voxel T3^3
--   R2P2ThreeModeBinaryTernaryNSAliasingCutExact    3-point MOD-3 folding
--
-- The SIGN of integer +2 is positive; the centred MOD-3 residue of +2
-- is negative. The sign-fibre quotient is NOT a modular group quotient.
--
-- There are exactly 27 input mode labels and 729 ORDERED pairs.
-- For each axis 7 of 9 pairs sum inside {-1,0,+1}. Thus 343 of 729
-- 3D ordered pair sums remain inside and 386 leave the retained cube.
-- This is about *indices*, not the nonzero value of NS interactions.
--
-- P3^3 path adjacency, C3^3 periodic adjacency, and Z^3 Fourier
-- convolution are different operations even if the 27 labels match.
-- Prior authors of pseudo-spectral dealiasing: Orszag and Patterson;
-- Lambert, Reneuve, Augier (arXiv:2603.08892, 2026).
-- No Monster 3B same-object promotion, no Clay or R2P2 proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as G
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicIntegerTernary27SignChartRound529Exact as Sign
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierTernaryTorusFibreBidiRound530Exact as SignSection
import DASHI.Physics.Closure.NSTriadKNPeriodicTorusBase369NormalizationRound531Exact as Torus
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- A genuine mode-label bijection onto the EXISTING 27-cube carrier.
------------------------------------------------------------------------

record ModeCube27 : Set where
  constructor modeCube
  field x y z : M.ThreeMode
open ModeCube27 public

modeCubeToVoxel : ModeCube27 → G.Ternary27Point
modeCubeToVoxel (modeCube x y z) =
  G.ternary27Point
    (M.modeToBalancedSSP x)
    (M.modeToBalancedSSP y)
    (M.modeToBalancedSSP z)

-- Transparent canonical inverse: one owner, no repeated local charts.
sspToMode : SSP.SSPTrit → M.ThreeMode
sspToMode SSP.sspNegOne = M.modeMinus
sspToMode SSP.sspZero = M.modeZero
sspToMode SSP.sspPosOne = M.modePlus

modeToSSPAfterRoundTrip :
  (t : SSP.SSPTrit) → M.modeToBalancedSSP (sspToMode t) ≡ t
modeToSSPAfterRoundTrip SSP.sspNegOne = refl
modeToSSPAfterRoundTrip SSP.sspZero = refl
modeToSSPAfterRoundTrip SSP.sspPosOne = refl

sspToModeAfterRoundTrip :
  (m : M.ThreeMode) → sspToMode (M.modeToBalancedSSP m) ≡ m
sspToModeAfterRoundTrip M.modeMinus = refl
sspToModeAfterRoundTrip M.modeZero = refl
sspToModeAfterRoundTrip M.modePlus = refl

-- Use canonical conversion rather than three copies of the above branch map.
voxelToModeCubeCanonical : G.Ternary27Point → ModeCube27
voxelToModeCubeCanonical (G.ternary27Point a b c) =
  modeCube (sspToMode a) (sspToMode b) (sspToMode c)

voxelModeRoundTrip :
  (v : G.Ternary27Point) →
  modeCubeToVoxel (voxelToModeCubeCanonical v) ≡ v
voxelModeRoundTrip (G.ternary27Point a b c)
  rewrite modeToSSPAfterRoundTrip a
        | modeToSSPAfterRoundTrip b
        | modeToSSPAfterRoundTrip c = refl

modeVoxelRoundTrip :
  (v : ModeCube27) →
  voxelToModeCubeCanonical (modeCubeToVoxel v) ≡ v
modeVoxelRoundTrip (modeCube a b c)
  rewrite sspToModeAfterRoundTrip a
        | sspToModeAfterRoundTrip b
        | sspToModeAfterRoundTrip c = refl

------------------------------------------------------------------------
-- Sign chart ≠ centred modulo-three sample residue. Same codomain.
------------------------------------------------------------------------

positiveTwoStillHasPositiveIntegerSign :
  Sign.integerSign529 (+ 2) ≡ SSP.sspPosOne
positiveTwoStillHasPositiveIntegerSign = refl

positiveTwoHasNegativeThreeSampleResidue :
  M.modeToBalancedSSP
    (M.periodicThreePointFold M.widePlusTwo) ≡ SSP.sspNegOne
positiveTwoHasNegativeThreeSampleResidue = refl

signAndResidueDisagreeOnPositiveTwo :
  Sign.integerSign529 (+ 2)
    ≡ M.modeToBalancedSSP
      (M.periodicThreePointFold M.widePlusTwo) → ⊥
signAndResidueDisagreeOnPositiveTwo ()

signedIntegerTriadPlusPlusStillPositive :
  Sign.observePeriodicMode529
    (Z3.addMode M.nsPlusOneX M.nsPlusOneX)
    ≡ G.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero
signedIntegerTriadPlusPlusStillPositive = refl

threeSamplePlusPlusAliasesNegative :
  M.threeAxisPeriodicallyAliasedPlusXSquare
    ≡ M.threeAxisBalancedModeCube M.modeMinus M.modeZero M.modeZero
threeSamplePlusPlusAliasesNegative =
  M.periodicThreeAxisPositiveXSquareWrapsToNegativeX

-- Source-owned sign observation has an existing section. It is not an
-- additive group homomorphism, since +1+1 represents +2, not -1.
canonicalSignSection :
  (v : G.Ternary27Point) →
  Sign.observePeriodicMode529
    (SignSection.periodicModeRepresentative530 v) ≡ v
canonicalSignSection = SignSection.periodicSignObservationSection530

------------------------------------------------------------------------
-- Existing periodic wraparound is NOT adjacency of the P3^3 path cube.
-- The published source of either adjacency is reused unmodified.
------------------------------------------------------------------------

periodicXAxisWraparoundExists :
  Torus.Base369PeriodicTorusAdjacent531
    (G.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero)
    (G.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero)
periodicXAxisWraparoundExists =
  Torus.periodicWraparoundLivesOnNormalizedCarrier531

pathXAxisWraparoundIsImpossible :
  G.HypervoxelAdjacent
    (G.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero)
    (G.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero)
  → ⊥
pathXAxisWraparoundIsImpossible ()

-- The explicit two-sided mode/voxel inverse also proves injectivity.
modeCubeToVoxelInjective :
  ∀ {a b : ModeCube27} →
  modeCubeToVoxel a ≡ modeCubeToVoxel b → a ≡ b
modeCubeToVoxelInjective {a} {b} eq =
  trans (sym (modeVoxelRoundTrip a))
    (trans (cong voxelToModeCubeCanonical eq)
           (modeVoxelRoundTrip b))

------------------------------------------------------------------------
-- REAL 27×27 PAIR ENUMERATION (not only 27*27 and 343+386 arithmetic).
------------------------------------------------------------------------

infixr 5 _++L_
_++L_ : ∀ {A : Set} → List A → List A → List A
[] ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f [] = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

concatMapL : ∀ {A B : Set} → (A → List B) → List A → List B
concatMapL f [] = []
concatMapL f (x ∷ xs) = f x ++L concatMapL f xs

lengthL : ∀ {A : Set} → List A → Nat
lengthL [] = 0
lengthL (_ ∷ xs) = 1 + lengthL xs

allMode3 : List M.ThreeMode
allMode3 = M.modeMinus ∷ M.modeZero ∷ M.modePlus ∷ []

cube27 : List ModeCube27
cube27 =
  concatMapL (λ a →
    concatMapL (λ b →
      mapL (λ c → modeCube a b c) allMode3) allMode3) allMode3

cube27HasExactly27Entries : lengthL cube27 ≡ 27
cube27HasExactly27Entries = refl

------------------------------------------------------------------------
-- Ordered dense indices: a full 27-rank list, not just cardinality.
-- rank is a list-position identifier, NOT a finite-field element.
------------------------------------------------------------------------

modeRank : M.ThreeMode → Nat
modeRank M.modeMinus = 0
modeRank M.modeZero = 1
modeRank M.modePlus = 2

cubeRank : ModeCube27 → Nat
cubeRank (modeCube a b c) =
  9 * modeRank a + 3 * modeRank b + modeRank c

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc remaining) =
  start ∷ rangeFrom (suc start) remaining

cube27RanksAreExactlyZeroThrough26 :
  mapL cubeRank cube27 ≡ rangeFrom 0 27
cube27RanksAreExactlyZeroThrough26 = refl

ModePair729 : Set
ModePair729 = ModeCube27 × ModeCube27

pair729 : List ModePair729
pair729 = concatMapL (λ a → mapL (λ b → a , b) cube27) cube27

orderedPairRank : ModePair729 → Nat
orderedPairRank (a , b) = 27 * cubeRank a + cubeRank b

orderedPairRanksAreExactlyZeroThrough728 :
  mapL orderedPairRank pair729 ≡ rangeFrom 0 729
orderedPairRanksAreExactlyZeroThrough728 = refl

pair729HasExactly729Entries : lengthL pair729 ≡ 729
pair729HasExactly729Entries = refl

_&&B_ : Bool → Bool → Bool
true &&B b = b
false &&B b = false

notB : Bool → Bool
notB true = false
notB false = true

-- A scalar sum is outside [-1,0,+1] exactly for (-1,-1) or (+1,+1).
axisSumInside : M.ThreeMode → M.ThreeMode → Bool
axisSumInside M.modeMinus M.modeMinus = false
axisSumInside M.modeMinus M.modeZero = true
axisSumInside M.modeMinus M.modePlus = true
axisSumInside M.modeZero M.modeMinus = true
axisSumInside M.modeZero M.modeZero = true
axisSumInside M.modeZero M.modePlus = true
axisSumInside M.modePlus M.modeMinus = true
axisSumInside M.modePlus M.modeZero = true
axisSumInside M.modePlus M.modePlus = false

insidePair27 : ModePair729 → Bool
insidePair27 ((modeCube x y z) , (modeCube x' y' z')) =
  (axisSumInside x x' &&B axisSumInside y y')
    &&B axisSumInside z z'

countWhereL : ∀ {A : Set} → (A → Bool) → List A → Nat
countWhereL test [] = 0
countWhereL test (x ∷ xs) with test x
... | true = 1 + countWhereL test xs
... | false = countWhereL test xs

oneAxisExactNinePairs :
  countWhereL
    (λ pair → axisSumInside (proj₁ pair)
                            (proj₂ pair))
    (concatMapL (λ a → mapL (λ b → a , b) allMode3) allMode3)
  ≡ 7
oneAxisExactNinePairs = refl

exact343InWindowPairs : countWhereL insidePair27 pair729 ≡ 343
exact343InWindowPairs = refl

exact386OutOfWindowPairs :
  countWhereL (λ pair → notB (insidePair27 pair)) pair729 ≡ 386
exact386OutOfWindowPairs = refl

exact729Partition : 343 + 386 ≡ lengthL pair729
exact729Partition = refl

-- Note: counted list contains all combinations by its explicit nested
-- construction. For Fin27/Fin729 bijective indexing and no duplicates,
-- use the canonical Fin27 ABI owner after its open-PR reverse proof lands.
-- We have NOT silently imported sibling PR #1386/#1390.

------------------------------------------------------------------------
-- Five-point integer-frequency *label* recovery for all nine pairs.
-- This is NOT a full DFT, Parseval or arbitrary-complex-coefficient theorem.
------------------------------------------------------------------------

data FiveGridMode : Set where
  gridMinusTwo gridMinusOne gridZero gridPlusOne gridPlusTwo : FiveGridMode

toGridFive : M.FiveMode → FiveGridMode
toGridFive M.wideMinusTwo = gridMinusTwo
toGridFive M.wideMinusOne = gridMinusOne
toGridFive M.wideZero = gridZero
toGridFive M.widePlusOne = gridPlusOne
toGridFive M.widePlusTwo = gridPlusTwo

fromGridFive : FiveGridMode → M.FiveMode
fromGridFive gridMinusTwo = M.wideMinusTwo
fromGridFive gridMinusOne = M.wideMinusOne
fromGridFive gridZero = M.wideZero
fromGridFive gridPlusOne = M.widePlusOne
fromGridFive gridPlusTwo = M.widePlusTwo

fiveGridModeRoundTrip :
  (w : M.FiveMode) → fromGridFive (toGridFive w) ≡ w
fiveGridModeRoundTrip M.wideMinusTwo = refl
fiveGridModeRoundTrip M.wideMinusOne = refl
fiveGridModeRoundTrip M.wideZero = refl
fiveGridModeRoundTrip M.widePlusOne = refl
fiveGridModeRoundTrip M.widePlusTwo = refl

fiveGridNoQuadraticModeFolding :
  (p q : M.ThreeMode) →
  fromGridFive (toGridFive (M.exactQuadraticModeSum p q))
    ≡ M.exactQuadraticModeSum p q
fiveGridNoQuadraticModeFolding p q =
  fiveGridModeRoundTrip (M.exactQuadraticModeSum p q)

-- A generic consumer after integer sum sees the identical output label
-- after five-grid recovery. This quantifies over arbitrary outcomes.
fiveGridPreservesEveryQuadraticLabelConsumer :
  ∀ {Output : Set} →
  (consumer : M.FiveMode → Output) →
  (p q : M.ThreeMode) →
  consumer (fromGridFive (toGridFive (M.exactQuadraticModeSum p q)))
    ≡ consumer (M.exactQuadraticModeSum p q)
fiveGridPreservesEveryQuadraticLabelConsumer consumer p q
  rewrite fiveGridNoQuadraticModeFolding p q = refl

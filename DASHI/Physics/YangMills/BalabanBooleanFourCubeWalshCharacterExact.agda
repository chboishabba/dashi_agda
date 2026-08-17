module DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977. DOI: 10.1007/978-1-4684-9458-7.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368. DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
--
-- Put the Walsh/Fourier character geometry on the SAME sixteen-element
-- Subset4 carrier already used by the Wilson Möbius decomposition, while
-- proving rather than assuming that the two transforms are different.
--
-- Symmetric difference is the additive C2^4 law.  The sixteen characters are
--
--     chi_A(S) = (-1)^{|A cap S|}.
--
-- Every nontrivial character row sums exactly to zero.  Consequently a pure
-- nontrivial sign-character sector has zero complete sign-orbit sum before
-- interval arithmetic.  This is the finite cancellation mechanism needed by
-- the Brillouin one-loop symmetry lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeMobiusExact as Mobius

false xor false = false
false xor true = true
true xor false = true
true xor true = false

false and right = false
true and right = right

xorCommutative : ∀ left right → left xor right ≡ right xor left
xorCommutative false false = refl
xorCommutative false true = refl
xorCommutative true false = refl
xorCommutative true true = refl

subsetFromBits : Bool → Bool → Bool → Bool → Cube.Subset4
subsetFromBits false false false false = Cube.empty
subsetFromBits true false false false = Cube.s0
subsetFromBits false true false false = Cube.s1
subsetFromBits false false true false = Cube.s2
subsetFromBits false false false true = Cube.s3
subsetFromBits true true false false = Cube.s01
subsetFromBits true false true false = Cube.s02
subsetFromBits true false false true = Cube.s03
subsetFromBits false true true false = Cube.s12
subsetFromBits false true false true = Cube.s13
subsetFromBits false false true true = Cube.s23
subsetFromBits true true true false = Cube.s012
subsetFromBits true true false true = Cube.s013
subsetFromBits true false true true = Cube.s023
subsetFromBits false true true true = Cube.s123
subsetFromBits true true true true = Cube.s0123

symmetricDifference : Cube.Subset4 → Cube.Subset4 → Cube.Subset4
symmetricDifference left right = subsetFromBits
  (Cube.contains Cube.slot0 left xor Cube.contains Cube.slot0 right)
  (Cube.contains Cube.slot1 left xor Cube.contains Cube.slot1 right)
  (Cube.contains Cube.slot2 left xor Cube.contains Cube.slot2 right)
  (Cube.contains Cube.slot3 left xor Cube.contains Cube.slot3 right)

symmetricDifferenceEmptyLeft : ∀ subset →
  symmetricDifference Cube.empty subset ≡ subset
symmetricDifferenceEmptyLeft Cube.empty = refl
symmetricDifferenceEmptyLeft Cube.s0 = refl
symmetricDifferenceEmptyLeft Cube.s1 = refl
symmetricDifferenceEmptyLeft Cube.s2 = refl
symmetricDifferenceEmptyLeft Cube.s3 = refl
symmetricDifferenceEmptyLeft Cube.s01 = refl
symmetricDifferenceEmptyLeft Cube.s02 = refl
symmetricDifferenceEmptyLeft Cube.s03 = refl
symmetricDifferenceEmptyLeft Cube.s12 = refl
symmetricDifferenceEmptyLeft Cube.s13 = refl
symmetricDifferenceEmptyLeft Cube.s23 = refl
symmetricDifferenceEmptyLeft Cube.s012 = refl
symmetricDifferenceEmptyLeft Cube.s013 = refl
symmetricDifferenceEmptyLeft Cube.s023 = refl
symmetricDifferenceEmptyLeft Cube.s123 = refl
symmetricDifferenceEmptyLeft Cube.s0123 = refl

symmetricDifferenceSelf : ∀ subset →
  symmetricDifference subset subset ≡ Cube.empty
symmetricDifferenceSelf Cube.empty = refl
symmetricDifferenceSelf Cube.s0 = refl
symmetricDifferenceSelf Cube.s1 = refl
symmetricDifferenceSelf Cube.s2 = refl
symmetricDifferenceSelf Cube.s3 = refl
symmetricDifferenceSelf Cube.s01 = refl
symmetricDifferenceSelf Cube.s02 = refl
symmetricDifferenceSelf Cube.s03 = refl
symmetricDifferenceSelf Cube.s12 = refl
symmetricDifferenceSelf Cube.s13 = refl
symmetricDifferenceSelf Cube.s23 = refl
symmetricDifferenceSelf Cube.s012 = refl
symmetricDifferenceSelf Cube.s013 = refl
symmetricDifferenceSelf Cube.s023 = refl
symmetricDifferenceSelf Cube.s123 = refl
symmetricDifferenceSelf Cube.s0123 = refl

symmetricDifferenceCommutative : ∀ left right →
  symmetricDifference left right ≡ symmetricDifference right left
symmetricDifferenceCommutative left right
  rewrite xorCommutative (Cube.contains Cube.slot0 left) (Cube.contains Cube.slot0 right)
        | xorCommutative (Cube.contains Cube.slot1 left) (Cube.contains Cube.slot1 right)
        | xorCommutative (Cube.contains Cube.slot2 left) (Cube.contains Cube.slot2 right)
        | xorCommutative (Cube.contains Cube.slot3 left) (Cube.contains Cube.slot3 right)
  = refl

parity4 : Bool → Bool → Bool → Bool → Bool
parity4 a b c d = a xor (b xor (c xor d))

intersectionParity : Cube.Subset4 → Cube.Subset4 → Bool
intersectionParity frequency point = parity4
  (Cube.contains Cube.slot0 frequency and Cube.contains Cube.slot0 point)
  (Cube.contains Cube.slot1 frequency and Cube.contains Cube.slot1 point)
  (Cube.contains Cube.slot2 frequency and Cube.contains Cube.slot2 point)
  (Cube.contains Cube.slot3 frequency and Cube.contains Cube.slot3 point)

one minusOne sixteen : ℚ
one = + 1 / 1
minusOne = - one
sixteen = + 16 / 1

sign : Bool → ℚ
sign false = one
sign true = minusOne

walshCharacter : Cube.Subset4 → Cube.Subset4 → ℚ
walshCharacter frequency point = sign (intersectionParity frequency point)

walshRowSum : Cube.Subset4 → ℚ
walshRowSum frequency =
  Sums.sumRational Cube.allSubsets4 (walshCharacter frequency)

trivialWalshRowSumExact : walshRowSum Cube.empty ≡ sixteen
trivialWalshRowSumExact = refl

data NontrivialFrequency : Cube.Subset4 → Set where
  n0 : NontrivialFrequency Cube.s0
  n1 : NontrivialFrequency Cube.s1
  n2 : NontrivialFrequency Cube.s2
  n3 : NontrivialFrequency Cube.s3
  n01 : NontrivialFrequency Cube.s01
  n02 : NontrivialFrequency Cube.s02
  n03 : NontrivialFrequency Cube.s03
  n12 : NontrivialFrequency Cube.s12
  n13 : NontrivialFrequency Cube.s13
  n23 : NontrivialFrequency Cube.s23
  n012 : NontrivialFrequency Cube.s012
  n013 : NontrivialFrequency Cube.s013
  n023 : NontrivialFrequency Cube.s023
  n123 : NontrivialFrequency Cube.s123
  n0123 : NontrivialFrequency Cube.s0123

nontrivialWalshRowSumZero : ∀ {frequency} →
  NontrivialFrequency frequency → walshRowSum frequency ≡ 0ℚ
nontrivialWalshRowSumZero n0 = refl
nontrivialWalshRowSumZero n1 = refl
nontrivialWalshRowSumZero n2 = refl
nontrivialWalshRowSumZero n3 = refl
nontrivialWalshRowSumZero n01 = refl
nontrivialWalshRowSumZero n02 = refl
nontrivialWalshRowSumZero n03 = refl
nontrivialWalshRowSumZero n12 = refl
nontrivialWalshRowSumZero n13 = refl
nontrivialWalshRowSumZero n23 = refl
nontrivialWalshRowSumZero n012 = refl
nontrivialWalshRowSumZero n013 = refl
nontrivialWalshRowSumZero n023 = refl
nontrivialWalshRowSumZero n123 = refl
nontrivialWalshRowSumZero n0123 = refl

characterSector : Cube.Subset4 → ℚ → Cube.Subset4 → ℚ
characterSector frequency amplitude point = walshCharacter frequency point * amplitude

characterSectorOrbitSum : Cube.Subset4 → ℚ → ℚ
characterSectorOrbitSum frequency amplitude =
  Sums.sumRational Cube.allSubsets4 (characterSector frequency amplitude)

nontrivialCharacterSectorOrbitSumVanishes :
  ∀ {frequency} → NontrivialFrequency frequency → ∀ amplitude →
  characterSectorOrbitSum frequency amplitude ≡ 0ℚ
nontrivialCharacterSectorOrbitSumVanishes n0 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n1 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n2 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n3 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n01 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n02 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n03 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n12 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n13 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n23 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n012 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n013 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n023 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n123 amplitude = ℚRing.solve-∀ amplitude
nontrivialCharacterSectorOrbitSumVanishes n0123 amplitude = ℚRing.solve-∀ amplitude

walshCoefficient : (Cube.Subset4 → ℚ) → Cube.Subset4 → ℚ
walshCoefficient value frequency =
  Sums.sumRational Cube.allSubsets4
    (λ point → walshCharacter frequency point * value point)

constantOne : Cube.Subset4 → ℚ
constantOne point = one

mobiusAndWalshAreNotTheSameTransform :
  Mobius.mobiusAtom constantOne Cube.s0 ≡ 0ℚ
mobiusAndWalshAreNotTheSameTransform = refl

constantOneWalshTrivialIsSixteen :
  walshCoefficient constantOne Cube.empty ≡ sixteen
constantOneWalshTrivialIsSixteen = refl

booleanFourCubeSymmetricDifferenceLevel : ProofLevel
booleanFourCubeSymmetricDifferenceLevel = machineChecked

booleanFourCubeWalshCharacterLevel : ProofLevel
booleanFourCubeWalshCharacterLevel = machineChecked

nontrivialWalshOrbitCancellationLevel : ProofLevel
nontrivialWalshOrbitCancellationLevel = machineChecked

mobiusWalshSeparationLevel : ProofLevel
mobiusWalshSeparationLevel = machineChecked

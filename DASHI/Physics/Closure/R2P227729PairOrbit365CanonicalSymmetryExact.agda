module DASHI.Physics.Closure.R2P227729PairOrbit365CanonicalSymmetryExact where

-- Original source owners: BalancedTernaryAntipodalOrbitExact,
-- R2P227729AntipodalThirteenFiveOrbitFourierCutExact,
-- R2P227729FourierObserverIncidenceExact, and source 729 pairing.
-- Serre finite C2-orbit counting is inherited mathematics.
-- New finite receipt: canonical orientation of SIMULTANEOUS inversion
-- of two Fourier input modes. Crucially this differs from quotienting
-- EACH input independently (which loses their relative orientation).
-- A 365-class pair index is not, by itself, an accelerated NS operator.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729AntipodalThirteenFiveOrbitFourierCutExact as Ant
import DASHI.Physics.Closure.R2P227729HermitianThirteenPairFourierCodecExact as Herm
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Conv
open import Data.Product using (proj₁; proj₂)

zeroCube : I.ModeCube27
zeroCube = I.modeCube M.modeZero M.modeZero M.modeZero

isZeroMode : M.ThreeMode → Bool
isZeroMode M.modeMinus = false
isZeroMode M.modeZero = true
isZeroMode M.modePlus = false

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

isZeroCube : I.ModeCube27 → Bool
isZeroCube (I.modeCube x y z) =
  isZeroMode x && isZeroMode y && isZeroMode z

isCentralPair : I.ModePair729 → Bool
isCentralPair (p , q) = isZeroCube p && isZeroCube q

-- Lexicographic orientation on six signed trits: first nonzero decides.
-- If the first input mode is zero, orientation is determined by the second.
positivePair : I.ModePair729 → Bool
positivePair (p , q) with isZeroCube p
... | true = Herm.positiveSide q
... | false = Herm.positiveSide p

canonicalPair : I.ModePair729 → I.ModePair729
canonicalPair pair with positivePair pair
... | true = pair
... | false = Ant.simultaneouslyNegateOrderedPair pair

-- Real computation on the existing complete list of 729 ordered pairs,
-- NOT only the arithmetic identity 1+364*2=729.
oneActualCentralPair :
  I.countWhereL isCentralPair I.pair729 ≡ 1
oneActualCentralPair = refl

actualPositivePairRepresentatives :
  I.countWhereL positivePair I.pair729 ≡ 365
actualPositivePairRepresentatives = refl

noncentralPairsSplitAs364SignedPairs :
  729 ≡ 1 + 364 * 2
noncentralPairsSplitAs364SignedPairs = refl

-- Pair orientation is compatible with the exact integer output only
-- when the ENTIRE ordered pair is negated. Independent input antipodes
-- have the proven nonfactorability counterexample in the source owner.
negatingBothInputModesNegatesTheirIntegerOutput :
  (pair : I.ModePair729) →
  Conv.exactPairOutput
    (proj₁ (Ant.simultaneouslyNegateOrderedPair pair))
    (proj₂ (Ant.simultaneouslyNegateOrderedPair pair))
    ≡ Ant.negateWideCube
        (Conv.exactPairOutput (proj₁ pair) (proj₂ pair))
negatingBothInputModesNegatesTheirIntegerOutput =
  Ant.orderedPairOutputCovariantUnderSimultaneousNegation

-- Explicit fail-closed statement: labels in the 365 classes do not
-- by themselves encode signed complex amplitudes or an NS interaction.
orbitClassCountDoesNotEstablishPhysicalNS : Bool
orbitClassCountDoesNotEstablishPhysicalNS = false

orbitClassCountDoesNotEstablishPhysicalNSIsFalse :
  orbitClassCountDoesNotEstablishPhysicalNS ≡ false
orbitClassCountDoesNotEstablishPhysicalNSIsFalse = refl

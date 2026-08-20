module DASHI.Moonshine.P11ElevenStateSymmetricSchreierNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- DASHI CONTRIBUTION
--
-- The preceding six-sector no-go might have suggested that the cure is merely
-- to go back to the full p=11 SO(3) weight-state carrier of dimension 11.
-- This file shows that an ORDINARY UNWEIGHTED SYMMETRIC equitable binary graph
-- quotient still cannot produce B_11(2).
--
-- Symmetric edge double counting requires fibre sizes L,R to obey
--
--   3 L = 2 R
--
-- because B01=3 and B10=2.  Hence L:R=2:3 and L+R must be divisible by five.
-- The full representation has eleven weight states, so no binary split of all
-- eleven unweighted vertices satisfies the balance.
--
-- Thus simply refining six sectors back to eleven weight labels does not repair
-- the geometric obstruction.  A successful producer needs stabilizer/orbifold
-- weighting or a genuinely different coset/ideal-class vertex set.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

data ElevenBinaryFiberSplit : Set where
  split0and11 : ElevenBinaryFiberSplit
  split1and10 : ElevenBinaryFiberSplit
  split2and9 : ElevenBinaryFiberSplit
  split3and8 : ElevenBinaryFiberSplit
  split4and7 : ElevenBinaryFiberSplit
  split5and6 : ElevenBinaryFiberSplit
  split6and5 : ElevenBinaryFiberSplit
  split7and4 : ElevenBinaryFiberSplit
  split8and3 : ElevenBinaryFiberSplit
  split9and2 : ElevenBinaryFiberSplit
  split10and1 : ElevenBinaryFiberSplit
  split11and0 : ElevenBinaryFiberSplit

leftSize : ElevenBinaryFiberSplit → Nat
leftSize split0and11 = 0
leftSize split1and10 = 1
leftSize split2and9 = 2
leftSize split3and8 = 3
leftSize split4and7 = 4
leftSize split5and6 = 5
leftSize split6and5 = 6
leftSize split7and4 = 7
leftSize split8and3 = 8
leftSize split9and2 = 9
leftSize split10and1 = 10
leftSize split11and0 = 11

rightSize : ElevenBinaryFiberSplit → Nat
rightSize split0and11 = 11
rightSize split1and10 = 10
rightSize split2and9 = 9
rightSize split3and8 = 8
rightSize split4and7 = 7
rightSize split5and6 = 6
rightSize split6and5 = 5
rightSize split7and4 = 4
rightSize split8and3 = 3
rightSize split9and2 = 2
rightSize split10and1 = 1
rightSize split11and0 = 0

splitTotalIsEleven : (split : ElevenBinaryFiberSplit) →
  leftSize split + rightSize split ≡ 11
splitTotalIsEleven split0and11 = refl
splitTotalIsEleven split1and10 = refl
splitTotalIsEleven split2and9 = refl
splitTotalIsEleven split3and8 = refl
splitTotalIsEleven split4and7 = refl
splitTotalIsEleven split5and6 = refl
splitTotalIsEleven split6and5 = refl
splitTotalIsEleven split7and4 = refl
splitTotalIsEleven split8and3 = refl
splitTotalIsEleven split9and2 = refl
splitTotalIsEleven split10and1 = refl
splitTotalIsEleven split11and0 = refl

brandtEll2UnweightedBalance : ElevenBinaryFiberSplit → Set
brandtEll2UnweightedBalance split =
  3 * leftSize split ≡ 2 * rightSize split

brandtEll2BalanceImpossible :
  (split : ElevenBinaryFiberSplit) →
  brandtEll2UnweightedBalance split → ⊥
brandtEll2BalanceImpossible split0and11 ()
brandtEll2BalanceImpossible split1and10 ()
brandtEll2BalanceImpossible split2and9 ()
brandtEll2BalanceImpossible split3and8 ()
brandtEll2BalanceImpossible split4and7 ()
brandtEll2BalanceImpossible split5and6 ()
brandtEll2BalanceImpossible split6and5 ()
brandtEll2BalanceImpossible split7and4 ()
brandtEll2BalanceImpossible split8and3 ()
brandtEll2BalanceImpossible split9and2 ()
brandtEll2BalanceImpossible split10and1 ()
brandtEll2BalanceImpossible split11and0 ()

record UnweightedSymmetricElevenToP11BrandtData : Set where
  field
    fibreSplit : ElevenBinaryFiberSplit
    crossingEdgeDoubleCount : brandtEll2UnweightedBalance fibreSplit

open UnweightedSymmetricElevenToP11BrandtData public

unweightedSymmetricElevenToP11BrandtImpossible :
  UnweightedSymmetricElevenToP11BrandtData → ⊥
unweightedSymmetricElevenToP11BrandtImpossible data =
  brandtEll2BalanceImpossible
    (fibreSplit data)
    (crossingEdgeDoubleCount data)

record P11ElevenStateSymmetricSchreierNoGoBoundary : Set where
  field
    allTwelveBinaryFiberSizesEnumerated : Bool
    allTwelveBinaryFiberSizesEnumeratedIsTrue :
      allTwelveBinaryFiberSizesEnumerated ≡ true

    noUnweightedSymmetricElevenVertexBalanceForB11ell2 : Bool
    noUnweightedSymmetricElevenVertexBalanceForB11ell2IsTrue :
      noUnweightedSymmetricElevenVertexBalanceForB11ell2 ≡ true

    refiningSixSectorsToElevenUnweightedStatesSolvesBalance : Bool
    refiningSixSectorsToElevenUnweightedStatesSolvesBalanceIsFalse :
      refiningSixSectorsToElevenUnweightedStatesSolvesBalance ≡ false

    weightedOrDifferentCosetCarrierStillOpen : Bool
    weightedOrDifferentCosetCarrierStillOpenIsTrue :
      weightedOrDifferentCosetCarrierStillOpen ≡ true

canonicalP11ElevenStateSymmetricSchreierNoGoBoundary :
  P11ElevenStateSymmetricSchreierNoGoBoundary
canonicalP11ElevenStateSymmetricSchreierNoGoBoundary =
  record
    { allTwelveBinaryFiberSizesEnumerated = true
    ; allTwelveBinaryFiberSizesEnumeratedIsTrue = refl
    ; noUnweightedSymmetricElevenVertexBalanceForB11ell2 = true
    ; noUnweightedSymmetricElevenVertexBalanceForB11ell2IsTrue = refl
    ; refiningSixSectorsToElevenUnweightedStatesSolvesBalance = false
    ; refiningSixSectorsToElevenUnweightedStatesSolvesBalanceIsFalse = refl
    ; weightedOrDifferentCosetCarrierStillOpen = true
    ; weightedOrDifferentCosetCarrierStillOpenIsTrue = refl
    }

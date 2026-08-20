module DASHI.Moonshine.P11SixSectorSymmetricSchreierNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- DASHI CONTRIBUTION
--
-- Strengthen the p=11 six-sector falsifier from one particular binary lens to
-- every UNWEIGHTED SYMMETRIC equitable binary quotient of a six-vertex graph.
--
-- For an ordinary undirected/symmetric finite graph, double-counting crossing
-- edges between quotient fibres F0,F1 gives the necessary balance law
--
--   |F0| * B01 = |F1| * B10.
--
-- The p=11 ell=2 Brandt quotient has B01=3 and B10=2, so any such unweighted
-- quotient must satisfy
--
--   3 |F0| = 2 |F1|.
--
-- Thus the fibre sizes have ratio 2:3 and their total is a multiple of five.
-- The actual matched-dihedral carrier has SIX sectors, so no binary partition
-- of those six unweighted vertices can satisfy the required balance.
--
-- This does NOT rule out weighted/orbifold Schreier geometry.  Indeed the
-- arithmetic Brandt carrier itself has stabilizer-derived weights (2,3), which
-- is precisely the structure an unweighted six-sector model is missing.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Every possible cardinality split of six vertices into two labelled fibres.
------------------------------------------------------------------------

data SixBinaryFiberSplit : Set where
  split0and6 : SixBinaryFiberSplit
  split1and5 : SixBinaryFiberSplit
  split2and4 : SixBinaryFiberSplit
  split3and3 : SixBinaryFiberSplit
  split4and2 : SixBinaryFiberSplit
  split5and1 : SixBinaryFiberSplit
  split6and0 : SixBinaryFiberSplit

leftSize : SixBinaryFiberSplit → Nat
leftSize split0and6 = 0
leftSize split1and5 = 1
leftSize split2and4 = 2
leftSize split3and3 = 3
leftSize split4and2 = 4
leftSize split5and1 = 5
leftSize split6and0 = 6

rightSize : SixBinaryFiberSplit → Nat
rightSize split0and6 = 6
rightSize split1and5 = 5
rightSize split2and4 = 4
rightSize split3and3 = 3
rightSize split4and2 = 2
rightSize split5and1 = 1
rightSize split6and0 = 0

splitTotalIsSix : (split : SixBinaryFiberSplit) →
  leftSize split + rightSize split ≡ 6
splitTotalIsSix split0and6 = refl
splitTotalIsSix split1and5 = refl
splitTotalIsSix split2and4 = refl
splitTotalIsSix split3and3 = refl
splitTotalIsSix split4and2 = refl
splitTotalIsSix split5and1 = refl
splitTotalIsSix split6and0 = refl

------------------------------------------------------------------------
-- Required unweighted symmetric balance for B_11(2): 3 L = 2 R.
-- No split of six satisfies it.
------------------------------------------------------------------------

brandtEll2UnweightedBalance : SixBinaryFiberSplit → Set
brandtEll2UnweightedBalance split =
  3 * leftSize split ≡ 2 * rightSize split

brandtEll2BalanceImpossible :
  (split : SixBinaryFiberSplit) →
  brandtEll2UnweightedBalance split → ⊥
brandtEll2BalanceImpossible split0and6 ()
brandtEll2BalanceImpossible split1and5 ()
brandtEll2BalanceImpossible split2and4 ()
brandtEll2BalanceImpossible split3and3 ()
brandtEll2BalanceImpossible split4and2 ()
brandtEll2BalanceImpossible split5and1 ()
brandtEll2BalanceImpossible split6and0 ()

------------------------------------------------------------------------
-- Necessary numerical surface for an ordinary symmetric equitable quotient.
-- A future actual graph theorem may construct this record from edge reversal;
-- the impossibility below then closes immediately.
------------------------------------------------------------------------

record UnweightedSymmetricSixToP11BrandtData : Set where
  field
    fibreSplit : SixBinaryFiberSplit
    crossingEdgeDoubleCount : brandtEll2UnweightedBalance fibreSplit

open UnweightedSymmetricSixToP11BrandtData public

unweightedSymmetricSixToP11BrandtImpossible :
  UnweightedSymmetricSixToP11BrandtData → ⊥
unweightedSymmetricSixToP11BrandtImpossible data =
  brandtEll2BalanceImpossible
    (fibreSplit data)
    (crossingEdgeDoubleCount data)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record P11SixSectorSymmetricSchreierNoGoBoundary : Set where
  field
    allSevenBinaryFiberSizesEnumerated : Bool
    allSevenBinaryFiberSizesEnumeratedIsTrue :
      allSevenBinaryFiberSizesEnumerated ≡ true

    noUnweightedSymmetricSixVertexBalanceForB11ell2 : Bool
    noUnweightedSymmetricSixVertexBalanceForB11ell2IsTrue :
      noUnweightedSymmetricSixVertexBalanceForB11ell2 ≡ true

    naturalOneVsFiveOnlyNoGo : Bool
    naturalOneVsFiveOnlyNoGoIsFalse : naturalOneVsFiveOnlyNoGo ≡ false

    weightedOrbifoldSchreierGeometryRuledOut : Bool
    weightedOrbifoldSchreierGeometryRuledOutIsFalse :
      weightedOrbifoldSchreierGeometryRuledOut ≡ false

    fullElevenWeightStateGeometryRuledOut : Bool
    fullElevenWeightStateGeometryRuledOutIsFalse :
      fullElevenWeightStateGeometryRuledOut ≡ false

canonicalP11SixSectorSymmetricSchreierNoGoBoundary :
  P11SixSectorSymmetricSchreierNoGoBoundary
canonicalP11SixSectorSymmetricSchreierNoGoBoundary =
  record
    { allSevenBinaryFiberSizesEnumerated = true
    ; allSevenBinaryFiberSizesEnumeratedIsTrue = refl
    ; noUnweightedSymmetricSixVertexBalanceForB11ell2 = true
    ; noUnweightedSymmetricSixVertexBalanceForB11ell2IsTrue = refl
    ; naturalOneVsFiveOnlyNoGo = false
    ; naturalOneVsFiveOnlyNoGoIsFalse = refl
    ; weightedOrbifoldSchreierGeometryRuledOut = false
    ; weightedOrbifoldSchreierGeometryRuledOutIsFalse = refl
    ; fullElevenWeightStateGeometryRuledOut = false
    ; fullElevenWeightStateGeometryRuledOutIsFalse = refl
    }

module DASHI.Biology.Physical.BiologicalSharedFiniteVectorTransferExact where

-- One shared indexed vector material inventory.
-- Transfer debits the selected SOURCE Fin index and credits the selected
-- TARGET Fin index (or stays put for absent source and same endpoints).
-- All state coordinates are in the SAME vector. No per-edge copies.
-- Proves total conservation for EVERY pair of indices at arbitrary size,
-- and every controlled sequence of such indexed transfers.
--
-- The original 54-bond hypervoxel geometry must separately supply its
-- genuine point -> Fin 27 indexing before physical route identity is paid.

open import DASHI.Core.Prelude

import Data.Vec.Base as V
import Data.Fin.Base as F
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Grid
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube

creditAt : ∀ {n} → F.Fin n → V.Vec Nat n → V.Vec Nat n
creditAt F.zero (V._∷_ a xs) = V._∷_ (suc a) xs
creditAt (F.suc i) (V._∷_ a xs) =
  V._∷_ a (creditAt i xs)

creditIncreasesTotalByOne :
  ∀ {n} (index : F.Fin n) (xs : V.Vec Nat n) →
  V.sum (creditAt index xs) ≡ suc (V.sum xs)
creditIncreasesTotalByOne F.zero (V._∷_ a xs) = refl
creditIncreasesTotalByOne (F.suc index) (V._∷_ a xs) =
  trans
    (cong (λ k → a + k) (creditIncreasesTotalByOne index xs))
    (+-suc a (V.sum xs))

debitAt : ∀ {n} → F.Fin n → V.Vec Nat n → V.Vec Nat n
debitAt F.zero (V._∷_ zero xs) = V._∷_ zero xs
debitAt F.zero (V._∷_ (suc a) xs) = V._∷_ a xs
debitAt (F.suc index) (V._∷_ a xs) =
  V._∷_ a (debitAt index xs)

successfulDebitDecreasesTotalByOne :
  ∀ {n} (index : F.Fin n) (xs : V.Vec Nat n) (k : Nat) →
  V.lookup xs index ≡ suc k →
  suc (V.sum (debitAt index xs)) ≡ V.sum xs
successfulDebitDecreasesTotalByOne F.zero (V._∷_ zero xs) k ()
successfulDebitDecreasesTotalByOne F.zero (V._∷_ (suc a) xs) k proof =
  refl
successfulDebitDecreasesTotalByOne (F.suc index) (V._∷_ a xs) k proof =
  trans
    (sym (+-suc a (V.sum (debitAt index xs))))
    (cong (λ n → a + n)
      (successfulDebitDecreasesTotalByOne index xs k proof))

-- Source/target are arbitrary indices. Equal indices are stationary.
transferOne :
  ∀ {n} →
  F.Fin n → F.Fin n → V.Vec Nat n → V.Vec Nat n
transferOne F.zero F.zero (V._∷_ a xs) = V._∷_ a xs
transferOne F.zero (F.suc j) (V._∷_ zero xs) =
  V._∷_ zero xs
transferOne F.zero (F.suc j) (V._∷_ (suc a) xs) =
  V._∷_ a (creditAt j xs)
transferOne (F.suc i) F.zero (V._∷_ a xs)
  with V.lookup xs i
... | zero = V._∷_ a xs
... | suc k = V._∷_ (suc a) (debitAt i xs)
transferOne (F.suc i) (F.suc j) (V._∷_ a xs) =
  V._∷_ a (transferOne i j xs)

everyDirectedPairConservesSharedInventory :
  ∀ {n}
  (source destination : F.Fin n)
  (xs : V.Vec Nat n) →
  V.sum (transferOne source destination xs) ≡ V.sum xs
everyDirectedPairConservesSharedInventory
  F.zero F.zero (V._∷_ a xs) = refl
everyDirectedPairConservesSharedInventory
  F.zero (F.suc j) (V._∷_ zero xs) = refl
everyDirectedPairConservesSharedInventory
  F.zero (F.suc j) (V._∷_ (suc a) xs) =
  trans
    (cong (λ n → a + n) (creditIncreasesTotalByOne j xs))
    (+-suc a (V.sum xs))
everyDirectedPairConservesSharedInventory
  (F.suc i) F.zero (V._∷_ a xs)
  with V.lookup xs i
... | zero = refl
... | suc k =
  trans
    (sym (+-suc a (V.sum (debitAt i xs))))
    (cong (λ n → a + n)
      (successfulDebitDecreasesTotalByOne i xs k refl))
everyDirectedPairConservesSharedInventory
  (F.suc i) (F.suc j) (V._∷_ a xs) =
  cong (λ n → a + n)
    (everyDirectedPairConservesSharedInventory i j xs)

-- Physically chronological: first list element is applied first.
runTransfers :
  ∀ {n} →
  List (F.Fin n × F.Fin n) →
  V.Vec Nat n → V.Vec Nat n
runTransfers [] xs = xs
runTransfers ((source , destination) ∷ rest) xs =
  runTransfers rest (transferOne source destination xs)

allSharedVectorTransportHistoriesConserve :
  ∀ {n}
  (actions : List (F.Fin n × F.Fin n))
  (xs : V.Vec Nat n) →
  V.sum (runTransfers actions xs) ≡ V.sum xs
allSharedVectorTransportHistoriesConserve [] xs = refl
allSharedVectorTransportHistoriesConserve
  ((source , destination) ∷ rest) xs =
  trans
    (allSharedVectorTransportHistoriesConserve rest
      (transferOne source destination xs))
    (everyDirectedPairConservesSharedInventory
      source destination xs)

-- Direct specialization to all 27 SHARED cells. A Fin 27 pair
-- is not automatically an actual 3D nearest-neighbour connection:
-- the next geometric weld must prove each supplied directed
-- physical edge matches Grid.bondStart / Grid.bondEnd.
all27SharedSitesConserve :
  (actions : List (F.Fin 27 × F.Fin 27))
  (xs : V.Vec Nat 27) →
  V.sum (runTransfers actions xs) ≡ V.sum xs
all27SharedSitesConserve = allSharedVectorTransportHistoriesConserve

record Original54BondIndexing : Set where
  field
    pointIndex : Cube.Ternary27Point → F.Fin 27
    sourceIndex : Grid.PositiveBond → F.Fin 27
    targetIndex : Grid.PositiveBond → F.Fin 27
    indexesOriginalSource :
      (edge : Grid.PositiveBond) →
      sourceIndex edge ≡ pointIndex (Grid.bondStart edge)
    indexesOriginalTarget :
      (edge : Grid.PositiveBond) →
      targetIndex edge ≡ pointIndex (Grid.bondEnd edge)

open Original54BondIndexing public

originalBondForwardAction :
  Original54BondIndexing →
  Grid.PositiveBond → (F.Fin 27 × F.Fin 27)
originalBondForwardAction geometry bond =
  sourceIndex geometry bond , targetIndex geometry bond

originalBondReverseAction :
  Original54BondIndexing →
  Grid.PositiveBond → (F.Fin 27 × F.Fin 27)
originalBondReverseAction geometry bond =
  targetIndex geometry bond , sourceIndex geometry bond

forwardOriginalBondConserves :
  (geometry : Original54BondIndexing)
  (bond : Grid.PositiveBond)
  (state : V.Vec Nat 27) →
  V.sum (transferOne
    (sourceIndex geometry bond)
    (targetIndex geometry bond) state)
    ≡ V.sum state
forwardOriginalBondConserves geometry bond state =
  everyDirectedPairConservesSharedInventory
    (sourceIndex geometry bond)
    (targetIndex geometry bond) state

-- This universal theorem now covers any selection/ordering of real
-- bond indices under one shared 27-site conservation law. Constructing
-- an independently verified original pointIndex remains an obligation.
allOriginalIndexedBondHistoriesConserve :
  (geometry : Original54BondIndexing)
  (actions : List (F.Fin 27 × F.Fin 27))
  (state : V.Vec Nat 27) →
  V.sum (runTransfers actions state) ≡ V.sum state
allOriginalIndexedBondHistoriesConserve geometry actions state =
  all27SharedSitesConserve actions state

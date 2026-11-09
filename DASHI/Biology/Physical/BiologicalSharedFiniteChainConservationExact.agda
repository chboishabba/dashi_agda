module DASHI.Biology.Physical.BiologicalSharedFiniteChainConservationExact where

-- A single shared list of material amounts, with arbitrary-length
-- exact conservative nearest-entry transfer and all-history proofs.
-- Generalizes the original three-compartment shared-state witness.
-- The index here is a linear-chain coordinate; the separate original
-- 54-bond 3D grid owner must supply any non-linear edge mapping.

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.BiologicalSharedChainFiniteVolumeExact as Chain
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Cube

sumInventory : List Nat → Nat
sumInventory [] = 0
sumInventory (x ∷ xs) = x + sumInventory xs

numberOfSites : List Nat → Nat
numberOfSites [] = 0
numberOfSites (_ ∷ xs) = suc (numberOfSites xs)

-- Each transfer debits position k and credits position k+1.
-- If either position is absent or source is empty, it is stationary.
moveFirstPair : List Nat → List Nat
moveFirstPair [] = []
moveFirstPair (a ∷ []) = a ∷ []
moveFirstPair (zero ∷ b ∷ rest) = zero ∷ b ∷ rest
moveFirstPair ((suc a) ∷ b ∷ rest) = a ∷ suc b ∷ rest

moveFirstPairConserves :
  (sites : List Nat) →
  sumInventory (moveFirstPair sites) ≡ sumInventory sites
moveFirstPairConserves [] = refl
moveFirstPairConserves (a ∷ []) = refl
moveFirstPairConserves (zero ∷ b ∷ rest) = refl
moveFirstPairConserves ((suc a) ∷ b ∷ rest) =
  +-suc a (b + sumInventory rest)

moveFirstPairPreservesSiteCount :
  (sites : List Nat) →
  numberOfSites (moveFirstPair sites) ≡ numberOfSites sites
moveFirstPairPreservesSiteCount [] = refl
moveFirstPairPreservesSiteCount (a ∷ []) = refl
moveFirstPairPreservesSiteCount (zero ∷ b ∷ rest) = refl
moveFirstPairPreservesSiteCount ((suc a) ∷ b ∷ rest) = refl

moveAtIndex : Nat → List Nat → List Nat
moveAtIndex zero sites = moveFirstPair sites
moveAtIndex (suc n) [] = []
moveAtIndex (suc n) (a ∷ rest) = a ∷ moveAtIndex n rest

moveAtIndexConserves :
  (index : Nat) (sites : List Nat) →
  sumInventory (moveAtIndex index sites) ≡ sumInventory sites
moveAtIndexConserves zero sites = moveFirstPairConserves sites
moveAtIndexConserves (suc n) [] = refl
moveAtIndexConserves (suc n) (a ∷ rest) =
  cong (λ k → a + k) (moveAtIndexConserves n rest)

moveAtIndexPreservesSiteCount :
  (index : Nat) (sites : List Nat) →
  numberOfSites (moveAtIndex index sites) ≡ numberOfSites sites
moveAtIndexPreservesSiteCount zero sites =
  moveFirstPairPreservesSiteCount sites
moveAtIndexPreservesSiteCount (suc n) [] = refl
moveAtIndexPreservesSiteCount (suc n) (a ∷ rest) =
  cong suc (moveAtIndexPreservesSiteCount n rest)

-- Chronological action words of arbitrary length.
runSharedSites : List Nat → List Nat → List Nat
runSharedSites [] sites = sites
runSharedSites (index ∷ rest) sites =
  runSharedSites rest (moveAtIndex index sites)

everySharedTransportHistoryConserves :
  (indices : List Nat) (sites : List Nat) →
  sumInventory (runSharedSites indices sites) ≡ sumInventory sites
everySharedTransportHistoryConserves [] sites = refl
everySharedTransportHistoryConserves (index ∷ rest) sites =
  trans
    (everySharedTransportHistoryConserves rest
      (moveAtIndex index sites))
    (moveAtIndexConserves index sites)

everySharedTransportHistoryPreservesSiteCount :
  (indices : List Nat) (sites : List Nat) →
  numberOfSites (runSharedSites indices sites)
    ≡ numberOfSites sites
everySharedTransportHistoryPreservesSiteCount [] sites = refl
everySharedTransportHistoryPreservesSiteCount (index ∷ rest) sites =
  trans
    (everySharedTransportHistoryPreservesSiteCount rest
      (moveAtIndex index sites))
    (moveAtIndexPreservesSiteCount index sites)

zeroSites : Nat → List Nat
zeroSites zero = []
zeroSites (suc n) = 0 ∷ zeroSites n

zeroSitesHaveRequestedLength :
  (n : Nat) → numberOfSites (zeroSites n) ≡ n
zeroSitesHaveRequestedLength zero = refl
zeroSitesHaveRequestedLength (suc n) =
  cong suc (zeroSitesHaveRequestedLength n)

original27SharedCells : List Nat
original27SharedCells = zeroSites 27

original27SharedCellCount :
  numberOfSites original27SharedCells ≡ 27
original27SharedCellCount = zeroSitesHaveRequestedLength 27

everyTransportHistoryKeeps27Cells :
  (indices : List Nat) →
  numberOfSites (runSharedSites indices original27SharedCells) ≡ 27
everyTransportHistoryKeeps27Cells indices =
  trans
    (everySharedTransportHistoryPreservesSiteCount indices
      original27SharedCells)
    original27SharedCellCount

-- Separate geometric proof owner: 54 real 3D nearest-neighbour bonds.
-- The indexed linear chain above is NOT asserted to implement all of
-- these 54 edges until a source-specific bond-to-index update is built.
originalNonperiodicBondCount :
  Cube.countList Cube.allPositiveBonds ≡ 54
originalNonperiodicBondCount = Cube.completeBondCount

originalThreeCompartmentCarrier : Set
originalThreeCompartmentCarrier = Chain.SharedChain3

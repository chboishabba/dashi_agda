module DASHI.Biology.Physical.BiologicalSharedChainFiniteVolumeExact where

-- First concrete SHARED-STATE conservative transport operator.
-- Three distinct ordered compartments share ONE inventory, not a
-- separately duplicated two-site IonPairState for every transport edge.
-- Source: Turing (1952) reaction-diffusion; existing DASHI finite
-- electrodiffusive transfer and open-system material balance owners.
-- The unit-step is a normalized discrete event, NOT a measured BH4,
-- tissue, vascular or PNP constitutive rate.

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.FiniteElectrodiffusiveMovingBoundaryExact as Transport
import DASHI.Biology.Physical.FiniteReactionDiffusionConservationExact as Reaction

record SharedChain3 : Set where
  constructor sharedChain3
  field
    sourcePool middlePool targetPool : Nat

open SharedChain3 public

totalSharedInventory : SharedChain3 → Nat
totalSharedInventory (sharedChain3 a b c) = a + (b + c)

-- A -> B -> C. Both edges debit/credit the SAME middlePool.
flowSourceToMiddle : SharedChain3 → SharedChain3
flowSourceToMiddle (sharedChain3 zero b c) = sharedChain3 zero b c
flowSourceToMiddle (sharedChain3 (suc a) b c) =
  sharedChain3 a (suc b) c

flowMiddleToTarget : SharedChain3 → SharedChain3
flowMiddleToTarget (sharedChain3 a zero c) = sharedChain3 a zero c
flowMiddleToTarget (sharedChain3 a (suc b) c) =
  sharedChain3 a b (suc c)

-- A disconnected edge has no transfer, even if upstream supply exists.
data PermittedChainAction : Set where
  noFlow : PermittedChainAction
  sourceToMiddle : PermittedChainAction
  middleToTarget : PermittedChainAction
  externalSupply : Nat → PermittedChainAction

supplyIntoSource : Nat → SharedChain3 → SharedChain3
supplyIntoSource q (sharedChain3 a b c) =
  sharedChain3 (q + a) b c

physicalStep : PermittedChainAction → SharedChain3 → SharedChain3
physicalStep noFlow x = x
physicalStep sourceToMiddle x = flowSourceToMiddle x
physicalStep middleToTarget x = flowMiddleToTarget x
physicalStep (externalSupply q) x = supplyIntoSource q x

sourceToMiddleConservesSharedInventory :
  (x : SharedChain3) →
  totalSharedInventory (flowSourceToMiddle x)
    ≡ totalSharedInventory x
sourceToMiddleConservesSharedInventory (sharedChain3 zero b c) = refl
sourceToMiddleConservesSharedInventory (sharedChain3 (suc a) b c)
  = +-suc a (b + c)

middleToTargetConservesSharedInventory :
  (x : SharedChain3) →
  totalSharedInventory (flowMiddleToTarget x)
    ≡ totalSharedInventory x
middleToTargetConservesSharedInventory (sharedChain3 a zero c) = refl
middleToTargetConservesSharedInventory (sharedChain3 a (suc b) c)
  = cong (λ v → a + v) (+-suc b c)

supplyBalance :
  (q : Nat) (x : SharedChain3) →
  totalSharedInventory (supplyIntoSource q x)
    ≡ totalSharedInventory x + q
supplyBalance q (sharedChain3 a b c) =
  trans (+-assoc q a (b + c))
        (+-comm q (a + (b + c)))

injectedSupply : PermittedChainAction → Nat
injectedSupply noFlow = 0
injectedSupply sourceToMiddle = 0
injectedSupply middleToTarget = 0
injectedSupply (externalSupply q) = q

physicalStepBalance :
  (action : PermittedChainAction)
  (x : SharedChain3) →
  totalSharedInventory (physicalStep action x)
    ≡ totalSharedInventory x + injectedSupply action
physicalStepBalance noFlow x =
  sym (+-identityʳ (totalSharedInventory x))
physicalStepBalance sourceToMiddle x =
  trans (sourceToMiddleConservesSharedInventory x)
        (sym (+-identityʳ (totalSharedInventory x)))
physicalStepBalance middleToTarget x =
  trans (middleToTargetConservesSharedInventory x)
        (sym (+-identityʳ (totalSharedInventory x)))
physicalStepBalance (externalSupply q) x = supplyBalance q x

-- Left-to-right chronology: the head is executed first.
physicalRun : List PermittedChainAction → SharedChain3 → SharedChain3
physicalRun [] state = state
physicalRun (action ∷ rest) state =
  physicalRun rest (physicalStep action state)

totalInjectedSupply : List PermittedChainAction → Nat
totalInjectedSupply [] = 0
totalInjectedSupply (action ∷ rest) =
  injectedSupply action + totalInjectedSupply rest

allControlledHistoriesRespectOpenBalance :
  (actions : List PermittedChainAction)
  (state : SharedChain3) →
  totalSharedInventory (physicalRun actions state)
    ≡ totalSharedInventory state + totalInjectedSupply actions
allControlledHistoriesRespectOpenBalance [] state =
  sym (+-identityʳ (totalSharedInventory state))
allControlledHistoriesRespectOpenBalance (action ∷ rest) state =
  trans
    (allControlledHistoriesRespectOpenBalance rest
      (physicalStep action state))
    (trans
      (cong (λ n → n + totalInjectedSupply rest)
        (physicalStepBalance action state))
      (+-assoc (totalSharedInventory state)
        (injectedSupply action) (totalInjectedSupply rest)))

-- A genuine location-sensitive countermodel for the same total.
originalInventory : SharedChain3
originalInventory = sharedChain3 1 0 0

disconnectedInventory connectedInventory : SharedChain3
disconnectedInventory = physicalStep noFlow originalInventory
connectedInventory = physicalStep sourceToMiddle originalInventory

sameTotalWithDifferentConnectivity :
  totalSharedInventory disconnectedInventory
    ≡ totalSharedInventory connectedInventory
sameTotalWithDifferentConnectivity = refl

disconnectedMiddleEmpty : middlePool disconnectedInventory ≡ 0
disconnectedMiddleEmpty = refl

connectedMiddleSupplied : middlePool connectedInventory ≡ 1
connectedMiddleSupplied = refl

zeroIsNotOne : 0 ≡ 1 → ⊥
zeroIsNotOne ()

noGlobalTotalPredictorForLocalDelivery :
  (predict : Nat → Nat)
  (factor : (action : PermittedChainAction) →
    middlePool (physicalStep action originalInventory)
      ≡ predict
        (totalSharedInventory (physicalStep action originalInventory))) →
  ⊥
noGlobalTotalPredictorForLocalDelivery predict factor =
  zeroIsNotOne
    (trans
      (sym disconnectedMiddleEmpty)
      (trans (factor noFlow)
        (trans
          (cong predict sameTotalWithDifferentConnectivity)
          (trans (sym (factor sourceToMiddle))
            connectedMiddleSupplied))))

-- Exact existing owner reuse, not a new PNP kinetic-law claim.
donorFiniteTransfer : Set
donorFiniteTransfer = Transport.IonPairState

donorReactionDiffusion : Set
donorReactionDiffusion = Reaction.TwoCompartment

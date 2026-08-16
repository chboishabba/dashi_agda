module DASHI.Biology.Physical.FinitePNPFreeEnergyDissipationExact where

------------------------------------------------------------------------
-- Exact finite energetic regression beneath a future Poisson--Nernst--Planck
-- gradient-flow theorem.  A passive concentration-imbalance relaxation lowers
-- a quadratic free-energy surrogate; an active pump can raise that stored
-- imbalance only with an explicit metabolic work input.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.FiniteElectrodiffusiveMovingBoundaryExact as ED

imbalance : ED.IonPairState → Nat
imbalance (ED.ionPair l r) = (l ∸ r) + (r ∸ l)

freeEnergySurrogate : ED.IonPairState → Nat
freeEnergySurrogate s = imbalance s * imbalance s

passiveInitial : ED.IonPairState
passiveInitial = ED.ionPair 3 1

passiveRelaxed : ED.IonPairState
passiveRelaxed = ED.transport ED.leftToRight passiveInitial

passiveRelaxedIsBalanced : passiveRelaxed ≡ ED.ionPair 2 2
passiveRelaxedIsBalanced = refl

passiveInitialEnergy : freeEnergySurrogate passiveInitial ≡ 4
passiveInitialEnergy = refl

passiveRelaxedEnergy : freeEnergySurrogate passiveRelaxed ≡ 0
passiveRelaxedEnergy = refl

passiveElectrodiffusionStrictlyDissipates :
  freeEnergySurrogate passiveRelaxed < freeEnergySurrogate passiveInitial
passiveElectrodiffusionStrictlyDissipates = s≤s z≤n

------------------------------------------------------------------------
-- An active pump reverses one relaxed transfer.  The induced energy increase
-- is paid for explicitly in the finite work balance.
------------------------------------------------------------------------

activePump : ED.IonPairState → ED.IonPairState
activePump (ED.ionPair l zero) = ED.ionPair l zero
activePump (ED.ionPair l (suc r)) = ED.ionPair (suc l) r

pumpedState : ED.IonPairState
pumpedState = activePump passiveRelaxed

pumpedStateIsInitial : pumpedState ≡ passiveInitial
pumpedStateIsInitial = refl

activePumpRaisesStoredEnergy :
  freeEnergySurrogate pumpedState ≡ freeEnergySurrogate passiveInitial
activePumpRaisesStoredEnergy = refl

pumpWorkBudget : ED.ActiveEnergyStep
pumpWorkBudget = ED.activeEnergyStep 0 4 0 4 refl

pumpEnergyIncreasePaidByMetabolicInput :
  ED.storedAfter pumpWorkBudget + ED.dissipation pumpWorkBudget
  ≡ ED.storedBefore pumpWorkBudget + ED.metabolicInput pumpWorkBudget
pumpEnergyIncreasePaidByMetabolicInput = ED.balance pumpWorkBudget

------------------------------------------------------------------------
-- Conservation is independent of dissipation: both passive and active
-- transfers preserve total ion amount while changing the energetic surrogate.
------------------------------------------------------------------------

passiveAmountConserved :
  ED.totalAmount passiveRelaxed ≡ ED.totalAmount passiveInitial
passiveAmountConserved = ED.transportConservesAmount ED.leftToRight passiveInitial

activeAmountConserved :
  ED.totalAmount pumpedState ≡ ED.totalAmount passiveRelaxed
activeAmountConserved = refl

record PNPFreeEnergyAuthorityBoundary : Set where
  field
    finiteQuadraticSurrogateIsContinuumElectrochemicalFreeEnergy : Bool
    finiteQuadraticSurrogateIsContinuumElectrochemicalFreeEnergyIsFalse :
      finiteQuadraticSurrogateIsContinuumElectrochemicalFreeEnergy ≡ false
    finiteDissipationProvesContinuumPositivityAndWellPosedness : Bool
    finiteDissipationProvesContinuumPositivityAndWellPosednessIsFalse :
      finiteDissipationProvesContinuumPositivityAndWellPosedness ≡ false

canonicalPNPFreeEnergyAuthorityBoundary : PNPFreeEnergyAuthorityBoundary
canonicalPNPFreeEnergyAuthorityBoundary = record
  { finiteQuadraticSurrogateIsContinuumElectrochemicalFreeEnergy = false
  ; finiteQuadraticSurrogateIsContinuumElectrochemicalFreeEnergyIsFalse = refl
  ; finiteDissipationProvesContinuumPositivityAndWellPosedness = false
  ; finiteDissipationProvesContinuumPositivityAndWellPosednessIsFalse = refl
  }

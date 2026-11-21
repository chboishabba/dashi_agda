module DASHI.Biology.BH4CatalyticTurnoverFutureCountermodelExact where

-- BH4 is a recycled cofactor, not an irreversibly consumed substrate
-- at every enzyme-catalyzed reaction. A pool amount alone cannot identify
-- a possible throughput. This finite toy capacity theorem is agnostic about
-- the numerical physiological turnover rate and the clinical hypothesis.

open import DASHI.Core.Prelude

import DASHI.Biology.BH4SystemStateExact as BH4
import DASHI.Biology.BH4CompartmentKineticStateExact as Kinetics
import DASHI.Biology.BH4NOSCouplingSameObjectExact as NOS

record CatalyticCapacityScenario : Set where
  constructor catalytic-capacity-scenario
  field
    availableCofactorMolecules : Nat
    supportedTurnsPerMolecule : Nat
    selectedTurnoverCapacity : Nat
    capacityIdentity :
      availableCofactorMolecules * supportedTurnsPerMolecule
        ≡ selectedTurnoverCapacity

open CatalyticCapacityScenario public

slowCycle fastCycle : CatalyticCapacityScenario
slowCycle = catalytic-capacity-scenario 1 1 1 refl
fastCycle = catalytic-capacity-scenario 1 2 2 refl

sameOriginalPoolAmount :
  availableCofactorMolecules slowCycle
    ≡ availableCofactorMolecules fastCycle
sameOriginalPoolAmount = refl

differentThroughputAtSameAmount :
  selectedTurnoverCapacity slowCycle
    ≡ selectedTurnoverCapacity fastCycle → ⊥
differentThroughputAtSameAmount ()

samePoolDoesNotDetermineEffectiveTurnover :
  (rateFromPool : Nat → Nat)
  ((scenario : CatalyticCapacityScenario) →
    selectedTurnoverCapacity scenario
      ≡ rateFromPool (availableCofactorMolecules scenario)) →
  ⊥
samePoolDoesNotDetermineEffectiveTurnover model factors =
  differentThroughputAtSameAmount
    (trans (factors slowCycle)
      (trans
        (cong model sameOriginalPoolAmount)
        (sym (factors fastCycle))))

-- Same-object source information and kinetic evidence are distinct owners.
originalPoolType : Set
originalPoolType = BH4.BH4PoolState

originalKineticEvidenceType : Set
originalKineticEvidenceType = Kinetics.BH4ParameterEvidence

originalNOSPaymentType : Set
originalNOSPaymentType = NOS.BH4NOSSameObjectPayment

-- The numerical value 2 is an illustrative turnover-count fixture, not
-- a measured enzyme rate, a universal upper bound, or a disease mechanism.

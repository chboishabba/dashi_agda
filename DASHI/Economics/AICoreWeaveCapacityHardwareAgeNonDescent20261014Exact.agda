module DASHI.Economics.AICoreWeaveCapacityHardwareAgeNonDescent20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- CAPACITY VINTAGE DOES NOT DESCEND TO HARDWARE AGE
--
-- This finite witness captures the OSINT identification ceiling. A data-centre
-- MW footprint can retain the same commissioning/vintage observation while the
-- hardware inside it is refreshed. Therefore exact/current hardware age cannot
-- factor through capacity vintage alone. The missing refresh/hardware coordinate
-- is a genuine residual rather than a reason to discard the capacity evidence.
------------------------------------------------------------------------

data HardwareAgeClass : Set where
  olderInstalledHardware refreshedYoungHardware : HardwareAgeClass

data RefreshState : Set where
  originalHardware refreshedInPlace : RefreshState

record FleetWorld : Set where
  constructor fleet-world
  field
    capacityVintageMW : Nat
    hardwareAgeClass : HardwareAgeClass
    refreshState : RefreshState

open FleetWorld public

unrefreshedWorld : FleetWorld
unrefreshedWorld = fleet-world 290 olderInstalledHardware originalHardware

refreshedWorld : FleetWorld
refreshedWorld = fleet-world 290 refreshedYoungHardware refreshedInPlace

capacityObserver : FleetWorld → Nat
capacityObserver = capacityVintageMW

hardwareAgeConsumer : FleetWorld → HardwareAgeClass
hardwareAgeConsumer = hardwareAgeClass

refreshCoordinate : FleetWorld → RefreshState
refreshCoordinate = refreshState

sameCapacityDifferentHardwareAgeWitness :
  Descent.ConsumerNonDescentWitness capacityObserver hardwareAgeConsumer
sameCapacityDifferentHardwareAgeWitness =
  Descent.consumerNonDescentWitness
    unrefreshedWorld
    refreshedWorld
    refl
    (λ ())

capacityVintageCannotFactorHardwareAge :
  Descent.FactorsThrough capacityObserver hardwareAgeConsumer → ⊥
capacityVintageCannotFactorHardwareAge =
  Descent.nonDescentWitnessBlocksFactorization sameCapacityDifferentHardwareAgeWitness

refreshCoordinateSeparatesWitness :
  refreshCoordinate unrefreshedWorld ≡ refreshCoordinate refreshedWorld → ⊥
refreshCoordinateSeparatesWitness ()

data CapacityAgeDeterminesHardwareAgePermission : Set where

data MoreActiveMWMeansNoRefreshPermission : Set where

capacityAgeDoesNotDetermineHardwareAge :
  CapacityAgeDeterminesHardwareAgePermission → ⊥
capacityAgeDoesNotDetermineHardwareAge ()

moreActiveMWDoesNotProveNoRefresh : MoreActiveMWMeansNoRefreshPermission → ⊥
moreActiveMWDoesNotProveNoRefresh ()

boundary : String
boundary =
  "Capacity-vintage OSINT and hardware-vintage inference are different observers. Two worlds can expose the same 290-MW deployment-vintage coordinate while carrying old versus refreshed hardware. The canonical consumer-non-descent witness therefore blocks exact hardware-age recovery from active-power history alone. A refresh/hardware-generation coordinate separates this witnessed collision; broader fleet recovery still requires empirical generation, replacement and retirement evidence."

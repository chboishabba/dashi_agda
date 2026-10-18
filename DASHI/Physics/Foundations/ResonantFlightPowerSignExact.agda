module DASHI.Physics.Foundations.ResonantFlightPowerSignExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Keep sign semantics explicit without committing to a concrete ordered
-- scalar field at this layer.
------------------------------------------------------------------------

data PowerSign : Set where
  positive zero negative : PowerSign

record SignedPower : Set₁ where
  constructor signed-power
  field
    Power : Set
    value : Power
    sign : PowerSign

open SignedPower public

data EnergyDirection : Set where
  sourceToWing wingToStore noNetTransfer : EnergyDirection

powerSignDirection : PowerSign → EnergyDirection
powerSignDirection positive = sourceToWing
powerSignDirection zero = noNetTransfer
powerSignDirection negative = wingToStore

negativePowerIsRegenerative :
  powerSignDirection negative ≡ wingToStore
negativePowerIsRegenerative = refl

positivePowerIsDrive :
  powerSignDirection positive ≡ sourceToWing
positivePowerIsDrive = refl

module DASHI.Physics.YangMills.BalabanVacuumPolarisationDomainTail where

-- Compatibility boundary only.  The canonical mathematical bridge is
-- `BalabanMarkedPolarisationResummation`, where `concreteBetaDomainTail` is
-- an explicit proof term.  Keep this fail-closed name for source-intake
-- clients while avoiding a second record that stores the desired conclusion
-- as data.

open import Agda.Builtin.Bool using (false)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( VerificationStatus ; openTarget )
open import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation public

actualBalabanVacuumPolarisationDomainTailAvailable : Set
actualBalabanVacuumPolarisationDomainTailAvailable = ⊥

currentBalabanVacuumPolarisationDomainTailStatus : VerificationStatus
currentBalabanVacuumPolarisationDomainTailStatus = openTarget

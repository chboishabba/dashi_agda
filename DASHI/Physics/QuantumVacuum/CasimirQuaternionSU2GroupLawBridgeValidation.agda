module DASHI.Physics.QuantumVacuum.CasimirQuaternionSU2GroupLawBridgeValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.CasimirQuaternionSU2GroupLawBridgeExact as M
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2

sameCarrierRegression :
  M.genericSU2Carrier ≡ SU2.SU2Quaternion
sameCarrierRegression = refl

identityLawRegression :
  M.genericSU2Identity ≡ SU2.su2Identity
identityLawRegression = refl

multiplyLawRegression :
  ∀ a b → M.genericSU2Multiply a b ≡ SU2.su2Multiply a b
multiplyLawRegression a b = refl

inverseLawRegression :
  ∀ a → M.genericSU2Inverse a ≡ SU2.su2Inverse a
inverseLawRegression a = refl

legacyGaugeStructureCompilerPaidRegression :
  M.genericToLegacyQuaternionGroupLawBridgePaid M.canonicalQuaternionSU2GroupLawBoundary ≡ true
legacyGaugeStructureCompilerPaidRegression = refl

selectedStructuralGroupStillNeedsIdentificationRegression :
  M.selectedStructuralGroupIdentifiedWithQuaternionSU2 M.canonicalQuaternionSU2GroupLawBoundary ≡ false
selectedStructuralGroupStillNeedsIdentificationRegression = refl

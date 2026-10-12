module DASHI.Moonshine.Monster3BSelectedHeisenbergLiftValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.Monster3BSelectedHeisenbergLiftExact as Lift

selectedWordStrictlySymplectic :
  Lift.selectedWordSymplecticMultiplier Lift.canonicalReceipt ≡ 1
selectedWordStrictlySymplectic = refl

compressionMatchesFieldSelector :
  Lift.compressionMatchesSelectedFieldReceipt Lift.canonicalReceipt ≡ true
compressionMatchesFieldSelector = refl

centralDefectSymmetric :
  Lift.cocycleDefectSymmetric Lift.canonicalReceipt ≡ true
centralDefectSymmetric = refl

quadraticCorrectionPaid :
  Lift.quadraticPolarizationIdentityPaid Lift.canonicalReceipt ≡ true
quadraticCorrectionPaid = refl

heisenbergCoboundaryPaid :
  Lift.heisenbergCoboundaryIdentityPaid Lift.canonicalReceipt ≡ true
heisenbergCoboundaryPaid = refl

fullNormalizerLiftStillOpen :
  Lift.fullNormalizerHeisenbergActionPaid Lift.canonicalBoundary ≡ false
fullNormalizerLiftStillOpen = refl

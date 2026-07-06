module DASHI.Physics.Closure.NSTriadKNAdversarialColumnClosureDependency where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.NSTriadKNAdversarialColumnConcreteBounds
  using ( NSTriadKNAdversarialColumnConcreteBounds
        ; canonicalNSTriadKNAdversarialColumnConcreteBounds
        )

------------------------------------------------------------------------
-- Dependency-honest local closure bridge for the adversarial column lane.
--
-- This does not promote the adversarial profile globally. It only packages
-- the second analytic theorem surface,
--
--   adversarialColumnN1Bound
--
-- so the weighted-product theorem can later depend on a canonical witness
-- rather than a documentary boolean.

record NSTriadKNAdversarialColumnClosureDependency : Set where
  constructor mkNSTriadKNAdversarialColumnClosureDependency
  field
    columnConcreteBounds :
      NSTriadKNAdversarialColumnConcreteBounds

open NSTriadKNAdversarialColumnClosureDependency public

canonicalNSTriadKNAdversarialColumnClosureDependency :
  NSTriadKNAdversarialColumnClosureDependency
canonicalNSTriadKNAdversarialColumnClosureDependency =
  mkNSTriadKNAdversarialColumnClosureDependency
    canonicalNSTriadKNAdversarialColumnConcreteBounds

adversarialColumnN1BoundAvailable : Bool
adversarialColumnN1BoundAvailable
  with canonicalNSTriadKNAdversarialColumnClosureDependency
... | _ = true

adversarialColumnN1BoundAvailableIsTrue :
  adversarialColumnN1BoundAvailable ≡ true
adversarialColumnN1BoundAvailableIsTrue = refl

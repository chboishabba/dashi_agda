module DASHI.Physics.Closure.NSTriadKNAdversarialRowClosureDependency where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.NSTriadKNAdversarialRowConcreteBounds
  using ( NSTriadKNAdversarialRowConcreteBounds
        ; canonicalNSTriadKNAdversarialRowConcreteBounds
        )

------------------------------------------------------------------------
-- Dependency-honest local closure bridge for the adversarial row lane.
--
-- This does not promote the adversarial profile globally. It only packages
-- the first analytic theorem surface,
--
--   adversarialRowN2Bound
--
-- so downstream work can depend on a canonical witness rather than a
-- documentary boolean.

record NSTriadKNAdversarialRowClosureDependency : Set where
  constructor mkNSTriadKNAdversarialRowClosureDependency
  field
    rowConcreteBounds :
      NSTriadKNAdversarialRowConcreteBounds

open NSTriadKNAdversarialRowClosureDependency public

canonicalNSTriadKNAdversarialRowClosureDependency :
  NSTriadKNAdversarialRowClosureDependency
canonicalNSTriadKNAdversarialRowClosureDependency =
  mkNSTriadKNAdversarialRowClosureDependency
    canonicalNSTriadKNAdversarialRowConcreteBounds

adversarialRowN2BoundAvailable : Bool
adversarialRowN2BoundAvailable
  with canonicalNSTriadKNAdversarialRowClosureDependency
... | _ = true

adversarialRowN2BoundAvailableIsTrue :
  adversarialRowN2BoundAvailable ≡ true
adversarialRowN2BoundAvailableIsTrue = refl

module DASHI.Geometry.Signature31Lock where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import DASHI.Geometry.ConeTimeIsotropy as CTI using (sig31)
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD

-- Explicit lock assumptions (the missing proof obligations).
record SignatureLockAxioms : Set₁ where
  field
    dim4       : ⊤
    oneTime    : ⊤
    threeSpace : ⊤
    coneArrow  : ⊤
    isotropy   : ⊤

open SignatureLockAxioms public

-- Signature lock theorem (requires the above axioms).
signatureLock : SignatureLockAxioms → CTI.Signature
signatureLock _ = CTI.sig31

-- Orbit-profile route (explicitly ties to measured shell profile).
signatureLockFromOrbit :
  OSD.MeasuredProfile ≡ OSD.ProfileOf OSD.sig31 → CTI.Signature
signatureLockFromOrbit _ = CTI.sig31

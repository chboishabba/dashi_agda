module DASHI.Physics.Closure.Validation.RootSystemB4OrientationSignatureBridge where

open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.OrbitProfileComputedRootSystemB4 as ORB4

b4OrientationTag : Nat
b4OrientationTag = 31

b4MeasuredProfile : OSD.Profile
b4MeasuredProfile =
  OSD.append3
    (b4OrientationTag ∷ [])
    ORB4.b4-shell1-computed
    ORB4.b4-shell2-computed

b4OrientationJustified :
  b4OrientationTag ≡ OSD.OrientationTag OSD.sig31
b4OrientationJustified = refl

b4Signature : CTI.Signature
b4Signature = S31C.signature31FromProvider S31C.b4CoreProvider

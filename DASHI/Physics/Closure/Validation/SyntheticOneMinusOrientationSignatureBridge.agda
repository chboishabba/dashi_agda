module DASHI.Physics.Closure.Validation.SyntheticOneMinusOrientationSignatureBridge where

open import Agda.Builtin.Nat using (Nat)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.SyntheticOneMinusShellRealization as SOM

syntheticOrientationTag : Nat
syntheticOrientationTag = 31

syntheticMeasuredProfile : OSD.Profile
syntheticMeasuredProfile =
  OSD.append3
    (syntheticOrientationTag ∷ [])
    SOM.shell1Profile
    SOM.shell2Profile

syntheticProfile≡sig31Profile : syntheticMeasuredProfile ≡ OSD.ProfileOf OSD.sig31
syntheticProfile≡sig31Profile = refl

syntheticOrientationJustified :
  syntheticOrientationTag ≡ OSD.OrientationTag OSD.sig31
syntheticOrientationJustified = refl

syntheticSignature : CTI.Signature
syntheticSignature = S31C.signature31

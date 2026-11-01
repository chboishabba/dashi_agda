module DASHI.Geometry.ConeArrowIsotropyOrbitProfile where

open import Agda.Builtin.Nat using (Nat)
open import Data.List using (List; _∷_; []; _++_)
open import Level using (_⊔_; suc)

open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.ProjectionDefect using (Additive)
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.Signature31FromConeArrowIsotropy as S31
open import DASHI.Geometry.ConeArrowIsotropyShellAction as CAS
open import DASHI.Geometry.ConeArrowIsotropyShellEnumeration as CASE

record AbstractOrbitProfile : Set where
  field
    profileData : CTI.OrbitProfileData

open AbstractOrbitProfile public

record OrbitProfileDerivation {ℓv ℓs}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {QF : QuadraticForm A F}
  (shellAction : CAS.AbstractShellAction A F QF) : Set where
  field
    orientationTag : Nat
    enumeration : CTI.ShellOrbitEnumeration

open OrbitProfileDerivation public

toProfile : AbstractOrbitProfile → List Nat
toProfile prof =
  (CTI.OrbitProfileData.orientationTag d ∷ [])
  ++ CTI.OrbitProfileData.shell1Profile d
  ++ CTI.OrbitProfileData.shell2Profile d
  where
    d : CTI.OrbitProfileData
    d = profileData prof

buildOrbitProfileFromDerivation :
  ∀ {ℓv ℓs}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {QF : QuadraticForm A F} →
  {shellAction : CAS.AbstractShellAction A F QF} →
  OrbitProfileDerivation shellAction →
  AbstractOrbitProfile
buildOrbitProfileFromDerivation {shellAction = shellAction} deriv =
  record
    { profileData =
        record
          { orientationTag = OrbitProfileDerivation.orientationTag deriv
          ; shell1Profile = CTI.ShellOrbitEnumeration.shell1OrbitSizes
              (OrbitProfileDerivation.enumeration deriv)
          ; shell2Profile = CTI.ShellOrbitEnumeration.shell2OrbitSizes
              (OrbitProfileDerivation.enumeration deriv)
          }
    }

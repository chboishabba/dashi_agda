module DASHI.Physics.Closure.IntrinsicOrbitProfileLorentzTheorem where

-- Intrinsic finite-profile route: cone/arrow/isotropy/finite-speed data produce
-- an orientation tag and finite shell-orbit enumeration.  The only concrete
-- arithmetic obligations are equality of those computed lists with the
-- canonical signed-block enumeration.  No CSV-backed measured-profile premise
-- is required by the theorem below.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; []; _++_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD

append3 : OSD.Profile → OSD.Profile → OSD.Profile → OSD.Profile
append3 a b c = (a ++ b) ++ c

record IntrinsicConeArrowOrbitData : Setω where
  field
    ConeCarrier : Set
    cone : CTI.ConeStructure ConeCarrier
    arrow : CTI.TimeArrow ConeCarrier
    isotropy : CTI.IsotropyAction ConeCarrier
    FiniteSpeedCompatible : Set
    finiteSpeedCompatible : FiniteSpeedCompatible

    orientationTag : Nat
    shellEnumeration : CTI.ShellOrbitEnumeration

  intrinsicProfile : OSD.Profile
  intrinsicProfile =
    append3
      (orientationTag ∷ [])
      (CTI.ShellOrbitEnumeration.shell1OrbitSizes shellEnumeration)
      (CTI.ShellOrbitEnumeration.shell2OrbitSizes shellEnumeration)

record IntrinsicLorentz31Enumeration
  (data : IntrinsicConeArrowOrbitData) : Setω where
  field
    orientationIs31 :
      IntrinsicConeArrowOrbitData.orientationTag data ≡ 31
    shell1Is31 :
      CTI.ShellOrbitEnumeration.shell1OrbitSizes
        (IntrinsicConeArrowOrbitData.shellEnumeration data)
      ≡ OPD.shell1_p3_q1
    shell2Is31 :
      CTI.ShellOrbitEnumeration.shell2OrbitSizes
        (IntrinsicConeArrowOrbitData.shellEnumeration data)
      ≡ OPD.shell2_p3_q1

intrinsicProfileIsCanonical31 :
  ∀ {data} →
  IntrinsicLorentz31Enumeration data →
  IntrinsicConeArrowOrbitData.intrinsicProfile data ≡ OSD.ProfileOf OSD.sig31
intrinsicProfileIsCanonical31 {data} enumeration
  rewrite IntrinsicLorentz31Enumeration.orientationIs31 enumeration
        | IntrinsicLorentz31Enumeration.shell1Is31 enumeration
        | IntrinsicLorentz31Enumeration.shell2Is31 enumeration = refl

intrinsicSignatureUnique31 :
  ∀ {data} →
  (enumeration : IntrinsicLorentz31Enumeration data) →
  ∀ s →
  IntrinsicConeArrowOrbitData.intrinsicProfile data ≡ OSD.ProfileOf s →
  s ≡ OSD.sig31
intrinsicSignatureUnique31 {data} enumeration s profileOfS =
  OSD.SignatureFromMeasuredProfileUnique s
    (trans
      (sym (intrinsicProfileIsCanonical31 enumeration))
      profileOfS)

record IntrinsicLorentz31Theorem : Setω where
  field
    data : IntrinsicConeArrowOrbitData
    enumeration : IntrinsicLorentz31Enumeration data

  profileIs31 :
    IntrinsicConeArrowOrbitData.intrinsicProfile data ≡ OSD.ProfileOf OSD.sig31
  profileIs31 = intrinsicProfileIsCanonical31 enumeration

  uniqueSignature :
    ∀ s → IntrinsicConeArrowOrbitData.intrinsicProfile data ≡ OSD.ProfileOf s →
    s ≡ OSD.sig31
  uniqueSignature = intrinsicSignatureUnique31 enumeration

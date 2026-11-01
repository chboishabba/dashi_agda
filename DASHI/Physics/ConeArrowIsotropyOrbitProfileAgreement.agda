module DASHI.Physics.ConeArrowIsotropyOrbitProfileAgreement where

open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import DASHI.Geometry.ConeArrowIsotropyOrbitProfile as CAOP
open import DASHI.Geometry.ConeTimeIsotropy as CTI
import DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration as SOE
open import DASHI.Physics.OrbitProfileComputedSignedPerm as OPCSP
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.Signature31ShiftProfileWitness as SPW

shiftOrbitProfileDerivation :
  CAOP.OrbitProfileDerivation SOE.shiftShellAction
shiftOrbitProfileDerivation = SOE.shiftOrbitProfileDerivation

abstractProfile : CAOP.AbstractOrbitProfile
abstractProfile =
  CAOP.buildOrbitProfileFromDerivation shiftOrbitProfileDerivation

orientationTag-derived :
  CAOP.OrbitProfileDerivation.orientationTag shiftOrbitProfileDerivation
  ≡ OSD.OrientationTag OSD.sig31
orientationTag-derived = SOE.orientationTagDerived

shell1-derived :
  CTI.ShellOrbitEnumeration.shell1OrbitSizes
    (CAOP.OrbitProfileDerivation.enumeration shiftOrbitProfileDerivation)
  ≡ OPCSP.shell1_p3_q1_computed
shell1-derived = SOE.shiftEnumeration-shell1≡computed

shell2-derived :
  CTI.ShellOrbitEnumeration.shell2OrbitSizes
    (CAOP.OrbitProfileDerivation.enumeration shiftOrbitProfileDerivation)
  ≡ OPCSP.shell2_p3_q1_computed
shell2-derived = SOE.shiftEnumeration-shell2≡computed

abstractProfile≡computedProfile : CAOP.toProfile abstractProfile ≡ SPW.computedProfile
abstractProfile≡computedProfile
  rewrite orientationTag-derived | shell1-derived | shell2-derived = refl

abstractMeasured≡ProfileOfSig31 : CAOP.toProfile abstractProfile ≡ OSD.ProfileOf OSD.sig31
abstractMeasured≡ProfileOfSig31 =
  trans
    abstractProfile≡computedProfile
    SPW.computed≡sig31Profile

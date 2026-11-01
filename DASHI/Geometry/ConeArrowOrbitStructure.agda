module DASHI.Geometry.ConeArrowOrbitStructure where

open import Agda.Builtin.Nat using (Nat)
open import Level using (suc)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.ConeArrowIsotropyOrbitProfile as CAOP
open import DASHI.Geometry.ConeArrowShellStratification as CASS

record IntrinsicOrbitStructure : Set where
  field
    enumeration : CTI.ShellOrbitEnumeration

open IntrinsicOrbitStructure public

buildIntrinsicOrbitStructure :
  CASS.IntrinsicShellStratification →
  IntrinsicOrbitStructure
buildIntrinsicOrbitStructure strata =
  record
    { enumeration = CASS.toEnumeration strata
    }

buildAbstractOrbitProfile :
  Nat →
  IntrinsicOrbitStructure →
  CAOP.AbstractOrbitProfile
buildAbstractOrbitProfile orientationTag orbit =
  record
    { profileData =
        record
          { orientationTag = orientationTag
          ; shell1Profile =
              CTI.ShellOrbitEnumeration.shell1OrbitSizes
                (IntrinsicOrbitStructure.enumeration orbit)
          ; shell2Profile =
              CTI.ShellOrbitEnumeration.shell2OrbitSizes
                (IntrinsicOrbitStructure.enumeration orbit)
          }
    }

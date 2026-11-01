module DASHI.Geometry.ConeArrowShellStratification where

open import Level using (suc)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

open import DASHI.Geometry.ConeTimeIsotropy as CTI

record IntrinsicShellStratification : Set where
  field
    shell1OrbitSizes : List Nat
    shell2OrbitSizes : List Nat

open IntrinsicShellStratification public

toEnumeration :
  IntrinsicShellStratification → CTI.ShellOrbitEnumeration
toEnumeration strata =
  record
    { shell1OrbitSizes = IntrinsicShellStratification.shell1OrbitSizes strata
    ; shell2OrbitSizes = IntrinsicShellStratification.shell2OrbitSizes strata
    }

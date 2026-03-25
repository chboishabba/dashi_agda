{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.DASHI.Geometry.ConeArrowShellStratification where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy

-- DASHI.Geometry.ConeArrowShellStratification.IntrinsicShellStratification
d_IntrinsicShellStratification_6 = ()
data T_IntrinsicShellStratification_6
  = C_IntrinsicShellStratification'46'constructor_13 [Integer]
                                                     [Integer]
-- DASHI.Geometry.ConeArrowShellStratification.IntrinsicShellStratification.shell1OrbitSizes
d_shell1OrbitSizes_12 ::
  T_IntrinsicShellStratification_6 -> [Integer]
d_shell1OrbitSizes_12 v0
  = case coe v0 of
      C_IntrinsicShellStratification'46'constructor_13 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowShellStratification.IntrinsicShellStratification.shell2OrbitSizes
d_shell2OrbitSizes_14 ::
  T_IntrinsicShellStratification_6 -> [Integer]
d_shell2OrbitSizes_14 v0
  = case coe v0 of
      C_IntrinsicShellStratification'46'constructor_13 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowShellStratification.toEnumeration
d_toEnumeration_16 ::
  T_IntrinsicShellStratification_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
d_toEnumeration_16 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_ShellOrbitEnumeration'46'constructor_1915
      (coe d_shell1OrbitSizes_12 (coe v0))
      (coe d_shell2OrbitSizes_14 (coe v0))

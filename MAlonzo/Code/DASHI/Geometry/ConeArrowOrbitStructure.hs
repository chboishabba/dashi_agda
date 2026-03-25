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

module MAlonzo.Code.DASHI.Geometry.ConeArrowOrbitStructure where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyOrbitProfile
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowShellStratification
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy

-- DASHI.Geometry.ConeArrowOrbitStructure.IntrinsicOrbitStructure
d_IntrinsicOrbitStructure_6 = ()
newtype T_IntrinsicOrbitStructure_6
  = C_IntrinsicOrbitStructure'46'constructor_1 MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
-- DASHI.Geometry.ConeArrowOrbitStructure.IntrinsicOrbitStructure.enumeration
d_enumeration_10 ::
  T_IntrinsicOrbitStructure_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
d_enumeration_10 v0
  = case coe v0 of
      C_IntrinsicOrbitStructure'46'constructor_1 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowOrbitStructure.buildIntrinsicOrbitStructure
d_buildIntrinsicOrbitStructure_12 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowShellStratification.T_IntrinsicShellStratification_6 ->
  T_IntrinsicOrbitStructure_6
d_buildIntrinsicOrbitStructure_12 v0
  = coe
      C_IntrinsicOrbitStructure'46'constructor_1
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeArrowShellStratification.d_toEnumeration_16
         (coe v0))
-- DASHI.Geometry.ConeArrowOrbitStructure.buildAbstractOrbitProfile
d_buildAbstractOrbitProfile_16 ::
  Integer ->
  T_IntrinsicOrbitStructure_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyOrbitProfile.T_AbstractOrbitProfile_6
d_buildAbstractOrbitProfile_16 v0 v1
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyOrbitProfile.C_AbstractOrbitProfile'46'constructor_1
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_OrbitProfileData'46'constructor_1961
         (coe v0)
         (coe
            MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_shell1OrbitSizes_268
            (coe d_enumeration_10 (coe v1)))
         (coe
            MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_shell2OrbitSizes_270
            (coe d_enumeration_10 (coe v1))))

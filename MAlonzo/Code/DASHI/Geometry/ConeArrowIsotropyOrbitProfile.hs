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

module MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyOrbitProfile where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.Data.List.Base

-- DASHI.Geometry.ConeArrowIsotropyOrbitProfile.AbstractOrbitProfile
d_AbstractOrbitProfile_6 = ()
newtype T_AbstractOrbitProfile_6
  = C_AbstractOrbitProfile'46'constructor_1 MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_OrbitProfileData_272
-- DASHI.Geometry.ConeArrowIsotropyOrbitProfile.AbstractOrbitProfile.profileData
d_profileData_10 ::
  T_AbstractOrbitProfile_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_OrbitProfileData_272
d_profileData_10 v0
  = case coe v0 of
      C_AbstractOrbitProfile'46'constructor_1 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyOrbitProfile.OrbitProfileDerivation
d_OrbitProfileDerivation_24 a0 a1 a2 a3 a4 a5 = ()
data T_OrbitProfileDerivation_24
  = C_OrbitProfileDerivation'46'constructor_195 Integer
                                                MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
-- DASHI.Geometry.ConeArrowIsotropyOrbitProfile.OrbitProfileDerivation.orientationTag
d_orientationTag_42 :: T_OrbitProfileDerivation_24 -> Integer
d_orientationTag_42 v0
  = case coe v0 of
      C_OrbitProfileDerivation'46'constructor_195 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyOrbitProfile.OrbitProfileDerivation.enumeration
d_enumeration_44 ::
  T_OrbitProfileDerivation_24 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
d_enumeration_44 v0
  = case coe v0 of
      C_OrbitProfileDerivation'46'constructor_195 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyOrbitProfile.toProfile
d_toProfile_46 :: T_AbstractOrbitProfile_6 -> [Integer]
d_toProfile_46 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_orientationTag_280
            (coe d_d_54 (coe v0)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_shell1Profile_282
            (coe d_d_54 (coe v0)))
         (coe
            MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_shell2Profile_284
            (coe d_d_54 (coe v0))))
-- DASHI.Geometry.ConeArrowIsotropyOrbitProfile._.d
d_d_54 ::
  T_AbstractOrbitProfile_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_OrbitProfileData_272
d_d_54 v0 = coe d_profileData_10 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyOrbitProfile.buildOrbitProfileFromDerivation
d_buildOrbitProfileFromDerivation_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  T_OrbitProfileDerivation_24 -> T_AbstractOrbitProfile_6
d_buildOrbitProfileFromDerivation_68 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_buildOrbitProfileFromDerivation_68 v6
du_buildOrbitProfileFromDerivation_68 ::
  T_OrbitProfileDerivation_24 -> T_AbstractOrbitProfile_6
du_buildOrbitProfileFromDerivation_68 v0
  = coe
      C_AbstractOrbitProfile'46'constructor_1
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_OrbitProfileData'46'constructor_1961
         (coe d_orientationTag_42 (coe v0))
         (coe
            MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_shell1OrbitSizes_268
            (coe d_enumeration_44 (coe v0)))
         (coe
            MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_shell2OrbitSizes_270
            (coe d_enumeration_44 (coe v0))))

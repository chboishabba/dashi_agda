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

module MAlonzo.Code.DASHI.Geometry.QQuadraticForm where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect

-- DASHI.Geometry.QuadraticForm.ScalarField
d_ScalarField_8 a0 = ()
data T_ScalarField_8
  = C_ScalarField'46'constructor_77 (AgdaAny -> AgdaAny -> AgdaAny)
                                    (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny AgdaAny
                                    (AgdaAny -> AgdaAny)
-- DASHI.Geometry.QuadraticForm.ScalarField.S
d_S_24 :: T_ScalarField_8 -> ()
d_S_24 = erased
-- DASHI.Geometry.QuadraticForm.ScalarField._+s_
d__'43's__26 :: T_ScalarField_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43's__26 v0
  = case coe v0 of
      C_ScalarField'46'constructor_77 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.QuadraticForm.ScalarField._*s_
d__'42's__28 :: T_ScalarField_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42's__28 v0
  = case coe v0 of
      C_ScalarField'46'constructor_77 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.QuadraticForm.ScalarField.0s
d_0s_30 :: T_ScalarField_8 -> AgdaAny
d_0s_30 v0
  = case coe v0 of
      C_ScalarField'46'constructor_77 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.QuadraticForm.ScalarField.1s
d_1s_32 :: T_ScalarField_8 -> AgdaAny
d_1s_32 v0
  = case coe v0 of
      C_ScalarField'46'constructor_77 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.QuadraticForm.ScalarField.-s_
d_'45's__34 :: T_ScalarField_8 -> AgdaAny -> AgdaAny
d_'45's__34 v0
  = case coe v0 of
      C_ScalarField'46'constructor_77 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.QuadraticForm.QuadraticForm
d_QuadraticForm_44 a0 a1 a2 a3 = ()
data T_QuadraticForm_44
  = C_QuadraticForm'46'constructor_1593 (AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Geometry.QuadraticForm._._*s_
d__'42's__66 :: T_ScalarField_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42's__66 v0 = coe d__'42's__28 (coe v0)
-- DASHI.Geometry.QuadraticForm._._+s_
d__'43's__68 :: T_ScalarField_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43's__68 v0 = coe d__'43's__26 (coe v0)
-- DASHI.Geometry.QuadraticForm._.-s_
d_'45's__70 :: T_ScalarField_8 -> AgdaAny -> AgdaAny
d_'45's__70 v0 = coe d_'45's__34 (coe v0)
-- DASHI.Geometry.QuadraticForm._.0s
d_0s_72 :: T_ScalarField_8 -> AgdaAny
d_0s_72 v0 = coe d_0s_30 (coe v0)
-- DASHI.Geometry.QuadraticForm._.1s
d_1s_74 :: T_ScalarField_8 -> AgdaAny
d_1s_74 v0 = coe d_1s_32 (coe v0)
-- DASHI.Geometry.QuadraticForm._.S
d_S_76 :: T_ScalarField_8 -> ()
d_S_76 = erased
-- DASHI.Geometry.QuadraticForm.QuadraticForm._._*s_
d__'42's__106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  T_ScalarField_8 ->
  T_QuadraticForm_44 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42's__106 ~v0 ~v1 ~v2 v3 ~v4 = du__'42's__106 v3
du__'42's__106 :: T_ScalarField_8 -> AgdaAny -> AgdaAny -> AgdaAny
du__'42's__106 v0 = coe d__'42's__28 (coe v0)
-- DASHI.Geometry.QuadraticForm.QuadraticForm._._+s_
d__'43's__108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  T_ScalarField_8 ->
  T_QuadraticForm_44 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43's__108 ~v0 ~v1 ~v2 v3 ~v4 = du__'43's__108 v3
du__'43's__108 :: T_ScalarField_8 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43's__108 v0 = coe d__'43's__26 (coe v0)
-- DASHI.Geometry.QuadraticForm.QuadraticForm._.-s_
d_'45's__110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  T_ScalarField_8 -> T_QuadraticForm_44 -> AgdaAny -> AgdaAny
d_'45's__110 ~v0 ~v1 ~v2 v3 ~v4 = du_'45's__110 v3
du_'45's__110 :: T_ScalarField_8 -> AgdaAny -> AgdaAny
du_'45's__110 v0 = coe d_'45's__34 (coe v0)
-- DASHI.Geometry.QuadraticForm.QuadraticForm._.0s
d_0s_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  T_ScalarField_8 -> T_QuadraticForm_44 -> AgdaAny
d_0s_112 ~v0 ~v1 ~v2 v3 ~v4 = du_0s_112 v3
du_0s_112 :: T_ScalarField_8 -> AgdaAny
du_0s_112 v0 = coe d_0s_30 (coe v0)
-- DASHI.Geometry.QuadraticForm.QuadraticForm._.1s
d_1s_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  T_ScalarField_8 -> T_QuadraticForm_44 -> AgdaAny
d_1s_114 ~v0 ~v1 ~v2 v3 ~v4 = du_1s_114 v3
du_1s_114 :: T_ScalarField_8 -> AgdaAny
du_1s_114 v0 = coe d_1s_32 (coe v0)
-- DASHI.Geometry.QuadraticForm.QuadraticForm._.S
d_S_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  T_ScalarField_8 -> T_QuadraticForm_44 -> ()
d_S_116 = erased
-- DASHI.Geometry.QuadraticForm.QuadraticForm.Q
d_Q_118 :: T_QuadraticForm_44 -> AgdaAny -> AgdaAny
d_Q_118 v0
  = case coe v0 of
      C_QuadraticForm'46'constructor_1593 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.QuadraticForm.QuadraticForm._·_
d__'183'__120 ::
  T_QuadraticForm_44 -> AgdaAny -> AgdaAny -> AgdaAny
d__'183'__120 v0
  = case coe v0 of
      C_QuadraticForm'46'constructor_1593 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.QuadraticForm.QuadraticForm.Parallelogram
d_Parallelogram_126 ::
  T_QuadraticForm_44 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Parallelogram_126 = erased
-- DASHI.Geometry.QuadraticForm.QuadraticForm.Homog
d_Homog_132 ::
  T_QuadraticForm_44 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Homog_132 = erased

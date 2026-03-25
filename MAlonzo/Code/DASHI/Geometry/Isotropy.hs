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

module MAlonzo.Code.DASHI.Geometry.Isotropy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Ultrametric

-- DASHI.Geometry.Isotropy.Group
d_Group_8 a0 = ()
data T_Group_8
  = C_Group'46'constructor_565 (AgdaAny -> AgdaAny -> AgdaAny)
                               AgdaAny (AgdaAny -> AgdaAny)
-- DASHI.Geometry.Isotropy.Group._∙_
d__'8729'__34 :: T_Group_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__34 v0
  = case coe v0 of
      C_Group'46'constructor_565 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Isotropy.Group.e
d_e_36 :: T_Group_8 -> AgdaAny
d_e_36 v0
  = case coe v0 of
      C_Group'46'constructor_565 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Isotropy.Group.inv
d_inv_38 :: T_Group_8 -> AgdaAny -> AgdaAny
d_inv_38 v0
  = case coe v0 of
      C_Group'46'constructor_565 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Isotropy.Group.assoc
d_assoc_46 ::
  T_Group_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_46 = erased
-- DASHI.Geometry.Isotropy.Group.idL
d_idL_50 ::
  T_Group_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idL_50 = erased
-- DASHI.Geometry.Isotropy.Group.invL
d_invL_54 ::
  T_Group_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_invL_54 = erased
-- DASHI.Geometry.Isotropy.Isotropy
d_Isotropy_62 a0 a1 a2 = ()
data T_Isotropy_62
  = C_Isotropy'46'constructor_1461 T_Group_8
                                   (AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Geometry.Isotropy._.d
d_d_72 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> Integer
d_d_72 v0 ~v1 = du_d_72 v0
du_d_72 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  AgdaAny -> AgdaAny -> Integer
du_d_72 v0 = coe MAlonzo.Code.Ultrametric.d_d_30 (coe v0)
-- DASHI.Geometry.Isotropy.Isotropy.G
d_G_110 :: T_Isotropy_62 -> ()
d_G_110 = erased
-- DASHI.Geometry.Isotropy.Isotropy.group
d_group_112 :: T_Isotropy_62 -> T_Group_8
d_group_112 v0
  = case coe v0 of
      C_Isotropy'46'constructor_1461 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Isotropy.Isotropy.act
d_act_114 :: T_Isotropy_62 -> AgdaAny -> AgdaAny -> AgdaAny
d_act_114 v0
  = case coe v0 of
      C_Isotropy'46'constructor_1461 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Isotropy.Isotropy.preservesMetric
d_preservesMetric_122 ::
  T_Isotropy_62 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_preservesMetric_122 = erased
-- DASHI.Geometry.Isotropy.Isotropy.commutesWithT
d_commutesWithT_128 ::
  T_Isotropy_62 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_commutesWithT_128 = erased
-- DASHI.Geometry.Isotropy.trivialIsotropy
d_trivialIsotropy_136 ::
  () ->
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) -> T_Isotropy_62
d_trivialIsotropy_136 ~v0 ~v1 ~v2 = du_trivialIsotropy_136
du_trivialIsotropy_136 :: T_Isotropy_62
du_trivialIsotropy_136
  = coe
      C_Isotropy'46'constructor_1461
      (coe
         C_Group'46'constructor_565
         (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (\ v0 v1 -> v1)

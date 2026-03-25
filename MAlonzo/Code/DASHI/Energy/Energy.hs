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

module MAlonzo.Code.DASHI.Energy.Energy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

-- DASHI.Energy.Energy.Preorder
d_Preorder_8 a0 = ()
data T_Preorder_8
  = C_Preorder'46'constructor_233 (AgdaAny -> AgdaAny)
                                  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Energy.Energy.Preorder.S
d_S_28 :: T_Preorder_8 -> ()
d_S_28 = erased
-- DASHI.Energy.Energy.Preorder._≤_
d__'8804'__30 :: T_Preorder_8 -> AgdaAny -> AgdaAny -> ()
d__'8804'__30 = erased
-- DASHI.Energy.Energy.Preorder.refl≤
d_refl'8804'_34 :: T_Preorder_8 -> AgdaAny -> AgdaAny
d_refl'8804'_34 v0
  = case coe v0 of
      C_Preorder'46'constructor_233 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Energy.Energy.Preorder.trans≤
d_trans'8804'_42 ::
  T_Preorder_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8804'_42 v0
  = case coe v0 of
      C_Preorder'46'constructor_233 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Energy.Energy.EnergySpace
d_EnergySpace_52 a0 a1 a2 a3 = ()
data T_EnergySpace_52
  = C_EnergySpace'46'constructor_881 (AgdaAny -> AgdaAny -> AgdaAny)
                                     (AgdaAny -> AgdaAny)
-- DASHI.Energy.Energy._._≤_
d__'8804'__64 :: T_Preorder_8 -> AgdaAny -> AgdaAny -> ()
d__'8804'__64 = erased
-- DASHI.Energy.Energy._.S
d_S_66 :: T_Preorder_8 -> ()
d_S_66 = erased
-- DASHI.Energy.Energy._.refl≤
d_refl'8804'_68 :: T_Preorder_8 -> AgdaAny -> AgdaAny
d_refl'8804'_68 v0 = coe d_refl'8804'_34 (coe v0)
-- DASHI.Energy.Energy._.trans≤
d_trans'8804'_70 ::
  T_Preorder_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8804'_70 v0 = coe d_trans'8804'_42 (coe v0)
-- DASHI.Energy.Energy.EnergySpace._._≤_
d__'8804'__86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Preorder_8 -> T_EnergySpace_52 -> AgdaAny -> AgdaAny -> ()
d__'8804'__86 = erased
-- DASHI.Energy.Energy.EnergySpace._.S
d_S_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Preorder_8 -> T_EnergySpace_52 -> ()
d_S_88 = erased
-- DASHI.Energy.Energy.EnergySpace._.refl≤
d_refl'8804'_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Preorder_8 -> T_EnergySpace_52 -> AgdaAny -> AgdaAny
d_refl'8804'_90 ~v0 ~v1 ~v2 v3 ~v4 = du_refl'8804'_90 v3
du_refl'8804'_90 :: T_Preorder_8 -> AgdaAny -> AgdaAny
du_refl'8804'_90 v0 = coe d_refl'8804'_34 (coe v0)
-- DASHI.Energy.Energy.EnergySpace._.trans≤
d_trans'8804'_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Preorder_8 ->
  T_EnergySpace_52 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8804'_92 ~v0 ~v1 ~v2 v3 ~v4 = du_trans'8804'_92 v3
du_trans'8804'_92 ::
  T_Preorder_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans'8804'_92 v0 = coe d_trans'8804'_42 (coe v0)
-- DASHI.Energy.Energy.EnergySpace.E
d_E_94 :: T_EnergySpace_52 -> AgdaAny -> AgdaAny -> AgdaAny
d_E_94 v0
  = case coe v0 of
      C_EnergySpace'46'constructor_881 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Energy.Energy.EnergySpace.E-refl
d_E'45'refl_98 :: T_EnergySpace_52 -> AgdaAny -> AgdaAny
d_E'45'refl_98 v0
  = case coe v0 of
      C_EnergySpace'46'constructor_881 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Energy.Energy.EnergySpace.E-sep
d_E'45'sep_104 ::
  T_EnergySpace_52 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E'45'sep_104 = erased

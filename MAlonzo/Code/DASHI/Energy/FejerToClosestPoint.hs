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

module MAlonzo.Code.DASHI.Energy.FejerToClosestPoint where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.DASHI.Energy.ClosestPoint
import qualified MAlonzo.Code.DASHI.Energy.Energy

-- DASHI.Energy.FejerToClosestPoint.FejerClosestAxioms
d_FejerClosestAxioms_18 a0 a1 a2 a3 a4 a5 = ()
data T_FejerClosestAxioms_18
  = C_FejerClosestAxioms'46'constructor_1185 MAlonzo.Code.DASHI.Energy.ClosestPoint.T_FejerMonotone_52
                                             (AgdaAny ->
                                              AgdaAny ->
                                              MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                                              AgdaAny)
-- DASHI.Energy.FejerToClosestPoint.FejerClosestAxioms.fejer
d_fejer_40 ::
  T_FejerClosestAxioms_18 ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_FejerMonotone_52
d_fejer_40 v0
  = case coe v0 of
      C_FejerClosestAxioms'46'constructor_1185 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Energy.FejerToClosestPoint.FejerClosestAxioms.fejer⇒closest
d_fejer'8658'closest_46 ::
  T_FejerClosestAxioms_18 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fejer'8658'closest_46 v0
  = case coe v0 of
      C_FejerClosestAxioms'46'constructor_1185 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Energy.FejerToClosestPoint.closestFromFejer
d_closestFromFejer_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.DASHI.Energy.Energy.T_Preorder_8 ->
  MAlonzo.Code.DASHI.Energy.Energy.T_EnergySpace_52 ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_Projection_10 ->
  T_FejerClosestAxioms_18 ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_ClosestPoint_126
d_closestFromFejer_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_closestFromFejer_62 v6
du_closestFromFejer_62 ::
  T_FejerClosestAxioms_18 ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_ClosestPoint_126
du_closestFromFejer_62 v0
  = coe
      MAlonzo.Code.DASHI.Energy.ClosestPoint.C_ClosestPoint'46'constructor_3867
      (coe d_fejer'8658'closest_46 (coe v0))
-- DASHI.Energy.FejerToClosestPoint.Fejer→ClosestPoint
d_Fejer'8594'ClosestPoint_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.DASHI.Energy.Energy.T_Preorder_8 ->
  MAlonzo.Code.DASHI.Energy.Energy.T_EnergySpace_52 ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_Projection_10 ->
  T_FejerClosestAxioms_18 ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_ClosestPoint_126
d_Fejer'8594'ClosestPoint_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_Fejer'8594'ClosestPoint_82 v6
du_Fejer'8594'ClosestPoint_82 ::
  T_FejerClosestAxioms_18 ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_ClosestPoint_126
du_Fejer'8594'ClosestPoint_82 v0
  = coe du_closestFromFejer_62 (coe v0)

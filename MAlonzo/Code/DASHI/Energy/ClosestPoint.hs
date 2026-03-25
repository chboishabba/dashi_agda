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

module MAlonzo.Code.DASHI.Energy.ClosestPoint where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.DASHI.Energy.Energy

-- DASHI.Energy.ClosestPoint.Projection
d_Projection_10 a0 a1 = ()
newtype T_Projection_10
  = C_Projection'46'constructor_105 (AgdaAny -> AgdaAny)
-- DASHI.Energy.ClosestPoint.Projection.P
d_P_22 :: T_Projection_10 -> AgdaAny -> AgdaAny
d_P_22 v0
  = case coe v0 of
      C_Projection'46'constructor_105 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Energy.ClosestPoint.Projection.idem
d_idem_26 ::
  T_Projection_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_26 = erased
-- DASHI.Energy.ClosestPoint.FixP
d_FixP_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Projection_10 -> AgdaAny -> ()
d_FixP_32 = erased
-- DASHI.Energy.ClosestPoint.FejerMonotone
d_FejerMonotone_52 a0 a1 a2 a3 a4 a5 = ()
newtype T_FejerMonotone_52
  = C_FejerMonotone'46'constructor_1661 (AgdaAny ->
                                         AgdaAny ->
                                         MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                                         AgdaAny)
-- DASHI.Energy.ClosestPoint.FejerMonotone.fejer
d_fejer_112 ::
  T_FejerMonotone_52 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fejer_112 v0
  = case coe v0 of
      C_FejerMonotone'46'constructor_1661 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Energy.ClosestPoint.ClosestPoint
d_ClosestPoint_126 a0 a1 a2 a3 a4 a5 = ()
newtype T_ClosestPoint_126
  = C_ClosestPoint'46'constructor_3867 (AgdaAny ->
                                        AgdaAny ->
                                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny)
-- DASHI.Energy.ClosestPoint.ClosestPoint.closest
d_closest_186 ::
  T_ClosestPoint_126 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_closest_186 v0
  = case coe v0 of
      C_ClosestPoint'46'constructor_3867 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Energy.ClosestPoint.FejerImpliesClosest
d_FejerImpliesClosest_202 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T_FejerImpliesClosest_202
  = C_FejerImpliesClosest'46'constructor_5269 T_ClosestPoint_126
-- DASHI.Energy.ClosestPoint.FejerImpliesClosest.proof
d_proof_220 :: T_FejerImpliesClosest_202 -> T_ClosestPoint_126
d_proof_220 v0
  = case coe v0 of
      C_FejerImpliesClosest'46'constructor_5269 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError

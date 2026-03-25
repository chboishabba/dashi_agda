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

module MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

-- DASHI.MDL.MDLDescentTradeoff.AddMonoid
d_AddMonoid_8 a0 = ()
data T_AddMonoid_8
  = C_AddMonoid'46'constructor_23 (AgdaAny -> AgdaAny -> AgdaAny)
                                  AgdaAny
-- DASHI.MDL.MDLDescentTradeoff.AddMonoid.N
d_N_18 :: T_AddMonoid_8 -> ()
d_N_18 = erased
-- DASHI.MDL.MDLDescentTradeoff.AddMonoid._+_
d__'43'__20 :: T_AddMonoid_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__20 v0
  = case coe v0 of
      C_AddMonoid'46'constructor_23 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.AddMonoid.0#
d_0'35'_22 :: T_AddMonoid_8 -> AgdaAny
d_0'35'_22 v0
  = case coe v0 of
      C_AddMonoid'46'constructor_23 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.OrderedMonoid
d_OrderedMonoid_26 a0 = ()
data T_OrderedMonoid_26
  = C_OrderedMonoid'46'constructor_761 T_AddMonoid_8
                                       (AgdaAny -> AgdaAny)
                                       (AgdaAny ->
                                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                       (AgdaAny ->
                                        AgdaAny ->
                                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.MDL.MDLDescentTradeoff.OrderedMonoid.M
d_M_56 :: T_OrderedMonoid_26 -> T_AddMonoid_8
d_M_56 v0
  = case coe v0 of
      C_OrderedMonoid'46'constructor_761 v1 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.OrderedMonoid._≤_
d__'8804'__58 :: T_OrderedMonoid_26 -> AgdaAny -> AgdaAny -> ()
d__'8804'__58 = erased
-- DASHI.MDL.MDLDescentTradeoff.OrderedMonoid.refl≤
d_refl'8804'_62 :: T_OrderedMonoid_26 -> AgdaAny -> AgdaAny
d_refl'8804'_62 v0
  = case coe v0 of
      C_OrderedMonoid'46'constructor_761 v1 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.OrderedMonoid.trans≤
d_trans'8804'_70 ::
  T_OrderedMonoid_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8804'_70 v0
  = case coe v0 of
      C_OrderedMonoid'46'constructor_761 v1 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.OrderedMonoid.mono+
d_mono'43'_80 ::
  T_OrderedMonoid_26 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono'43'_80 v0
  = case coe v0 of
      C_OrderedMonoid'46'constructor_761 v1 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.MDLParts
d_MDLParts_90 a0 a1 a2 a3 = ()
data T_MDLParts_90
  = C_MDLParts'46'constructor_1861 (AgdaAny -> AgdaAny)
                                   (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                   (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- DASHI.MDL.MDLDescentTradeoff._._+_
d__'43'__102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_OrderedMonoid_26 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__102 ~v0 ~v1 ~v2 v3 = du__'43'__102 v3
du__'43'__102 ::
  T_OrderedMonoid_26 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__102 v0 = coe d__'43'__20 (coe d_M_56 (coe v0))
-- DASHI.MDL.MDLDescentTradeoff._.0#
d_0'35'_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_OrderedMonoid_26 -> AgdaAny
d_0'35'_104 ~v0 ~v1 ~v2 v3 = du_0'35'_104 v3
du_0'35'_104 :: T_OrderedMonoid_26 -> AgdaAny
du_0'35'_104 v0 = coe d_0'35'_22 (coe d_M_56 (coe v0))
-- DASHI.MDL.MDLDescentTradeoff._.N
d_N_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_OrderedMonoid_26 -> ()
d_N_106 = erased
-- DASHI.MDL.MDLDescentTradeoff.MDLParts._._+_
d__'43'__126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__126 ~v0 ~v1 ~v2 v3 ~v4 = du__'43'__126 v3
du__'43'__126 ::
  T_OrderedMonoid_26 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__126 v0 = coe d__'43'__20 (coe d_M_56 (coe v0))
-- DASHI.MDL.MDLDescentTradeoff.MDLParts._.0#
d_0'35'_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_OrderedMonoid_26 -> T_MDLParts_90 -> AgdaAny
d_0'35'_128 ~v0 ~v1 ~v2 v3 ~v4 = du_0'35'_128 v3
du_0'35'_128 :: T_OrderedMonoid_26 -> AgdaAny
du_0'35'_128 v0 = coe d_0'35'_22 (coe d_M_56 (coe v0))
-- DASHI.MDL.MDLDescentTradeoff.MDLParts._.N
d_N_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_OrderedMonoid_26 -> T_MDLParts_90 -> ()
d_N_130 = erased
-- DASHI.MDL.MDLDescentTradeoff.MDLParts.P
d_P_132 :: T_MDLParts_90 -> AgdaAny -> AgdaAny
d_P_132 v0
  = case coe v0 of
      C_MDLParts'46'constructor_1861 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.MDLParts.D
d_D_134 :: T_MDLParts_90 -> AgdaAny -> AgdaAny
d_D_134 v0
  = case coe v0 of
      C_MDLParts'46'constructor_1861 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.MDLParts.T
d_T_136 :: T_MDLParts_90 -> AgdaAny -> AgdaAny
d_T_136 v0
  = case coe v0 of
      C_MDLParts'46'constructor_1861 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.MDLParts.ModelLen
d_ModelLen_138 :: T_MDLParts_90 -> AgdaAny -> AgdaAny
d_ModelLen_138 v0
  = case coe v0 of
      C_MDLParts'46'constructor_1861 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.MDLParts.ResidLen
d_ResidLen_140 :: T_MDLParts_90 -> AgdaAny -> AgdaAny
d_ResidLen_140 v0
  = case coe v0 of
      C_MDLParts'46'constructor_1861 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.MDLParts.MDL
d_MDL_142 :: T_MDLParts_90 -> AgdaAny -> AgdaAny
d_MDL_142 v0
  = case coe v0 of
      C_MDLParts'46'constructor_1861 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.MDLParts.MDL-def
d_MDL'45'def_146 ::
  T_MDLParts_90 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_MDL'45'def_146 = erased
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma
d_TradeoffLemma_158 a0 a1 a2 a3 a4 = ()
data T_TradeoffLemma_158
  = C_TradeoffLemma'46'constructor_4549 (AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny)
-- DASHI.MDL.MDLDescentTradeoff._._≤_
d__'8804'__172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 -> T_MDLParts_90 -> AgdaAny -> AgdaAny -> ()
d__'8804'__172 = erased
-- DASHI.MDL.MDLDescentTradeoff._.M
d_M_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_OrderedMonoid_26 -> T_MDLParts_90 -> T_AddMonoid_8
d_M_174 ~v0 ~v1 ~v2 v3 ~v4 = du_M_174 v3
du_M_174 :: T_OrderedMonoid_26 -> T_AddMonoid_8
du_M_174 v0 = coe d_M_56 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff._.mono+
d_mono'43'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono'43'_176 ~v0 ~v1 ~v2 v3 ~v4 = du_mono'43'_176 v3
du_mono'43'_176 ::
  T_OrderedMonoid_26 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mono'43'_176 v0 = coe d_mono'43'_80 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff._.refl≤
d_refl'8804'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_OrderedMonoid_26 -> T_MDLParts_90 -> AgdaAny -> AgdaAny
d_refl'8804'_178 ~v0 ~v1 ~v2 v3 ~v4 = du_refl'8804'_178 v3
du_refl'8804'_178 :: T_OrderedMonoid_26 -> AgdaAny -> AgdaAny
du_refl'8804'_178 v0 = coe d_refl'8804'_62 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff._.trans≤
d_trans'8804'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8804'_180 ~v0 ~v1 ~v2 v3 ~v4 = du_trans'8804'_180 v3
du_trans'8804'_180 ::
  T_OrderedMonoid_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans'8804'_180 v0 = coe d_trans'8804'_70 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff._._+_
d__'43'__184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__184 ~v0 ~v1 ~v2 v3 ~v4 = du__'43'__184 v3
du__'43'__184 ::
  T_OrderedMonoid_26 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__184 v0 = coe d__'43'__20 (coe d_M_56 (coe v0))
-- DASHI.MDL.MDLDescentTradeoff._.0#
d_0'35'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_OrderedMonoid_26 -> T_MDLParts_90 -> AgdaAny
d_0'35'_186 ~v0 ~v1 ~v2 v3 ~v4 = du_0'35'_186 v3
du_0'35'_186 :: T_OrderedMonoid_26 -> AgdaAny
du_0'35'_186 v0 = coe d_0'35'_22 (coe d_M_56 (coe v0))
-- DASHI.MDL.MDLDescentTradeoff._.N
d_N_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_OrderedMonoid_26 -> T_MDLParts_90 -> ()
d_N_188 = erased
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma._._≤_
d__'8804'__200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> T_TradeoffLemma_158 -> AgdaAny -> AgdaAny -> ()
d__'8804'__200 = erased
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma._.M
d_M_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> T_TradeoffLemma_158 -> T_AddMonoid_8
d_M_202 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_M_202 v3
du_M_202 :: T_OrderedMonoid_26 -> T_AddMonoid_8
du_M_202 v0 = coe d_M_56 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma._.mono+
d_mono'43'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 ->
  T_TradeoffLemma_158 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono'43'_204 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_mono'43'_204 v3
du_mono'43'_204 ::
  T_OrderedMonoid_26 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mono'43'_204 v0 = coe d_mono'43'_80 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma._.refl≤
d_refl'8804'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> T_TradeoffLemma_158 -> AgdaAny -> AgdaAny
d_refl'8804'_206 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_refl'8804'_206 v3
du_refl'8804'_206 :: T_OrderedMonoid_26 -> AgdaAny -> AgdaAny
du_refl'8804'_206 v0 = coe d_refl'8804'_62 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma._.trans≤
d_trans'8804'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 ->
  T_TradeoffLemma_158 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8804'_208 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_trans'8804'_208 v3
du_trans'8804'_208 ::
  T_OrderedMonoid_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans'8804'_208 v0 = coe d_trans'8804'_70 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma._._+_
d__'43'__212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 ->
  T_TradeoffLemma_158 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__212 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du__'43'__212 v3
du__'43'__212 ::
  T_OrderedMonoid_26 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__212 v0 = coe d__'43'__20 (coe d_M_56 (coe v0))
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma._.0#
d_0'35'_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> T_TradeoffLemma_158 -> AgdaAny
d_0'35'_214 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_0'35'_214 v3
du_0'35'_214 :: T_OrderedMonoid_26 -> AgdaAny
du_0'35'_214 v0 = coe d_0'35'_22 (coe d_M_56 (coe v0))
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma._.N
d_N_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 -> T_MDLParts_90 -> T_TradeoffLemma_158 -> ()
d_N_216 = erased
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma.model-drop
d_model'45'drop_220 :: T_TradeoffLemma_158 -> AgdaAny -> AgdaAny
d_model'45'drop_220 v0
  = case coe v0 of
      C_TradeoffLemma'46'constructor_4549 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.TradeoffLemma.resid-drop
d_resid'45'drop_224 :: T_TradeoffLemma_158 -> AgdaAny -> AgdaAny
d_resid'45'drop_224 v0
  = case coe v0 of
      C_TradeoffLemma'46'constructor_4549 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.MDL.MDLDescentTradeoff.MDLDescent
d_MDLDescent_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> T_TradeoffLemma_158 -> AgdaAny -> AgdaAny
d_MDLDescent_240 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_MDLDescent_240 v3 v4 v5 v6
du_MDLDescent_240 ::
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> T_TradeoffLemma_158 -> AgdaAny -> AgdaAny
du_MDLDescent_240 v0 v1 v2 v3
  = coe
      d_mono'43'_80 v0
      (coe d_ModelLen_138 v1 (coe d_P_132 v1 (coe d_T_136 v1 v3)))
      (coe d_ModelLen_138 v1 (coe d_P_132 v1 v3))
      (coe d_ResidLen_140 v1 (coe d_D_134 v1 (coe d_T_136 v1 v3)))
      (coe d_ResidLen_140 v1 (coe d_D_134 v1 v3))
      (coe d_model'45'drop_220 v2 v3) (coe d_resid'45'drop_224 v2 v3)
-- DASHI.MDL.MDLDescentTradeoff._._≤_
d__'8804'__252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 ->
  T_TradeoffLemma_158 -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d__'8804'__252 = erased
-- DASHI.MDL.MDLDescentTradeoff._.M
d_M_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> T_TradeoffLemma_158 -> AgdaAny -> T_AddMonoid_8
d_M_254 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_M_254 v3
du_M_254 :: T_OrderedMonoid_26 -> T_AddMonoid_8
du_M_254 v0 = coe d_M_56 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff._.mono+
d_mono'43'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 ->
  T_TradeoffLemma_158 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono'43'_256 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_mono'43'_256 v3
du_mono'43'_256 ::
  T_OrderedMonoid_26 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mono'43'_256 v0 = coe d_mono'43'_80 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff._.refl≤
d_refl'8804'_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 ->
  T_TradeoffLemma_158 -> AgdaAny -> AgdaAny -> AgdaAny
d_refl'8804'_258 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_refl'8804'_258 v3
du_refl'8804'_258 :: T_OrderedMonoid_26 -> AgdaAny -> AgdaAny
du_refl'8804'_258 v0 = coe d_refl'8804'_62 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff._.trans≤
d_trans'8804'_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 ->
  T_TradeoffLemma_158 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8804'_260 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_trans'8804'_260 v3
du_trans'8804'_260 ::
  T_OrderedMonoid_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans'8804'_260 v0 = coe d_trans'8804'_70 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff._._+_
d__'43'__264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 ->
  T_TradeoffLemma_158 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__264 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du__'43'__264 v3
du__'43'__264 ::
  T_OrderedMonoid_26 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__264 v0 = coe d__'43'__20 (coe d_M_56 (coe v0))
-- DASHI.MDL.MDLDescentTradeoff._.0#
d_0'35'_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> T_TradeoffLemma_158 -> AgdaAny -> AgdaAny
d_0'35'_266 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_0'35'_266 v3
du_0'35'_266 :: T_OrderedMonoid_26 -> AgdaAny
du_0'35'_266 v0 = coe d_0'35'_22 (coe d_M_56 (coe v0))
-- DASHI.MDL.MDLDescentTradeoff._.N
d_N_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_OrderedMonoid_26 ->
  T_MDLParts_90 -> T_TradeoffLemma_158 -> AgdaAny -> ()
d_N_268 = erased
-- DASHI.MDL.MDLDescentTradeoff._.model-drop
d_model'45'drop_272 ::
  T_TradeoffLemma_158 -> AgdaAny -> AgdaAny -> AgdaAny
d_model'45'drop_272 v0 ~v1 = du_model'45'drop_272 v0
du_model'45'drop_272 :: T_TradeoffLemma_158 -> AgdaAny -> AgdaAny
du_model'45'drop_272 v0 = coe d_model'45'drop_220 (coe v0)
-- DASHI.MDL.MDLDescentTradeoff._.resid-drop
d_resid'45'drop_274 ::
  T_TradeoffLemma_158 -> AgdaAny -> AgdaAny -> AgdaAny
d_resid'45'drop_274 v0 ~v1 = du_resid'45'drop_274 v0
du_resid'45'drop_274 :: T_TradeoffLemma_158 -> AgdaAny -> AgdaAny
du_resid'45'drop_274 v0 = coe d_resid'45'drop_224 (coe v0)

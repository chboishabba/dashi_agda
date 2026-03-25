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

module MAlonzo.Code.Contraction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Ultrametric

-- Contraction._≢_
d__'8802'__4 :: () -> AgdaAny -> AgdaAny -> ()
d__'8802'__4 = erased
-- Contraction.Contractive
d_Contractive_16 a0 a1 a2 = ()
newtype T_Contractive_16
  = C_Contractive'46'constructor_297 (AgdaAny ->
                                      AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Contraction._.d
d_d_26 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> Integer
d_d_26 v0 ~v1 = du_d_26 v0
du_d_26 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  AgdaAny -> AgdaAny -> Integer
du_d_26 v0 = coe MAlonzo.Code.Ultrametric.d_d_30 (coe v0)
-- Contraction.Contractive.contraction
d_contraction_54 ::
  T_Contractive_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_contraction_54 v0
  = case coe v0 of
      C_Contractive'46'constructor_297 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Contraction.Contractive≢
d_Contractive'8802'_62 a0 a1 a2 = ()
newtype T_Contractive'8802'_62
  = C_Contractive'8802''46'constructor_849 (AgdaAny ->
                                            AgdaAny ->
                                            (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                                             MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
                                            MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Contraction._.d
d_d_72 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> Integer
d_d_72 v0 ~v1 = du_d_72 v0
du_d_72 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  AgdaAny -> AgdaAny -> Integer
du_d_72 v0 = coe MAlonzo.Code.Ultrametric.d_d_30 (coe v0)
-- Contraction.Contractive≢.contraction≢
d_contraction'8802'_100 ::
  T_Contractive'8802'_62 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_contraction'8802'_100 v0
  = case coe v0 of
      C_Contractive'8802''46'constructor_849 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Contraction.StrictContraction
d_StrictContraction_108 a0 a1 a2 = ()
data T_StrictContraction_108
  = C_StrictContraction'46'constructor_1559 T_Contractive'8802'_62
                                            AgdaAny
-- Contraction.StrictContraction.contractive≢
d_contractive'8802'_126 ::
  T_StrictContraction_108 -> T_Contractive'8802'_62
d_contractive'8802'_126 v0
  = case coe v0 of
      C_StrictContraction'46'constructor_1559 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Contraction.StrictContraction.fp
d_fp_128 :: T_StrictContraction_108 -> AgdaAny
d_fp_128 v0
  = case coe v0 of
      C_StrictContraction'46'constructor_1559 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Contraction.StrictContraction.fixed
d_fixed_130 ::
  T_StrictContraction_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fixed_130 = erased
-- Contraction.StrictContraction.unique
d_unique_134 ::
  T_StrictContraction_108 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique_134 = erased

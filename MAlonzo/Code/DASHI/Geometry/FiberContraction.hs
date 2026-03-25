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

module MAlonzo.Code.DASHI.Geometry.FiberContraction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Ultrametric

-- DASHI.Geometry.FiberContraction._≢_
d__'8802'__8 :: () -> AgdaAny -> AgdaAny -> ()
d__'8802'__8 = erased
-- DASHI.Geometry.FiberContraction.FiberDistinct
d_FiberDistinct_22 a0 a1 a2 a3 = ()
data T_FiberDistinct_22 = C_FiberDistinct'46'constructor_237
-- DASHI.Geometry.FiberContraction.FiberDistinct.x≢y
d_x'8802'y_36 ::
  T_FiberDistinct_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_x'8802'y_36 = erased
-- DASHI.Geometry.FiberContraction.FiberDistinct.sameFiber
d_sameFiber_38 ::
  T_FiberDistinct_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sameFiber_38 = erased
-- DASHI.Geometry.FiberContraction.ContractiveOnFibers
d_ContractiveOnFibers_46 a0 a1 a2 = ()
newtype T_ContractiveOnFibers_46
  = C_ContractiveOnFibers'46'constructor_559 (AgdaAny ->
                                              AgdaAny ->
                                              T_FiberDistinct_22 ->
                                              MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- DASHI.Geometry.FiberContraction._.d
d_d_56 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> Integer
d_d_56 v0 ~v1 = du_d_56 v0
du_d_56 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  AgdaAny -> AgdaAny -> Integer
du_d_56 v0 = coe MAlonzo.Code.Ultrametric.d_d_30 (coe v0)
-- DASHI.Geometry.FiberContraction.ContractiveOnFibers.contractFiber
d_contractFiber_84 ::
  T_ContractiveOnFibers_46 ->
  AgdaAny ->
  AgdaAny ->
  T_FiberDistinct_22 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_contractFiber_84 v0
  = case coe v0 of
      C_ContractiveOnFibers'46'constructor_559 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError

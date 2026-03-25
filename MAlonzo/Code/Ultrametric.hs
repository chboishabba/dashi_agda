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

module MAlonzo.Code.Ultrametric where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Nat.Base

-- Ultrametric.max
d_max_2 :: Integer -> Integer -> Integer
d_max_2 = coe MAlonzo.Code.Data.Nat.Base.d__'8852'__204
-- Ultrametric.Ultrametric
d_Ultrametric_6 a0 = ()
data T_Ultrametric_6
  = C_Ultrametric'46'constructor_391 (AgdaAny -> AgdaAny -> Integer)
                                     (AgdaAny ->
                                      AgdaAny ->
                                      AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Ultrametric.Ultrametric.d
d_d_30 :: T_Ultrametric_6 -> AgdaAny -> AgdaAny -> Integer
d_d_30 v0
  = case coe v0 of
      C_Ultrametric'46'constructor_391 v1 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ultrametric.Ultrametric.id-zero
d_id'45'zero_34 ::
  T_Ultrametric_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_id'45'zero_34 = erased
-- Ultrametric.Ultrametric.symmetric
d_symmetric_40 ::
  T_Ultrametric_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_symmetric_40 = erased
-- Ultrametric.Ultrametric.ultratriangle
d_ultratriangle_48 ::
  T_Ultrametric_6 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ultratriangle_48 v0
  = case coe v0 of
      C_Ultrametric'46'constructor_391 v1 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError

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

module MAlonzo.Code.DASHI.Geometry.TimeOrientation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Nat.Base

-- DASHI.Geometry.TimeOrientation.TimeOrientation
d_TimeOrientation_10 a0 a1 = ()
data T_TimeOrientation_10
  = C_TimeOrientation'46'constructor_59 (AgdaAny -> Integer)
                                        (AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- DASHI.Geometry.TimeOrientation.TimeOrientation.Lyap
d_Lyap_24 :: T_TimeOrientation_10 -> AgdaAny -> Integer
d_Lyap_24 v0
  = case coe v0 of
      C_TimeOrientation'46'constructor_59 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.TimeOrientation.TimeOrientation.mono
d_mono_28 ::
  T_TimeOrientation_10 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mono_28 v0
  = case coe v0 of
      C_TimeOrientation'46'constructor_59 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.TimeOrientation.TimeOrientation.strictUnlessFixed
d_strictUnlessFixed_30 :: T_TimeOrientation_10 -> ()
d_strictUnlessFixed_30 = erased

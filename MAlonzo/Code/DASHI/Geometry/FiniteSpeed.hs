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

module MAlonzo.Code.DASHI.Geometry.FiniteSpeed where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Unit

-- DASHI.Geometry.FiniteSpeed.FiniteSpeed
d_FiniteSpeed_10 a0 a1 = ()
newtype T_FiniteSpeed_10
  = C_FiniteSpeed'46'constructor_107 (AgdaAny ->
                                      AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Geometry.FiniteSpeed.FiniteSpeed.local
d_local_24 :: T_FiniteSpeed_10 -> AgdaAny -> AgdaAny -> ()
d_local_24 = erased
-- DASHI.Geometry.FiniteSpeed.FiniteSpeed.preservesLocality
d_preservesLocality_30 ::
  T_FiniteSpeed_10 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_preservesLocality_30 v0
  = case coe v0 of
      C_FiniteSpeed'46'constructor_107 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.FiniteSpeed.trivialFiniteSpeed
d_trivialFiniteSpeed_36 ::
  () -> (AgdaAny -> AgdaAny) -> T_FiniteSpeed_10
d_trivialFiniteSpeed_36 ~v0 ~v1 = du_trivialFiniteSpeed_36
du_trivialFiniteSpeed_36 :: T_FiniteSpeed_10
du_trivialFiniteSpeed_36
  = coe
      C_FiniteSpeed'46'constructor_107
      (\ v0 v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)

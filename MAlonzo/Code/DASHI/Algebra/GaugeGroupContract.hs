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

module MAlonzo.Code.DASHI.Algebra.GaugeGroupContract where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality

-- DASHI.Algebra.GaugeGroupContract.Gauge
d_Gauge_6 = ()
data T_Gauge_6 = C_SU3'215'SU2'215'U1_8 | C_Other_10
-- DASHI.Algebra.GaugeGroupContract.Emergence
d_Emergence_14 a0 = ()
newtype T_Emergence_14
  = C_Emergence'46'constructor_5 (AgdaAny -> T_Gauge_6)
-- DASHI.Algebra.GaugeGroupContract.Emergence.pickGauge
d_pickGauge_20 :: T_Emergence_14 -> AgdaAny -> T_Gauge_6
d_pickGauge_20 v0
  = case coe v0 of
      C_Emergence'46'constructor_5 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Algebra.GaugeGroupContract.UniquenessClaim
d_UniquenessClaim_24 a0 = ()
data T_UniquenessClaim_24
  = C_UniquenessClaim'46'constructor_221 T_Emergence_14
                                         (AgdaAny -> Bool)
-- DASHI.Algebra.GaugeGroupContract.UniquenessClaim.E
d_E_36 :: T_UniquenessClaim_24 -> T_Emergence_14
d_E_36 v0
  = case coe v0 of
      C_UniquenessClaim'46'constructor_221 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Algebra.GaugeGroupContract.UniquenessClaim.admissible
d_admissible_38 :: T_UniquenessClaim_24 -> AgdaAny -> Bool
d_admissible_38 v0
  = case coe v0 of
      C_UniquenessClaim'46'constructor_221 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Algebra.GaugeGroupContract.UniquenessClaim.unique-SM
d_unique'45'SM_42 ::
  T_UniquenessClaim_24 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'45'SM_42 = erased

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

module MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Geometry.ParallelogramLaw

-- DASHI.Geometry.ConeMetricCompatibility.Cone
d_Cone_8 a0 = ()
data T_Cone_8 = C_Cone'46'constructor_9
-- DASHI.Geometry.ConeMetricCompatibility.Cone.InCone
d_InCone_34 :: T_Cone_8 -> AgdaAny -> ()
d_InCone_34 = erased
-- DASHI.Geometry.ConeMetricCompatibility.Quadratic
d_Quadratic_38 a0 = ()
newtype T_Quadratic_38
  = C_Quadratic'46'constructor_133 (AgdaAny -> Integer)
-- DASHI.Geometry.ConeMetricCompatibility.Quadratic.Q
d_Q_64 :: T_Quadratic_38 -> AgdaAny -> Integer
d_Q_64 v0
  = case coe v0 of
      C_Quadratic'46'constructor_133 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeMetricCompatibility.ConeMetricCompat
d_ConeMetricCompat_72 a0 a1 a2 = ()
data T_ConeMetricCompat_72 = C_ConeMetricCompat'46'constructor_349
-- DASHI.Geometry.ConeMetricCompatibility._.InCone
d_InCone_92 :: T_Cone_8 -> T_Quadratic_38 -> AgdaAny -> ()
d_InCone_92 = erased
-- DASHI.Geometry.ConeMetricCompatibility._.Q
d_Q_96 :: T_Quadratic_38 -> AgdaAny -> Integer
d_Q_96 v0 = coe d_Q_64 (coe v0)
-- DASHI.Geometry.ConeMetricCompatibility.ConeMetricCompat._.InCone
d_InCone_112 ::
  T_Cone_8 ->
  T_Quadratic_38 -> T_ConeMetricCompat_72 -> AgdaAny -> ()
d_InCone_112 = erased
-- DASHI.Geometry.ConeMetricCompatibility.ConeMetricCompat._.Q
d_Q_116 ::
  T_Cone_8 ->
  T_Quadratic_38 -> T_ConeMetricCompat_72 -> AgdaAny -> Integer
d_Q_116 ~v0 v1 ~v2 = du_Q_116 v1
du_Q_116 :: T_Quadratic_38 -> AgdaAny -> Integer
du_Q_116 v0 = coe d_Q_64 (coe v0)
-- DASHI.Geometry.ConeMetricCompatibility.ConeMetricCompat.compat
d_compat_118 :: T_ConeMetricCompat_72 -> ()
d_compat_118 = erased

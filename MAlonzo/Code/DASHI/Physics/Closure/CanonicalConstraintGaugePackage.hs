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

module MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Algebra.GaugeGroupContract

-- DASHI.Physics.Closure.CanonicalConstraintGaugePackage.CanonicalConstraintGaugePackage
d_CanonicalConstraintGaugePackage_8 = ()
data T_CanonicalConstraintGaugePackage_8
  = C_CanonicalConstraintGaugePackage'46'constructor_829 (AgdaAny ->
                                                          AgdaAny -> AgdaAny)
                                                         (AgdaAny ->
                                                          AgdaAny ->
                                                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                                                         (AgdaAny -> Bool)
                                                         (AgdaAny ->
                                                          MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.T_Gauge_6)
-- DASHI.Physics.Closure.CanonicalConstraintGaugePackage.CanonicalConstraintGaugePackage.Carrier
d_Carrier_36 :: T_CanonicalConstraintGaugePackage_8 -> ()
d_Carrier_36 = erased
-- DASHI.Physics.Closure.CanonicalConstraintGaugePackage.CanonicalConstraintGaugePackage._[_,]_
d__'91'_'44''93'__38 ::
  T_CanonicalConstraintGaugePackage_8 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'91'_'44''93'__38 v0
  = case coe v0 of
      C_CanonicalConstraintGaugePackage'46'constructor_829 v2 v3 v4 v6
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.CanonicalConstraintGaugePackage.CanonicalConstraintGaugePackage.closes
d_closes_46 ::
  T_CanonicalConstraintGaugePackage_8 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closes_46 v0
  = case coe v0 of
      C_CanonicalConstraintGaugePackage'46'constructor_829 v2 v3 v4 v6
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.CanonicalConstraintGaugePackage.CanonicalConstraintGaugePackage.admissible
d_admissible_48 ::
  T_CanonicalConstraintGaugePackage_8 -> AgdaAny -> Bool
d_admissible_48 v0
  = case coe v0 of
      C_CanonicalConstraintGaugePackage'46'constructor_829 v2 v3 v4 v6
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.CanonicalConstraintGaugePackage.CanonicalConstraintGaugePackage.admissibleClosed
d_admissibleClosed_54 ::
  T_CanonicalConstraintGaugePackage_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_admissibleClosed_54 = erased
-- DASHI.Physics.Closure.CanonicalConstraintGaugePackage.CanonicalConstraintGaugePackage.pickGauge
d_pickGauge_56 ::
  T_CanonicalConstraintGaugePackage_8 ->
  AgdaAny -> MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.T_Gauge_6
d_pickGauge_56 v0
  = case coe v0 of
      C_CanonicalConstraintGaugePackage'46'constructor_829 v2 v3 v4 v6
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.CanonicalConstraintGaugePackage.CanonicalConstraintGaugePackage.uniqueGaugeOnAdmissible
d_uniqueGaugeOnAdmissible_60 ::
  T_CanonicalConstraintGaugePackage_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uniqueGaugeOnAdmissible_60 = erased

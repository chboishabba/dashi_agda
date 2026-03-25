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

module MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Algebra.GaugeGroupContract
import qualified MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage
import qualified MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem

-- DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem.ParametricGaugeConstraintBridgeTheorem
d_ParametricGaugeConstraintBridgeTheorem_10 a0 = ()
data T_ParametricGaugeConstraintBridgeTheorem_10
  = C_ParametricGaugeConstraintBridgeTheorem'46'constructor_691 MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.T_ParametricGaugeConstraintTheorem_10
                                                                MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.T_UniquenessClaim_24
-- DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem.ParametricGaugeConstraintBridgeTheorem.gaugeTheorem
d_gaugeTheorem_28 ::
  T_ParametricGaugeConstraintBridgeTheorem_10 ->
  MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.T_ParametricGaugeConstraintTheorem_10
d_gaugeTheorem_28 v0
  = case coe v0 of
      C_ParametricGaugeConstraintBridgeTheorem'46'constructor_691 v1 v2
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem.ParametricGaugeConstraintBridgeTheorem.gaugeContract
d_gaugeContract_30 ::
  T_ParametricGaugeConstraintBridgeTheorem_10 ->
  MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.T_UniquenessClaim_24
d_gaugeContract_30 v0
  = case coe v0 of
      C_ParametricGaugeConstraintBridgeTheorem'46'constructor_691 v1 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem.ParametricGaugeConstraintBridgeTheorem.admissibleClosedOnCarrier
d_admissibleClosedOnCarrier_36 ::
  T_ParametricGaugeConstraintBridgeTheorem_10 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_admissibleClosedOnCarrier_36 = erased
-- DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem.ParametricGaugeConstraintBridgeTheorem.gaugeUniqueOnAdmissibleCarrier
d_gaugeUniqueOnAdmissibleCarrier_40 ::
  T_ParametricGaugeConstraintBridgeTheorem_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gaugeUniqueOnAdmissibleCarrier_40 = erased
-- DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem.parametricGaugeConstraintBridgeTheorem
d_parametricGaugeConstraintBridgeTheorem_44 ::
  MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.T_CanonicalConstraintGaugePackage_8 ->
  T_ParametricGaugeConstraintBridgeTheorem_10
d_parametricGaugeConstraintBridgeTheorem_44 v0
  = coe
      C_ParametricGaugeConstraintBridgeTheorem'46'constructor_691
      (MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_parametricGaugeConstraintTheorem_40
         (coe v0))
      (MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_uniqueness_30
         (coe
            MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_parametricGaugeConstraintTheorem_40
            (coe v0)))

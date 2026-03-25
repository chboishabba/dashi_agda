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

module MAlonzo.Code.DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage
import qualified MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem
import qualified MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem

-- DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem.ParametricAlgebraicClosureTheorem
d_ParametricAlgebraicClosureTheorem_10 a0 = ()
data T_ParametricAlgebraicClosureTheorem_10
  = C_ParametricAlgebraicClosureTheorem'46'constructor_1339 MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.T_ParametricGaugeConstraintTheorem_10
                                                            MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem.T_ParametricGaugeConstraintBridgeTheorem_10
                                                            (AgdaAny ->
                                                             AgdaAny ->
                                                             MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem.ParametricAlgebraicClosureTheorem.gaugeTheorem
d_gaugeTheorem_36 ::
  T_ParametricAlgebraicClosureTheorem_10 ->
  MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.T_ParametricGaugeConstraintTheorem_10
d_gaugeTheorem_36 v0
  = case coe v0 of
      C_ParametricAlgebraicClosureTheorem'46'constructor_1339 v1 v2 v3
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem.ParametricAlgebraicClosureTheorem.bridgeTheorem
d_bridgeTheorem_38 ::
  T_ParametricAlgebraicClosureTheorem_10 ->
  MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem.T_ParametricGaugeConstraintBridgeTheorem_10
d_bridgeTheorem_38 v0
  = case coe v0 of
      C_ParametricAlgebraicClosureTheorem'46'constructor_1339 v1 v2 v3
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem.ParametricAlgebraicClosureTheorem.carrierClosed
d_carrierClosed_46 ::
  T_ParametricAlgebraicClosureTheorem_10 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_carrierClosed_46 v0
  = case coe v0 of
      C_ParametricAlgebraicClosureTheorem'46'constructor_1339 v1 v2 v3
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem.ParametricAlgebraicClosureTheorem.admissibilityClosed
d_admissibilityClosed_52 ::
  T_ParametricAlgebraicClosureTheorem_10 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_admissibilityClosed_52 = erased
-- DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem.ParametricAlgebraicClosureTheorem.gaugeStableOnAdmissible
d_gaugeStableOnAdmissible_56 ::
  T_ParametricAlgebraicClosureTheorem_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gaugeStableOnAdmissible_56 = erased
-- DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem.parametricAlgebraicClosureTheorem
d_parametricAlgebraicClosureTheorem_60 ::
  MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.T_CanonicalConstraintGaugePackage_8 ->
  T_ParametricAlgebraicClosureTheorem_10
d_parametricAlgebraicClosureTheorem_60 v0
  = coe
      C_ParametricAlgebraicClosureTheorem'46'constructor_1339
      (MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_parametricGaugeConstraintTheorem_40
         (coe v0))
      (MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem.d_parametricGaugeConstraintBridgeTheorem_44
         (coe v0))
      (MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.d_closes_46
         (coe v0))

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

module MAlonzo.Code.DASHI.Physics.Closure.EnergyShiftBase where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Energy.ClosestPoint
import qualified MAlonzo.Code.DASHI.Energy.Energy
import qualified MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric
import qualified MAlonzo.Code.DASHI.Physics.TailCollapseProof
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Closure.EnergyShiftBase.NatPreorder
d_NatPreorder_8 :: MAlonzo.Code.DASHI.Energy.Energy.T_Preorder_8
d_NatPreorder_8
  = coe
      MAlonzo.Code.DASHI.Energy.Energy.C_Preorder'46'constructor_233
      (\ v0 ->
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776 (coe v0))
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784)
-- DASHI.Physics.Closure.EnergyShiftBase.energy-sep
d_energy'45'sep_26 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_energy'45'sep_26 = erased
-- DASHI.Physics.Closure.EnergyShiftBase.EnergyShift
d_EnergyShift_56 ::
  Integer ->
  Integer -> MAlonzo.Code.DASHI.Energy.Energy.T_EnergySpace_52
d_EnergyShift_56 v0 v1
  = coe
      MAlonzo.Code.DASHI.Energy.Energy.C_EnergySpace'46'constructor_881
      (MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine_36
         (coe addInt (coe v0) (coe v1)))
      (\ v2 ->
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
           (coe
              MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine_36
              (coe addInt (coe v0) (coe v1)) (coe v2) (coe v2)))
-- DASHI.Physics.Closure.EnergyShiftBase.ProjShift
d_ProjShift_68 ::
  Integer ->
  Integer -> MAlonzo.Code.DASHI.Energy.ClosestPoint.T_Projection_10
d_ProjShift_68 v0 v1
  = coe
      MAlonzo.Code.DASHI.Energy.ClosestPoint.C_Projection'46'constructor_105
      (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_P'7523'_158
         (coe v0) (coe v1))

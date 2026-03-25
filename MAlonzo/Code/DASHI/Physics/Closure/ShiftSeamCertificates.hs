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

module MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Energy.ClosestPoint
import qualified MAlonzo.Code.DASHI.Geometry.DefectCollapse
import qualified MAlonzo.Code.DASHI.Physics.Closure.DefectCollapseShiftInstance
import qualified MAlonzo.Code.DASHI.Physics.Closure.EnergyClosestPointShiftInstance
import qualified MAlonzo.Code.DASHI.Physics.Closure.MDLDescentShiftInstance
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Closure.ShiftSeamCertificates.ShiftSeams
d_ShiftSeams_12 a0 a1 = ()
data T_ShiftSeams_12
  = C_ShiftSeams'46'constructor_751 MAlonzo.Code.DASHI.Energy.ClosestPoint.T_FejerMonotone_52
                                    MAlonzo.Code.DASHI.Energy.ClosestPoint.T_ClosestPoint_126
                                    MAlonzo.Code.DASHI.Geometry.DefectCollapse.T_DefectCollapse_14
                                    (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
                                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- DASHI.Physics.Closure.ShiftSeamCertificates.ShiftSeams.fejer
d_fejer_28 ::
  T_ShiftSeams_12 ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_FejerMonotone_52
d_fejer_28 v0
  = case coe v0 of
      C_ShiftSeams'46'constructor_751 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ShiftSeamCertificates.ShiftSeams.closest
d_closest_30 ::
  T_ShiftSeams_12 ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_ClosestPoint_126
d_closest_30 v0
  = case coe v0 of
      C_ShiftSeams'46'constructor_751 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ShiftSeamCertificates.ShiftSeams.defectCollapse
d_defectCollapse_32 ::
  T_ShiftSeams_12 ->
  MAlonzo.Code.DASHI.Geometry.DefectCollapse.T_DefectCollapse_14
d_defectCollapse_32 v0
  = case coe v0 of
      C_ShiftSeams'46'constructor_751 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ShiftSeamCertificates.ShiftSeams.mdlDescent
d_mdlDescent_36 ::
  T_ShiftSeams_12 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mdlDescent_36 v0
  = case coe v0 of
      C_ShiftSeams'46'constructor_751 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ShiftSeamCertificates.shiftSeams
d_shiftSeams_42 :: Integer -> Integer -> T_ShiftSeams_12
d_shiftSeams_42 v0 v1
  = coe
      C_ShiftSeams'46'constructor_751
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.EnergyClosestPointShiftInstance.d_fejerShift_12
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.EnergyClosestPointShiftInstance.d_closestShift_76
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.DefectCollapseShiftInstance.d_defectCollapseShift_12
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.MDLDescentShiftInstance.d_mdlyapShift_34
         (coe v0) (coe v1))

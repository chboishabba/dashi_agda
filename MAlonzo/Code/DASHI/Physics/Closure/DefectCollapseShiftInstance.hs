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

module MAlonzo.Code.DASHI.Physics.Closure.DefectCollapseShiftInstance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Geometry.DefectCollapse
import qualified MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance
import qualified MAlonzo.Code.DASHI.Physics.TailCollapseProof

-- DASHI.Physics.Closure.DefectCollapseShiftInstance.defectCollapseShift
d_defectCollapseShift_12 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Geometry.DefectCollapse.T_DefectCollapse_14
d_defectCollapseShift_12 v0 v1
  = coe
      MAlonzo.Code.DASHI.Geometry.DefectCollapse.C_DefectCollapse'46'constructor_209
      (\ v2 -> v2)
      (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_T'7523'_228
         (coe v0) (coe v1))
      (\ v2 ->
         coe
           MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance.du_countNZ_34
           (coe
              MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
              (coe v2)))
      (MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance.d_resid'45'drop'45'lemma_212
         (coe v0) (coe v1))

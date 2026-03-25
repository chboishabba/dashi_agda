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

module MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff
import qualified MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Closure.MDLFejerAxiomsShift.Parts
d_Parts_12 ::
  Integer ->
  Integer -> MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.T_MDLParts_90
d_Parts_12 v0 v1
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance.d_MDLPartsShift_346
      (coe v0) (coe v1)
-- DASHI.Physics.Closure.MDLFejerAxiomsShift.Trade
d_Trade_22 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.T_TradeoffLemma_158
d_Trade_22 v0 v1
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance.d_TradeoffShift_366
      (coe v0) (coe v1)
-- DASHI.Physics.Closure.MDLFejerAxiomsShift.MDLFejerAxiomsShift
d_MDLFejerAxiomsShift_28 = ()
newtype T_MDLFejerAxiomsShift_28
  = C_MDLFejerAxiomsShift'46'constructor_453 (Integer ->
                                              Integer ->
                                              MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
                                              MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- DASHI.Physics.Closure.MDLFejerAxiomsShift.MDLFejerAxiomsShift.mdlFejer
d_mdlFejer_44 ::
  T_MDLFejerAxiomsShift_28 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mdlFejer_44 v0
  = case coe v0 of
      C_MDLFejerAxiomsShift'46'constructor_453 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.MDLFejerAxiomsShift.mdlFejerShift
d_mdlFejerShift_46 :: T_MDLFejerAxiomsShift_28
d_mdlFejerShift_46
  = coe
      C_MDLFejerAxiomsShift'46'constructor_453
      (coe
         (\ v0 v1 ->
            coe
              MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.du_MDLDescent_240
              (coe
                 MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance.d_NatOrderedMonoid_8)
              (coe d_Parts_12 (coe v0) (coe v1))
              (coe d_Trade_22 (coe v0) (coe v1))))

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

module MAlonzo.Code.DASHI.Physics.Closure.MDLDescentShiftInstance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff
import qualified MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Closure.MDLDescentShiftInstance.Parts
d_Parts_12 ::
  Integer ->
  Integer -> MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.T_MDLParts_90
d_Parts_12 v0 v1
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance.d_MDLPartsShift_346
      (coe v0) (coe v1)
-- DASHI.Physics.Closure.MDLDescentShiftInstance.Trade
d_Trade_22 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.T_TradeoffLemma_158
d_Trade_22 v0 v1
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance.d_TradeoffShift_366
      (coe v0) (coe v1)
-- DASHI.Physics.Closure.MDLDescentShiftInstance.mdlyapShift
d_mdlyapShift_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mdlyapShift_34 v0 v1
  = coe
      MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.du_MDLDescent_240
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance.d_NatOrderedMonoid_8)
      (coe d_Parts_12 (coe v0) (coe v1))
      (coe d_Trade_22 (coe v0) (coe v1))

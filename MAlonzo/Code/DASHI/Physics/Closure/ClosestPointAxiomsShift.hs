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

module MAlonzo.Code.DASHI.Physics.Closure.ClosestPointAxiomsShift where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Energy.FejerToClosestPoint

-- DASHI.Physics.Closure.ClosestPointAxiomsShift.ClosestPointAxiomsShift
d_ClosestPointAxiomsShift_8 = ()
newtype T_ClosestPointAxiomsShift_8
  = C_ClosestPointAxiomsShift'46'constructor_61 (Integer ->
                                                 Integer ->
                                                 MAlonzo.Code.DASHI.Energy.FejerToClosestPoint.T_FejerClosestAxioms_18)
-- DASHI.Physics.Closure.ClosestPointAxiomsShift.ClosestPointAxiomsShift.closestAxiomShift
d_closestAxiomShift_20 ::
  T_ClosestPointAxiomsShift_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Energy.FejerToClosestPoint.T_FejerClosestAxioms_18
d_closestAxiomShift_20 v0
  = case coe v0 of
      C_ClosestPointAxiomsShift'46'constructor_61 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError

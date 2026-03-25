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

module MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosure where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionDiffusionPair
import qualified MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureStatus
import qualified MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift
import qualified MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates
import qualified MAlonzo.Code.MDL.Core

-- DASHI.Physics.Closure.DynamicalClosure.DynamicalClosure
d_DynamicalClosure_8 = ()
data T_DynamicalClosure_8
  = C_DynamicalClosure'46'constructor_167 (Integer ->
                                           Integer ->
                                           MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates.T_ShiftSeams_12)
                                          (Integer ->
                                           Integer -> MAlonzo.Code.MDL.Core.T_Lyapunov_116)
                                          (Integer ->
                                           Integer ->
                                           MAlonzo.Code.DASHI.Physics.Closure.ContractionDiffusionPair.T_ContractionDiffusionPair_12)
                                          MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift.T_MDLFejerAxiomsShift_28
                                          MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureStatus.T_DynamicalClosureStatus_32
-- DASHI.Physics.Closure.DynamicalClosure.DynamicalClosure.seams
d_seams_36 ::
  T_DynamicalClosure_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates.T_ShiftSeams_12
d_seams_36 v0
  = case coe v0 of
      C_DynamicalClosure'46'constructor_167 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosure.DynamicalClosure.lyapunovShift
d_lyapunovShift_42 ::
  T_DynamicalClosure_8 ->
  Integer -> Integer -> MAlonzo.Code.MDL.Core.T_Lyapunov_116
d_lyapunovShift_42 v0
  = case coe v0 of
      C_DynamicalClosure'46'constructor_167 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosure.DynamicalClosure.contractionDiffusion
d_contractionDiffusion_48 ::
  T_DynamicalClosure_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionDiffusionPair.T_ContractionDiffusionPair_12
d_contractionDiffusion_48 v0
  = case coe v0 of
      C_DynamicalClosure'46'constructor_167 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosure.DynamicalClosure.mdlFejerWitness
d_mdlFejerWitness_50 ::
  T_DynamicalClosure_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift.T_MDLFejerAxiomsShift_28
d_mdlFejerWitness_50 v0
  = case coe v0 of
      C_DynamicalClosure'46'constructor_167 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosure.DynamicalClosure.status
d_status_52 ::
  T_DynamicalClosure_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureStatus.T_DynamicalClosureStatus_32
d_status_52 v0
  = case coe v0 of
      C_DynamicalClosure'46'constructor_167 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError

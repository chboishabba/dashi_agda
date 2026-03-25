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

module MAlonzo.Code.DASHI.Physics.Closure.ClosureObservableWitness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates
import qualified MAlonzo.Code.MDL.Core

-- DASHI.Physics.Closure.ClosureObservableWitness.ClosureObservableWitness
d_ClosureObservableWitness_8 = ()
data T_ClosureObservableWitness_8
  = C_ClosureObservableWitness'46'constructor_331 MAlonzo.Code.Agda.Builtin.String.T_String_6
                                                  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
                                                  Integer [Integer] [Integer]
                                                  (Integer ->
                                                   Integer ->
                                                   MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates.T_ShiftSeams_12)
                                                  (Integer ->
                                                   Integer -> MAlonzo.Code.MDL.Core.T_Lyapunov_116)
-- DASHI.Physics.Closure.ClosureObservableWitness.ClosureObservableWitness.realizationLabel
d_realizationLabel_32 ::
  T_ClosureObservableWitness_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_realizationLabel_32 v0
  = case coe v0 of
      C_ClosureObservableWitness'46'constructor_331 v1 v2 v3 v4 v5 v6 v7
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ClosureObservableWitness.ClosureObservableWitness.provedSignature
d_provedSignature_34 ::
  T_ClosureObservableWitness_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_provedSignature_34 v0
  = case coe v0 of
      C_ClosureObservableWitness'46'constructor_331 v1 v2 v3 v4 v5 v6 v7
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ClosureObservableWitness.ClosureObservableWitness.observedOrientationTag
d_observedOrientationTag_36 ::
  T_ClosureObservableWitness_8 -> Integer
d_observedOrientationTag_36 v0
  = case coe v0 of
      C_ClosureObservableWitness'46'constructor_331 v1 v2 v3 v4 v5 v6 v7
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ClosureObservableWitness.ClosureObservableWitness.observedShell1
d_observedShell1_38 :: T_ClosureObservableWitness_8 -> [Integer]
d_observedShell1_38 v0
  = case coe v0 of
      C_ClosureObservableWitness'46'constructor_331 v1 v2 v3 v4 v5 v6 v7
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ClosureObservableWitness.ClosureObservableWitness.observedShell2
d_observedShell2_40 :: T_ClosureObservableWitness_8 -> [Integer]
d_observedShell2_40 v0
  = case coe v0 of
      C_ClosureObservableWitness'46'constructor_331 v1 v2 v3 v4 v5 v6 v7
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ClosureObservableWitness.ClosureObservableWitness.seams
d_seams_46 ::
  T_ClosureObservableWitness_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates.T_ShiftSeams_12
d_seams_46 v0
  = case coe v0 of
      C_ClosureObservableWitness'46'constructor_331 v1 v2 v3 v4 v5 v6 v7
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ClosureObservableWitness.ClosureObservableWitness.lyapunovShift
d_lyapunovShift_52 ::
  T_ClosureObservableWitness_8 ->
  Integer -> Integer -> MAlonzo.Code.MDL.Core.T_Lyapunov_116
d_lyapunovShift_52 v0
  = case coe v0 of
      C_ClosureObservableWitness'46'constructor_331 v1 v2 v3 v4 v5 v6 v7
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError

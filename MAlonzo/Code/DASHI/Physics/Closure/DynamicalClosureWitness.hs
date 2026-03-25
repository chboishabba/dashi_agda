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

module MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureWitness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization
import qualified MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift
import qualified MAlonzo.Code.DASHI.Physics.Closure.OrthogonalityZ90ZLift
import qualified MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates
import qualified MAlonzo.Code.MDL.Core

-- DASHI.Physics.Closure.DynamicalClosureWitness.DynamicalClosureWitness
d_DynamicalClosureWitness_8 = ()
data T_DynamicalClosureWitness_8
  = C_DynamicalClosureWitness'46'constructor_271 (Integer ->
                                                  Integer ->
                                                  MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates.T_ShiftSeams_12)
                                                 (Integer ->
                                                  Integer ->
                                                  MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates.T_ShiftSeams_12)
                                                 (Integer ->
                                                  Integer -> MAlonzo.Code.MDL.Core.T_Lyapunov_116)
                                                 MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift.T_MDLFejerAxiomsShift_28
                                                 (Integer ->
                                                  MAlonzo.Code.DASHI.Physics.Closure.OrthogonalityZ90ZLift.T_OrthogonalityZLift_10)
                                                 (Integer ->
                                                  MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14)
-- DASHI.Physics.Closure.DynamicalClosureWitness.DynamicalClosureWitness.propagationSeams
d_propagationSeams_42 ::
  T_DynamicalClosureWitness_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates.T_ShiftSeams_12
d_propagationSeams_42 v0
  = case coe v0 of
      C_DynamicalClosureWitness'46'constructor_271 v1 v2 v3 v4 v5 v6
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosureWitness.DynamicalClosureWitness.causalAdmissibilitySeams
d_causalAdmissibilitySeams_48 ::
  T_DynamicalClosureWitness_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Physics.Closure.ShiftSeamCertificates.T_ShiftSeams_12
d_causalAdmissibilitySeams_48 v0
  = case coe v0 of
      C_DynamicalClosureWitness'46'constructor_271 v1 v2 v3 v4 v5 v6
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosureWitness.DynamicalClosureWitness.monotoneLyapunov
d_monotoneLyapunov_54 ::
  T_DynamicalClosureWitness_8 ->
  Integer -> Integer -> MAlonzo.Code.MDL.Core.T_Lyapunov_116
d_monotoneLyapunov_54 v0
  = case coe v0 of
      C_DynamicalClosureWitness'46'constructor_271 v1 v2 v3 v4 v5 v6
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosureWitness.DynamicalClosureWitness.monotoneFejer
d_monotoneFejer_56 ::
  T_DynamicalClosureWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift.T_MDLFejerAxiomsShift_28
d_monotoneFejer_56 v0
  = case coe v0 of
      C_DynamicalClosureWitness'46'constructor_271 v1 v2 v3 v4 v5 v6
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosureWitness.DynamicalClosureWitness.effectiveGeometryOrthogonality
d_effectiveGeometryOrthogonality_60 ::
  T_DynamicalClosureWitness_8 ->
  Integer ->
  MAlonzo.Code.DASHI.Physics.Closure.OrthogonalityZ90ZLift.T_OrthogonalityZLift_10
d_effectiveGeometryOrthogonality_60 v0
  = case coe v0 of
      C_DynamicalClosureWitness'46'constructor_271 v1 v2 v3 v4 v5 v6
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosureWitness.DynamicalClosureWitness.effectiveGeometryPolarization
d_effectiveGeometryPolarization_64 ::
  T_DynamicalClosureWitness_8 ->
  Integer ->
  MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14
d_effectiveGeometryPolarization_64 v0
  = case coe v0 of
      C_DynamicalClosureWitness'46'constructor_271 v1 v2 v3 v4 v5 v6
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError

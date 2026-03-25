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

module MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence

-- DASHI.Geometry.ProjectionDefectToParallelogram.ProjectionDefectParallelogramPackage
d_ProjectionDefectParallelogramPackage_14 a0 a1 a2 a3 = ()
data T_ProjectionDefectParallelogramPackage_14
  = C_ProjectionDefectParallelogramPackage'46'constructor_3753 MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_ProjectionDefect_32
                                                               MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.T_QuadraticEmergenceAxioms_16
-- DASHI.Geometry.ProjectionDefectToParallelogram.ProjectionDefectParallelogramPackage.projection
d_projection_38 ::
  T_ProjectionDefectParallelogramPackage_14 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_ProjectionDefect_32
d_projection_38 v0
  = case coe v0 of
      C_ProjectionDefectParallelogramPackage'46'constructor_3753 v1 v2
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ProjectionDefectToParallelogram.ProjectionDefectParallelogramPackage.emergenceAxioms
d_emergenceAxioms_40 ::
  T_ProjectionDefectParallelogramPackage_14 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.T_QuadraticEmergenceAxioms_16
d_emergenceAxioms_40 v0
  = case coe v0 of
      C_ProjectionDefectParallelogramPackage'46'constructor_3753 v1 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ProjectionDefectToParallelogram.ProjectionDefectParallelogramPackage.parallelogramFromProjection
d_parallelogramFromProjection_46 ::
  T_ProjectionDefectParallelogramPackage_14 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parallelogramFromProjection_46 = erased
-- DASHI.Geometry.ProjectionDefectToParallelogram.ProjectionDefectParallelogramPackage.splitEnergyOnProjectionDefect
d_splitEnergyOnProjectionDefect_50 ::
  T_ProjectionDefectParallelogramPackage_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitEnergyOnProjectionDefect_50 = erased
-- DASHI.Geometry.ProjectionDefectToParallelogram.fromEmergenceAxioms
d_fromEmergenceAxioms_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_ProjectionDefect_32 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.T_QuadraticEmergenceAxioms_16 ->
  T_ProjectionDefectParallelogramPackage_14
d_fromEmergenceAxioms_64 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_fromEmergenceAxioms_64 v4 v5
du_fromEmergenceAxioms_64 ::
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_ProjectionDefect_32 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.T_QuadraticEmergenceAxioms_16 ->
  T_ProjectionDefectParallelogramPackage_14
du_fromEmergenceAxioms_64 v0 v1
  = coe
      C_ProjectionDefectParallelogramPackage'46'constructor_3753 v0 v1
-- DASHI.Geometry.ProjectionDefectToParallelogram.quadraticFromProjectionDefect
d_quadraticFromProjectionDefect_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  T_ProjectionDefectParallelogramPackage_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_quadraticFromProjectionDefect_86 ~v0 ~v1 ~v2 ~v3 v4
  = du_quadraticFromProjectionDefect_86 v4
du_quadraticFromProjectionDefect_86 ::
  T_ProjectionDefectParallelogramPackage_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_quadraticFromProjectionDefect_86 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.du_QuadraticFormEmergence_170
      (coe d_emergenceAxioms_40 (coe v0))
-- DASHI.Geometry.ProjectionDefectToParallelogram.ProjectionDefectQuadraticWitness
d_ProjectionDefectQuadraticWitness_102 a0 a1 a2 a3 = ()
data T_ProjectionDefectQuadraticWitness_102
  = C_ProjectionDefectQuadraticWitness'46'constructor_5559 T_ProjectionDefectParallelogramPackage_14
                                                           MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
                                                           MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
-- DASHI.Geometry.ProjectionDefectToParallelogram.ProjectionDefectQuadraticWitness.package
d_package_118 ::
  T_ProjectionDefectQuadraticWitness_102 ->
  T_ProjectionDefectParallelogramPackage_14
d_package_118 v0
  = case coe v0 of
      C_ProjectionDefectQuadraticWitness'46'constructor_5559 v1 v2 v3
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ProjectionDefectToParallelogram.ProjectionDefectQuadraticWitness.quadratic
d_quadratic_120 ::
  T_ProjectionDefectQuadraticWitness_102 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
d_quadratic_120 v0
  = case coe v0 of
      C_ProjectionDefectQuadraticWitness'46'constructor_5559 v1 v2 v3
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ProjectionDefectToParallelogram.ProjectionDefectQuadraticWitness.witnessToken
d_witnessToken_122 ::
  T_ProjectionDefectQuadraticWitness_102 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_witnessToken_122 v0
  = case coe v0 of
      C_ProjectionDefectQuadraticWitness'46'constructor_5559 v1 v2 v3
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ProjectionDefectToParallelogram.fromProjectionPackageWitness
d_fromProjectionPackageWitness_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  T_ProjectionDefectParallelogramPackage_14 ->
  T_ProjectionDefectQuadraticWitness_102
d_fromProjectionPackageWitness_134 ~v0 ~v1 ~v2 ~v3 v4
  = du_fromProjectionPackageWitness_134 v4
du_fromProjectionPackageWitness_134 ::
  T_ProjectionDefectParallelogramPackage_14 ->
  T_ProjectionDefectQuadraticWitness_102
du_fromProjectionPackageWitness_134 v0
  = coe
      C_ProjectionDefectQuadraticWitness'46'constructor_5559 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_quadraticFromProjectionDefect_86 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_quadraticFromProjectionDefect_86 (coe v0)))

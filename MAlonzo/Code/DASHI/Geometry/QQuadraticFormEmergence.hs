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

module MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence where

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

-- DASHI.Geometry.QuadraticFormEmergence.QuadraticEmergenceAxioms
d_QuadraticEmergenceAxioms_16 a0 a1 a2 a3 a4 = ()
data T_QuadraticEmergenceAxioms_16
  = C_QuadraticEmergenceAxioms'46'constructor_2875 (AgdaAny ->
                                                    AgdaAny)
                                                   (AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Geometry.QuadraticFormEmergence.QuadraticEmergenceAxioms.Energy
d_Energy_130 :: T_QuadraticEmergenceAxioms_16 -> AgdaAny -> AgdaAny
d_Energy_130 v0
  = case coe v0 of
      C_QuadraticEmergenceAxioms'46'constructor_2875 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.QuadraticFormEmergence.QuadraticEmergenceAxioms.Scale
d_Scale_132 ::
  T_QuadraticEmergenceAxioms_16 -> AgdaAny -> AgdaAny -> AgdaAny
d_Scale_132 v0
  = case coe v0 of
      C_QuadraticEmergenceAxioms'46'constructor_2875 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.QuadraticFormEmergence.QuadraticEmergenceAxioms.ParallelogramQ
d_ParallelogramQ_138 ::
  T_QuadraticEmergenceAxioms_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ParallelogramQ_138 = erased
-- DASHI.Geometry.QuadraticFormEmergence.QuadraticEmergenceAxioms.HomogeneousQ
d_HomogeneousQ_144 ::
  T_QuadraticEmergenceAxioms_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_HomogeneousQ_144 = erased
-- DASHI.Geometry.QuadraticFormEmergence.QuadraticEmergenceAxioms.Additive-On-Orth
d_Additive'45'On'45'Orth_150 ::
  T_QuadraticEmergenceAxioms_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Additive'45'On'45'Orth_150 = erased
-- DASHI.Geometry.QuadraticFormEmergence.QuadraticEmergenceAxioms.PD-splits
d_PD'45'splits_154 ::
  T_QuadraticEmergenceAxioms_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_PD'45'splits_154 = erased
-- DASHI.Geometry.QuadraticFormEmergence.QuadraticFormEmergence
d_QuadraticFormEmergence_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_ProjectionDefect_32 ->
  T_QuadraticEmergenceAxioms_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_QuadraticFormEmergence_170 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_QuadraticFormEmergence_170 v5
du_QuadraticFormEmergence_170 ::
  T_QuadraticEmergenceAxioms_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_QuadraticFormEmergence_170 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.DASHI.Geometry.QQuadraticForm.C_QuadraticForm'46'constructor_1593
         (d_Energy_130 (coe v0)) (d_Scale_132 (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- DASHI.Geometry.QuadraticFormEmergence._.Additive-On-Orth
d_Additive'45'On'45'Orth_182 ::
  T_QuadraticEmergenceAxioms_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Additive'45'On'45'Orth_182 = erased
-- DASHI.Geometry.QuadraticFormEmergence._.Energy
d_Energy_184 :: T_QuadraticEmergenceAxioms_16 -> AgdaAny -> AgdaAny
d_Energy_184 v0 = coe d_Energy_130 (coe v0)
-- DASHI.Geometry.QuadraticFormEmergence._.HomogeneousQ
d_HomogeneousQ_186 ::
  T_QuadraticEmergenceAxioms_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_HomogeneousQ_186 = erased
-- DASHI.Geometry.QuadraticFormEmergence._.PD-splits
d_PD'45'splits_188 ::
  T_QuadraticEmergenceAxioms_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_PD'45'splits_188 = erased
-- DASHI.Geometry.QuadraticFormEmergence._.ParallelogramQ
d_ParallelogramQ_190 ::
  T_QuadraticEmergenceAxioms_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ParallelogramQ_190 = erased
-- DASHI.Geometry.QuadraticFormEmergence._.Scale
d_Scale_192 ::
  T_QuadraticEmergenceAxioms_16 -> AgdaAny -> AgdaAny -> AgdaAny
d_Scale_192 v0 = coe d_Scale_132 (coe v0)

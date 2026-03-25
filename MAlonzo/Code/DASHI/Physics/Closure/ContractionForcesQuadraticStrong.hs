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

module MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefectSplitForcesParallelogram
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance
import qualified MAlonzo.Code.DASHI.Physics.Signature31InstanceShiftZ90Z
import qualified MAlonzo.Code.DASHI.Physics.SignedPerm4
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.UniqueUpToScaleSeam
d_UniqueUpToScaleSeam_12 a0 a1 = ()
data T_UniqueUpToScaleSeam_12
  = C_UniqueUpToScaleSeam'46'constructor_181
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.UniqueUpToScaleSeam.normalizeToQ̂core
d_normalizeToQ'770'core_24 ::
  T_UniqueUpToScaleSeam_12 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalizeToQ'770'core_24 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.mkUniqueUpToScaleSeam
d_mkUniqueUpToScaleSeam_32 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_UniqueUpToScaleSeam_12
d_mkUniqueUpToScaleSeam_32 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.QuadraticUniquenessBridge
d_QuadraticUniquenessBridge_40 a0 a1 = ()
newtype T_QuadraticUniquenessBridge_40
  = C_QuadraticUniquenessBridge'46'constructor_1105 MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.QuadraticUniquenessBridge.referenceQuadratic
d_referenceQuadratic_54 ::
  T_QuadraticUniquenessBridge_40 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
d_referenceQuadratic_54 v0
  = case coe v0 of
      C_QuadraticUniquenessBridge'46'constructor_1105 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.QuadraticUniquenessBridge.invariantMatchesReference
d_invariantMatchesReference_58 ::
  T_QuadraticUniquenessBridge_40 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_invariantMatchesReference_58 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.QuadraticUniquenessBridge.uniqueness
d_uniqueness_60 ::
  T_QuadraticUniquenessBridge_40 -> T_UniqueUpToScaleSeam_12
d_uniqueness_60 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.mkQuadraticUniquenessBridge
d_mkQuadraticUniquenessBridge_70 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_QuadraticUniquenessBridge_40
d_mkQuadraticUniquenessBridge_70 ~v0 v1 ~v2 ~v3
  = du_mkQuadraticUniquenessBridge_70 v1
du_mkQuadraticUniquenessBridge_70 ::
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  T_QuadraticUniquenessBridge_40
du_mkQuadraticUniquenessBridge_70 v0
  = coe C_QuadraticUniquenessBridge'46'constructor_1105 v0
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong
d_ContractionForcesQuadraticStrong_78 = ()
data T_ContractionForcesQuadraticStrong_78
  = C_ContractionForcesQuadraticStrong'46'constructor_2531 Integer
                                                           MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_ProjectionDefect_32
                                                           MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.T_ProjectionDefectParallelogramPackage_14
                                                           MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.T_ProjectionDefectQuadraticWitness_102
                                                           MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
                                                           (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
                                                            MAlonzo.Code.Data.Vec.Base.T_Vec_28)
                                                           MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
                                                           MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
                                                           T_QuadraticUniquenessBridge_40
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong.dimension
d_dimension_102 :: T_ContractionForcesQuadraticStrong_78 -> Integer
d_dimension_102 v0
  = case coe v0 of
      C_ContractionForcesQuadraticStrong'46'constructor_2531 v1 v2 v3 v4 v5 v6 v8 v9 v10
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong.projection
d_projection_104 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_ProjectionDefect_32
d_projection_104 v0
  = case coe v0 of
      C_ContractionForcesQuadraticStrong'46'constructor_2531 v1 v2 v3 v4 v5 v6 v8 v9 v10
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong.projectionParallelogram
d_projectionParallelogram_106 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.T_ProjectionDefectParallelogramPackage_14
d_projectionParallelogram_106 v0
  = case coe v0 of
      C_ContractionForcesQuadraticStrong'46'constructor_2531 v1 v2 v3 v4 v5 v6 v8 v9 v10
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong.projectionQuadraticWitness
d_projectionQuadraticWitness_108 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.T_ProjectionDefectQuadraticWitness_102
d_projectionQuadraticWitness_108 v0
  = case coe v0 of
      C_ContractionForcesQuadraticStrong'46'constructor_2531 v1 v2 v3 v4 v5 v6 v8 v9 v10
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong.derivedQuadratic
d_derivedQuadratic_110 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
d_derivedQuadratic_110 v0
  = case coe v0 of
      C_ContractionForcesQuadraticStrong'46'constructor_2531 v1 v2 v3 v4 v5 v6 v8 v9 v10
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong.dynamicsMap
d_dynamicsMap_112 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_dynamicsMap_112 v0
  = case coe v0 of
      C_ContractionForcesQuadraticStrong'46'constructor_2531 v1 v2 v3 v4 v5 v6 v8 v9 v10
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong.invariantUnderT
d_invariantUnderT_116 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_invariantUnderT_116 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong.nondegenerate
d_nondegenerate_118 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_nondegenerate_118 v0
  = case coe v0 of
      C_ContractionForcesQuadraticStrong'46'constructor_2531 v1 v2 v3 v4 v5 v6 v8 v9 v10
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong.compatibleWithIsotropy
d_compatibleWithIsotropy_120 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_compatibleWithIsotropy_120 v0
  = case coe v0 of
      C_ContractionForcesQuadraticStrong'46'constructor_2531 v1 v2 v3 v4 v5 v6 v8 v9 v10
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.ContractionForcesQuadraticStrong.quadraticUniquenessBridge
d_quadraticUniquenessBridge_122 ::
  T_ContractionForcesQuadraticStrong_78 ->
  T_QuadraticUniquenessBridge_40
d_quadraticUniquenessBridge_122 v0
  = case coe v0 of
      C_ContractionForcesQuadraticStrong'46'constructor_2531 v1 v2 v3 v4 v5 v6 v8 v9 v10
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.invariantQuadraticWitness
d_invariantQuadraticWitness_128 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_invariantQuadraticWitness_128 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.uniqueUpToScaleWitness
d_uniqueUpToScaleWitness_136 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uniqueUpToScaleWitness_136 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.canonicalQuadraticAgreement
d_canonicalQuadraticAgreement_148 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  T_UniqueUpToScaleSeam_12 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_canonicalQuadraticAgreement_148 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.canonicalQuadraticAgreementToQ̂core
d_canonicalQuadraticAgreementToQ'770'core_162 ::
  T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_canonicalQuadraticAgreementToQ'770'core_162 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.buildContractionForcesQuadraticStrong
d_buildContractionForcesQuadraticStrong_178 ::
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   MAlonzo.Code.Data.Vec.Base.T_Vec_28) ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ContractionForcesQuadraticStrong_78
d_buildContractionForcesQuadraticStrong_178 v0 v1 ~v2 ~v3
  = du_buildContractionForcesQuadraticStrong_178 v0 v1
du_buildContractionForcesQuadraticStrong_178 ::
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   MAlonzo.Code.Data.Vec.Base.T_Vec_28) ->
  T_ContractionForcesQuadraticStrong_78
du_buildContractionForcesQuadraticStrong_178 v0 v1
  = coe
      C_ContractionForcesQuadraticStrong'46'constructor_2531 v0
      (MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_PDzero_308
         (coe v0))
      (MAlonzo.Code.DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.d_projectionDefectParallelogramFromSplit_98
         (coe v0))
      (coe
         MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.du_fromProjectionPackageWitness_134
         (coe
            MAlonzo.Code.DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.d_projectionDefectParallelogramFromSplit_98
            (coe v0)))
      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.du_quadraticFromProjectionDefect_86
            (coe
               MAlonzo.Code.DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.d_projectionDefectParallelogramFromSplit_98
               (coe v0))))
      v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         du_mkQuadraticUniquenessBridge_70
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.du_quadraticFromProjectionDefect_86
               (coe
                  MAlonzo.Code.DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.d_projectionDefectParallelogramFromSplit_98
                  (coe v0)))))
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.canonicalIdentityInvariantStrong
d_canonicalIdentityInvariantStrong_198 ::
  Integer -> T_ContractionForcesQuadraticStrong_78
d_canonicalIdentityInvariantStrong_198 v0
  = coe
      du_buildContractionForcesQuadraticStrong_178 (coe v0)
      (coe (\ v1 -> v1))
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.canonicalSignedPerm4InvariantStrong
d_canonicalSignedPerm4InvariantStrong_210 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  T_ContractionForcesQuadraticStrong_78
d_canonicalSignedPerm4InvariantStrong_210 v0
  = coe
      du_buildContractionForcesQuadraticStrong_178 (coe (4 :: Integer))
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31InstanceShiftZ90Z.d_actIso4_114
         (coe v0))
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.nontrivialSignedPerm4
d_nontrivialSignedPerm4_216 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86
d_nontrivialSignedPerm4_216
  = coe
      MAlonzo.Code.DASHI.Physics.SignedPerm4.C_SignedPerm4'46'constructor_4457
      (coe MAlonzo.Code.DASHI.Physics.SignedPerm4.C_p120_14)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe
         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe
            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
            (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
            (coe
               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
               (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))))
-- DASHI.Physics.Closure.ContractionForcesQuadraticStrong.canonicalNontrivialInvariantStrong
d_canonicalNontrivialInvariantStrong_218 ::
  T_ContractionForcesQuadraticStrong_78
d_canonicalNontrivialInvariantStrong_218
  = coe
      d_canonicalSignedPerm4InvariantStrong_210
      (coe d_nontrivialSignedPerm4_216)

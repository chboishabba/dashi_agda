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

module MAlonzo.Code.DASHI.Geometry.ProjectionDefectSplitForcesParallelogram where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticPolarization
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason._IsRelatedTo_
d__IsRelatedTo__8 a0 a1 = ()
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason._∎
d__'8718'_10 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d__'8718'_10
  = let v0
          = MAlonzo.Code.Data.Integer.Properties.d_'8801''45'setoid_2710 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                    (coe v0)) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
               (coe v1))))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.begin_
d_begin__12 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__12 = erased
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.start
d_start_16 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_start_16 = erased
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.step-≈
d_step'45''8776'_18 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8776'_18
  = let v0
          = MAlonzo.Code.Data.Integer.Properties.d_'8801''45'setoid_2710 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v0)))))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.step-≈-⟨
d_step'45''8776''45''10216'_20 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8776''45''10216'_20
  = let v0
          = MAlonzo.Code.Data.Integer.Properties.d_'8801''45'setoid_2710 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.step-≈-⟩
d_step'45''8776''45''10217'_22 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8776''45''10217'_22
  = let v0
          = MAlonzo.Code.Data.Integer.Properties.d_'8801''45'setoid_2710 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v0)))))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.step-≈˘
d_step'45''8776''728'_24 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8776''728'_24
  = let v0
          = MAlonzo.Code.Data.Integer.Properties.d_'8801''45'setoid_2710 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''728'_374
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.step-≡
d_step'45''8801'_26 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801'_26
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.step-≡-∣
d_step'45''8801''45''8739'_28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''8739'_28 ~v0 ~v1 v2
  = du_step'45''8801''45''8739'_28 v2
du_step'45''8801''45''8739'_28 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801''45''8739'_28 v0 = coe v0
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.step-≡-⟨
d_step'45''8801''45''10216'_30 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''10216'_30
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.step-≡-⟩
d_step'45''8801''45''10217'_32 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''10217'_32
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.step-≡˘
d_step'45''8801''728'_34 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''728'_34
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.stop
d_stop_36 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_stop_36
  = let v0
          = MAlonzo.Code.Data.Integer.Properties.d_'8801''45'setoid_2710 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.∼-go
d_'8764''45'go_38 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_'8764''45'go_38
  = let v0
          = MAlonzo.Code.Data.Integer.Properties.d_'8801''45'setoid_2710 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.ℤReason.≡-go
d_'8801''45'go_40 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_'8801''45'go_40 ~v0 ~v1 ~v2 ~v3 v4 = du_'8801''45'go_40 v4
du_'8801''45'go_40 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_'8801''45'go_40 v0 = coe v0
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.projectionDefectSplitForcesParallelogram
d_projectionDefectSplitForcesParallelogram_52 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projectionDefectSplitForcesParallelogram_52 = erased
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.projectionDefectOrthogonalAdditivity
d_projectionDefectOrthogonalAdditivity_62 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projectionDefectOrthogonalAdditivity_62 = erased
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.projectionDefectEnergySplit
d_projectionDefectEnergySplit_82 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projectionDefectEnergySplit_82 = erased
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.quadraticEmergenceFromProjectionDefectSplit
d_quadraticEmergenceFromProjectionDefectSplit_92 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.T_QuadraticEmergenceAxioms_16
d_quadraticEmergenceFromProjectionDefectSplit_92 ~v0
  = du_quadraticEmergenceFromProjectionDefectSplit_92
du_quadraticEmergenceFromProjectionDefectSplit_92 ::
  MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.T_QuadraticEmergenceAxioms_16
du_quadraticEmergenceFromProjectionDefectSplit_92
  = coe
      MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.C_QuadraticEmergenceAxioms'46'constructor_2875
      (coe
         MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du_Q'770'core_186)
      (coe
         MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.du_scaleVec_170)
-- DASHI.Geometry.ProjectionDefectSplitForcesParallelogram.projectionDefectParallelogramFromSplit
d_projectionDefectParallelogramFromSplit_98 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.T_ProjectionDefectParallelogramPackage_14
d_projectionDefectParallelogramFromSplit_98 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.du_fromEmergenceAxioms_64
      (coe
         MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_PDzero_308
         (coe v0))
      (coe du_quadraticEmergenceFromProjectionDefectSplit_92)

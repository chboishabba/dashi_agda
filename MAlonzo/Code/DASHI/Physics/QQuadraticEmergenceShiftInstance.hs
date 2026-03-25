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

module MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticPolarization
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Integer.Tactic.RingSolver
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Reflection
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing
import qualified MAlonzo.Code.Tactic.RingSolver.Core.Expression
import qualified MAlonzo.Code.Tactic.RingSolver.Core.Polynomial.Base
import qualified MAlonzo.Code.Tactic.RingSolver.Core.Polynomial.Parameters
import qualified MAlonzo.Code.Tactic.RingSolver.NonReflective

-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES._IsRelatedTo_
d__IsRelatedTo__8 a0 a1 = ()
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES._∎
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.begin_
d_begin__12 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__12 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.start
d_start_16 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_start_16 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.step-≈
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.step-≈-⟨
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.step-≈-⟩
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.step-≈˘
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.step-≡
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.step-≡-∣
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.step-≡-⟨
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.step-≡-⟩
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.step-≡˘
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.stop
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.∼-go
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ℤReasonQES.≡-go
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
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ._⊜_
d__'8860'__48 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8860'__48 ~v0 = du__'8860'__48
du__'8860'__48 ::
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'8860'__48 = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.solve
d_solve_50 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_solve_50
  = let v0 = MAlonzo.Code.Level.d_0ℓ_22 in
    coe
      (let v1 = MAlonzo.Code.Level.d_0ℓ_22 in
       coe
         (let v2 = MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reflection.du_solve_130
               (let v3
                      = MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.d_isAlmostCommutativeRing_222
                          (coe v2) in
                coe
                  (let v4
                         = MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.d_isCommutativeSemiring_62
                             (coe v3) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                                   (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                                      (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                            (coe v8) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v9))))))))))
               (coe
                  (\ v3 ->
                     coe MAlonzo.Code.Tactic.RingSolver.Core.Expression.C_Ι_24))
               (\ v3 v4 v5 ->
                  coe
                    MAlonzo.Code.Tactic.RingSolver.Core.Expression.du_'10214'_'10215'_90
                    (coe
                       MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.du_rawRing_346
                       (coe v2))
                    (coe (\ v6 -> v6)) v4 v5)
               (coe
                  MAlonzo.Code.Tactic.RingSolver.NonReflective.d_'10214'_'8659''10215'_374
                  (coe v0) (coe v1) (coe v2))
               (coe
                  MAlonzo.Code.Tactic.RingSolver.NonReflective.d_correct_402 (coe v0)
                  (coe v1) (coe v2)))))
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops._⊜_
d__'8860'__54 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8860'__54 v0
  = coe MAlonzo.Code.Relation.Binary.Reflection.du__'8860'__158
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops.close
d_close_56 :: () -> Integer -> AgdaAny -> AgdaAny
d_close_56 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reflection.du_close_120
      (coe
         (\ v3 ->
            coe MAlonzo.Code.Tactic.RingSolver.Core.Expression.C_Ι_24))
      v1 v2
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops.correct
d_correct_58 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_correct_58 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops.homo
d_homo_60 ::
  MAlonzo.Code.Tactic.RingSolver.Core.Polynomial.Parameters.T_Homomorphism_68
d_homo_60
  = coe
      MAlonzo.Code.Tactic.RingSolver.NonReflective.du_homo_188
      (coe MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8)
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops.norm
d_norm_62 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Polynomial.Base.T_Poly_176
d_norm_62
  = coe
      MAlonzo.Code.Tactic.RingSolver.NonReflective.d_norm_352
      (coe MAlonzo.Code.Level.d_0ℓ_22) (coe MAlonzo.Code.Level.d_0ℓ_22)
      (coe MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8)
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops.prove
d_prove_64 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prove_64 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops.solve
d_solve_66 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_solve_66
  = let v0 = MAlonzo.Code.Level.d_0ℓ_22 in
    coe
      (let v1 = MAlonzo.Code.Level.d_0ℓ_22 in
       coe
         (let v2 = MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reflection.du_solve_130
               (let v3
                      = MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.d_isAlmostCommutativeRing_222
                          (coe v2) in
                coe
                  (let v4
                         = MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.d_isCommutativeSemiring_62
                             (coe v3) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                                   (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                                      (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                            (coe v8) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v9))))))))))
               (coe
                  (\ v3 ->
                     coe MAlonzo.Code.Tactic.RingSolver.Core.Expression.C_Ι_24))
               (\ v3 v4 v5 ->
                  coe
                    MAlonzo.Code.Tactic.RingSolver.Core.Expression.du_'10214'_'10215'_90
                    (coe
                       MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.du_rawRing_346
                       (coe v2))
                    (coe (\ v6 -> v6)) v4 v5)
               (coe
                  MAlonzo.Code.Tactic.RingSolver.NonReflective.d_'10214'_'8659''10215'_374
                  (coe v0) (coe v1) (coe v2))
               (coe
                  MAlonzo.Code.Tactic.RingSolver.NonReflective.d_correct_402 (coe v0)
                  (coe v1) (coe v2)))))
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops.solve₁
d_solve'8321'_68 :: Integer -> AgdaAny -> AgdaAny
d_solve'8321'_68
  = let v0 = MAlonzo.Code.Level.d_0ℓ_22 in
    coe
      (let v1 = MAlonzo.Code.Level.d_0ℓ_22 in
       coe
         (let v2 = MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reflection.du_solve'8321'_146
               (let v3
                      = MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.d_isAlmostCommutativeRing_222
                          (coe v2) in
                coe
                  (let v4
                         = MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.d_isCommutativeSemiring_62
                             (coe v3) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                                   (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                                      (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                            (coe v8) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v9))))))))))
               (coe
                  (\ v3 ->
                     coe MAlonzo.Code.Tactic.RingSolver.Core.Expression.C_Ι_24))
               (\ v3 v4 v5 ->
                  coe
                    MAlonzo.Code.Tactic.RingSolver.Core.Expression.du_'10214'_'10215'_90
                    (coe
                       MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.du_rawRing_346
                       (coe v2))
                    (coe (\ v6 -> v6)) v4 v5)
               (coe
                  MAlonzo.Code.Tactic.RingSolver.NonReflective.d_'10214'_'8659''10215'_374
                  (coe v0) (coe v1) (coe v2))
               (coe
                  MAlonzo.Code.Tactic.RingSolver.NonReflective.d_correct_402 (coe v0)
                  (coe v1) (coe v2)))))
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops.zero-homo
d_zero'45'homo_70 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'45'homo_70 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops.⟦_⇓⟧
d_'10214'_'8659''10215'_72 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_'10214'_'8659''10215'_72
  = coe
      MAlonzo.Code.Tactic.RingSolver.NonReflective.d_'10214'_'8659''10215'_374
      (coe MAlonzo.Code.Level.d_0ℓ_22) (coe MAlonzo.Code.Level.d_0ℓ_22)
      (coe MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8)
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Ops.⟦_⟧
d_'10214'_'10215'_74 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_'10214'_'10215'_74
  = let v0 = MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8 in
    coe
      (\ v1 v2 v3 ->
         coe
           MAlonzo.Code.Tactic.RingSolver.Core.Expression.du_'10214'_'10215'_90
           (coe
              MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.du_rawRing_346
              (coe v0))
           (coe (\ v4 -> v4)) v2 v3)
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Expression.Expr
d_Expr_86 a0 a1 a2 = ()
-- DASHI.Physics.QuadraticEmergenceShiftInstance.RingQ.Eval.⟦_⟧
d_'10214'_'10215'_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'10214'_'10215'_96 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Tactic.RingSolver.Core.Expression.du_'10214'_'10215'_90
      v2 v5 v7 v8
-- DASHI.Physics.QuadraticEmergenceShiftInstance.negVec
d_negVec_112 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_negVec_112 ~v0 = du_negVec_112
du_negVec_112 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_negVec_112
  = coe
      MAlonzo.Code.Data.Vec.Base.du_map_178
      (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252)
-- DASHI.Physics.QuadraticEmergenceShiftInstance.addᵥ-zeroʳ
d_add'7525''45'zero'691'_120 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_add'7525''45'zero'691'_120 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.negVec-zero'
d_negVec'45'zero''_144 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negVec'45'zero''_144 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.negVec-zero
d_negVec'45'zero_150 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negVec'45'zero_150 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.ScalarFieldℤ
d_ScalarFieldℤ_154 ::
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8
d_ScalarFieldℤ_154
  = coe
      MAlonzo.Code.DASHI.Geometry.QQuadraticForm.C_ScalarField'46'constructor_77
      MAlonzo.Code.Data.Integer.Base.d__'43'__276
      MAlonzo.Code.Data.Integer.Base.d__'42'__308 (0 :: Integer)
      (1 :: Integer) MAlonzo.Code.Data.Integer.Base.d_'45'__252
-- DASHI.Physics.QuadraticEmergenceShiftInstance.Q̂core-zeroVec
d_Q'770'core'45'zeroVec_158 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Q'770'core'45'zeroVec_158 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.sq
d_sq_164 :: Integer -> Integer
d_sq_164 v0
  = coe MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v0)
-- DASHI.Physics.QuadraticEmergenceShiftInstance.scaleVec
d_scaleVec_170 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_scaleVec_170 ~v0 v1 = du_scaleVec_170 v1
du_scaleVec_170 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_scaleVec_170 v0
  = coe
      MAlonzo.Code.Data.Vec.Base.du_map_178
      (coe MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0))
-- DASHI.Physics.QuadraticEmergenceShiftInstance.swap-sum
d_swap'45'sum_184 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_swap'45'sum_184 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.parallelogramℤ
d_parallelogramℤ_206 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parallelogramℤ_206 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.reassoc
d_reassoc_224 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reassoc_224 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.parallelogramQ̂core
d_parallelogramQ'770'core_248 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parallelogramQ'770'core_248 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.sq-scaleℤ
d_sq'45'scaleℤ_268 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sq'45'scaleℤ_268 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.homQ̂core
d_homQ'770'core_284 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_homQ'770'core_284 = erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.AdditiveVecℤ
d_AdditiveVecℤ_302 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8
d_AdditiveVecℤ_302 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ProjectionDefect.C_Additive'46'constructor_39
      (coe
         MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du__'43''7525'__118)
      (MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.d_zeroVecℤ_148
         (coe v0))
      (coe du_negVec_112)
-- DASHI.Physics.QuadraticEmergenceShiftInstance.PDzero
d_PDzero_308 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_ProjectionDefect_32
d_PDzero_308 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ProjectionDefect.C_ProjectionDefect'46'constructor_761
      (\ v1 ->
         MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.d_zeroVecℤ_148
           (coe v0))
      (\ v1 -> v1) erased
-- DASHI.Physics.QuadraticEmergenceShiftInstance.QuadraticEmergenceShiftAxioms
d_QuadraticEmergenceShiftAxioms_332 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.T_QuadraticEmergenceAxioms_16
d_QuadraticEmergenceShiftAxioms_332 ~v0
  = du_QuadraticEmergenceShiftAxioms_332
du_QuadraticEmergenceShiftAxioms_332 ::
  MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.T_QuadraticEmergenceAxioms_16
du_QuadraticEmergenceShiftAxioms_332
  = coe
      MAlonzo.Code.DASHI.Geometry.QQuadraticFormEmergence.C_QuadraticEmergenceAxioms'46'constructor_2875
      (coe
         MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du_Q'770'core_186)
      (coe du_scaleVec_170)
-- DASHI.Physics.QuadraticEmergenceShiftInstance.projectionParallelogramShift
d_projectionParallelogramShift_356 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.T_ProjectionDefectParallelogramPackage_14
d_projectionParallelogramShift_356 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.du_fromEmergenceAxioms_64
      (coe d_PDzero_308 (coe v0))
      (coe du_QuadraticEmergenceShiftAxioms_332)
-- DASHI.Physics.QuadraticEmergenceShiftInstance.quadraticShiftΣ
d_quadraticShiftΣ_364 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_quadraticShiftΣ_364 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.du_quadraticFromProjectionDefect_86
      (coe d_projectionParallelogramShift_356 (coe v0))
-- DASHI.Physics.QuadraticEmergenceShiftInstance.quadraticShift
d_quadraticShift_370 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
d_quadraticShift_370 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_quadraticShiftΣ_364 (coe v0))

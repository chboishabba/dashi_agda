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

module MAlonzo.Code.DASHI.Physics.QQuadraticPolarization where

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
import qualified MAlonzo.Code.DASHI.Algebra.Trit
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

-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning._IsRelatedTo_
d__IsRelatedTo__8 a0 a1 = ()
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning._∎
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.begin_
d_begin__12 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__12 = erased
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.start
d_start_16 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_start_16 = erased
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.step-≈
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.step-≈-⟨
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.step-≈-⟩
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.step-≈˘
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.step-≡
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.step-≡-∣
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.step-≡-⟨
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.step-≡-⟩
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.step-≡˘
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.stop
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.∼-go
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
-- DASHI.Physics.QuadraticPolarization.ℤ-Reasoning.≡-go
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
-- DASHI.Physics.QuadraticPolarization.Ring._⊜_
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
-- DASHI.Physics.QuadraticPolarization.Ring.solve
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
-- DASHI.Physics.QuadraticPolarization.Ring.Ops._⊜_
d__'8860'__54 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8860'__54 v0
  = coe MAlonzo.Code.Relation.Binary.Reflection.du__'8860'__158
-- DASHI.Physics.QuadraticPolarization.Ring.Ops.close
d_close_56 :: () -> Integer -> AgdaAny -> AgdaAny
d_close_56 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reflection.du_close_120
      (coe
         (\ v3 ->
            coe MAlonzo.Code.Tactic.RingSolver.Core.Expression.C_Ι_24))
      v1 v2
-- DASHI.Physics.QuadraticPolarization.Ring.Ops.correct
d_correct_58 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_correct_58 = erased
-- DASHI.Physics.QuadraticPolarization.Ring.Ops.homo
d_homo_60 ::
  MAlonzo.Code.Tactic.RingSolver.Core.Polynomial.Parameters.T_Homomorphism_68
d_homo_60
  = coe
      MAlonzo.Code.Tactic.RingSolver.NonReflective.du_homo_188
      (coe MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8)
-- DASHI.Physics.QuadraticPolarization.Ring.Ops.norm
d_norm_62 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Polynomial.Base.T_Poly_176
d_norm_62
  = coe
      MAlonzo.Code.Tactic.RingSolver.NonReflective.d_norm_352
      (coe MAlonzo.Code.Level.d_0ℓ_22) (coe MAlonzo.Code.Level.d_0ℓ_22)
      (coe MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8)
-- DASHI.Physics.QuadraticPolarization.Ring.Ops.prove
d_prove_64 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prove_64 = erased
-- DASHI.Physics.QuadraticPolarization.Ring.Ops.solve
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
-- DASHI.Physics.QuadraticPolarization.Ring.Ops.solve₁
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
-- DASHI.Physics.QuadraticPolarization.Ring.Ops.zero-homo
d_zero'45'homo_70 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'45'homo_70 = erased
-- DASHI.Physics.QuadraticPolarization.Ring.Ops.⟦_⇓⟧
d_'10214'_'8659''10215'_72 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_'10214'_'8659''10215'_72
  = coe
      MAlonzo.Code.Tactic.RingSolver.NonReflective.d_'10214'_'8659''10215'_374
      (coe MAlonzo.Code.Level.d_0ℓ_22) (coe MAlonzo.Code.Level.d_0ℓ_22)
      (coe MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8)
-- DASHI.Physics.QuadraticPolarization.Ring.Ops.⟦_⟧
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
-- DASHI.Physics.QuadraticPolarization.Ring.Expression.Expr
d_Expr_86 a0 a1 a2 = ()
-- DASHI.Physics.QuadraticPolarization.Ring.Eval.⟦_⟧
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
-- DASHI.Physics.QuadraticPolarization.intOfTrit
d_intOfTrit_110 ::
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 -> Integer
d_intOfTrit_110 v0
  = case coe v0 of
      MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8 -> coe (-1 :: Integer)
      MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10 -> coe (0 :: Integer)
      MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.QuadraticPolarization.vecℤ
d_vecℤ_114 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_vecℤ_114 ~v0 = du_vecℤ_114
du_vecℤ_114 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_vecℤ_114
  = coe MAlonzo.Code.Data.Vec.Base.du_map_178 (coe d_intOfTrit_110)
-- DASHI.Physics.QuadraticPolarization._+ᵥ_
d__'43''7525'__118 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d__'43''7525'__118 ~v0 = du__'43''7525'__118
du__'43''7525'__118 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du__'43''7525'__118
  = coe
      MAlonzo.Code.Data.Vec.Base.du_zipWith_242
      (coe MAlonzo.Code.Data.Integer.Base.d__'43'__276)
-- DASHI.Physics.QuadraticPolarization.dotℤ
d_dotℤ_122 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_dotℤ_122 ~v0 v1 v2 = du_dotℤ_122 v1 v2
du_dotℤ_122 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_dotℤ_122 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe seq (coe v1) (coe (0 :: Integer))
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.d__'43'__276
                    (coe MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v3) (coe v6))
                    (coe du_dotℤ_122 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.QuadraticPolarization.sumℤ
d_sumℤ_134 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_sumℤ_134 ~v0 v1 = du_sumℤ_134 v1
du_sumℤ_134 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_sumℤ_134 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe (0 :: Integer)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v2)
             (coe du_sumℤ_134 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.QuadraticPolarization.replicateTrit0
d_replicateTrit0_142 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_replicateTrit0_142 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                (coe MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10)
                (d_replicateTrit0_142 (coe v1)))
-- DASHI.Physics.QuadraticPolarization.zeroVecℤ
d_zeroVecℤ_148 :: Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_zeroVecℤ_148 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 (0 :: Integer)
                (d_zeroVecℤ_148 (coe v1)))
-- DASHI.Physics.QuadraticPolarization.vecℤ-replicateTrit0
d_vecℤ'45'replicateTrit0_154 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vecℤ'45'replicateTrit0_154 = erased
-- DASHI.Physics.QuadraticPolarization.zeroVecℤ+ᵥ
d_zeroVecℤ'43''7525'_164 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zeroVecℤ'43''7525'_164 = erased
-- DASHI.Physics.QuadraticPolarization.Qcoreℤ
d_Qcoreℤ_174 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_Qcoreℤ_174 ~v0 v1 = du_Qcoreℤ_174 v1
du_Qcoreℤ_174 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_Qcoreℤ_174 v0
  = coe
      du_sumℤ_134
      (coe
         MAlonzo.Code.Data.Vec.Base.du_map_178
         (coe
            (\ v1 ->
               MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v1) (coe v1)))
         (coe du_vecℤ_114 v0))
-- DASHI.Physics.QuadraticPolarization.Q̂core
d_Q'770'core_186 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_Q'770'core_186 ~v0 v1 = du_Q'770'core_186 v1
du_Q'770'core_186 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_Q'770'core_186 v0
  = coe
      du_sumℤ_134
      (coe
         MAlonzo.Code.Data.Vec.Base.du_map_178
         (coe
            (\ v1 ->
               MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v1) (coe v1)))
         (coe v0))
-- DASHI.Physics.QuadraticPolarization.B₂ℤ
d_B'8322'ℤ_196 ::
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_B'8322'ℤ_196 ~v0 v1 v2 v3 = du_B'8322'ℤ_196 v1 v2 v3
du_B'8322'ℤ_196 ::
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_B'8322'ℤ_196 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'45'__294
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'45'__294
         (coe
            v0
            (coe
               du__'43''7525'__118 (coe du_vecℤ_114 v1) (coe du_vecℤ_114 v2)))
         (coe v0 (coe du_vecℤ_114 v1)))
      (coe v0 (coe du_vecℤ_114 v2))
-- DASHI.Physics.QuadraticPolarization.b2-trit
d_b2'45'trit_208 ::
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b2'45'trit_208 = erased
-- DASHI.Physics.QuadraticPolarization.split-B₂
d_split'45'B'8322'_222 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_split'45'B'8322'_222 = erased
-- DASHI.Physics.QuadraticPolarization.Q̂core-zero
d_Q'770'core'45'zero_250 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Q'770'core'45'zero_250 = erased
-- DASHI.Physics.QuadraticPolarization.B₂ℤ-zeroL
d_B'8322'ℤ'45'zeroL_260 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_B'8322'ℤ'45'zeroL_260 = erased
-- DASHI.Physics.QuadraticPolarization.B₂ℤ-Q̂core-dot2
d_B'8322'ℤ'45'Q'770'core'45'dot2_282 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_B'8322'ℤ'45'Q'770'core'45'dot2_282 = erased

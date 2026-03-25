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

module MAlonzo.Code.DASHI.Physics.QQuadraticPolarizationCoreInstance where

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
import qualified MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticPolarization
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Tactic.RingSolver
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.Reflection
import qualified MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing
import qualified MAlonzo.Code.Tactic.RingSolver.Core.Expression
import qualified MAlonzo.Code.Tactic.RingSolver.Core.Polynomial.Base
import qualified MAlonzo.Code.Tactic.RingSolver.Core.Polynomial.Parameters
import qualified MAlonzo.Code.Tactic.RingSolver.NonReflective

-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ._⊜_
d__'8860'__8 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8860'__8 ~v0 = du__'8860'__8
du__'8860'__8 ::
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'8860'__8 = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.solve
d_solve_10 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_solve_10
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
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops._⊜_
d__'8860'__14 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8860'__14 v0
  = coe MAlonzo.Code.Relation.Binary.Reflection.du__'8860'__158
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops.close
d_close_16 :: () -> Integer -> AgdaAny -> AgdaAny
d_close_16 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reflection.du_close_120
      (coe
         (\ v3 ->
            coe MAlonzo.Code.Tactic.RingSolver.Core.Expression.C_Ι_24))
      v1 v2
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops.correct
d_correct_18 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_correct_18 = erased
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops.homo
d_homo_20 ::
  MAlonzo.Code.Tactic.RingSolver.Core.Polynomial.Parameters.T_Homomorphism_68
d_homo_20
  = coe
      MAlonzo.Code.Tactic.RingSolver.NonReflective.du_homo_188
      (coe MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8)
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops.norm
d_norm_22 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Polynomial.Base.T_Poly_176
d_norm_22
  = coe
      MAlonzo.Code.Tactic.RingSolver.NonReflective.d_norm_352
      (coe MAlonzo.Code.Level.d_0ℓ_22) (coe MAlonzo.Code.Level.d_0ℓ_22)
      (coe MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8)
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops.prove
d_prove_24 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prove_24 = erased
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops.solve
d_solve_26 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_solve_26
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
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops.solve₁
d_solve'8321'_28 :: Integer -> AgdaAny -> AgdaAny
d_solve'8321'_28
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
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops.zero-homo
d_zero'45'homo_30 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'45'homo_30 = erased
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops.⟦_⇓⟧
d_'10214'_'8659''10215'_32 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_'10214'_'8659''10215'_32
  = coe
      MAlonzo.Code.Tactic.RingSolver.NonReflective.d_'10214'_'8659''10215'_374
      (coe MAlonzo.Code.Level.d_0ℓ_22) (coe MAlonzo.Code.Level.d_0ℓ_22)
      (coe MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8)
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Ops.⟦_⟧
d_'10214'_'10215'_34 ::
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_'10214'_'10215'_34
  = let v0 = MAlonzo.Code.Data.Integer.Tactic.RingSolver.d_ring_8 in
    coe
      (\ v1 v2 v3 ->
         coe
           MAlonzo.Code.Tactic.RingSolver.Core.Expression.du_'10214'_'10215'_90
           (coe
              MAlonzo.Code.Tactic.RingSolver.Core.AlmostCommutativeRing.du_rawRing_346
              (coe v0))
           (coe (\ v4 -> v4)) v2 v3)
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Expression.Expr
d_Expr_46 a0 a1 a2 = ()
-- DASHI.Physics.QuadraticPolarizationCoreInstance.RingZ.Eval.⟦_⟧
d_'10214'_'10215'_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Tactic.RingSolver.Core.Expression.T_Expr_14 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'10214'_'10215'_56 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Tactic.RingSolver.Core.Expression.du_'10214'_'10215'_90
      v2 v5 v7 v8
-- DASHI.Physics.QuadraticPolarizationCoreInstance.ScalarFieldℤ
d_ScalarFieldℤ_70 ::
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8
d_ScalarFieldℤ_70
  = coe
      MAlonzo.Code.DASHI.Geometry.QQuadraticForm.C_ScalarField'46'constructor_77
      MAlonzo.Code.Data.Integer.Base.d__'43'__276
      MAlonzo.Code.Data.Integer.Base.d__'42'__308 (0 :: Integer)
      (1 :: Integer) MAlonzo.Code.Data.Integer.Base.d_'45'__252
-- DASHI.Physics.QuadraticPolarizationCoreInstance.square-sum
d_square'45'sum_76 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_square'45'sum_76 = erased
-- DASHI.Physics.QuadraticPolarizationCoreInstance.rearrange
d_rearrange_98 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rearrange_98 = erased
-- DASHI.Physics.QuadraticPolarizationCoreInstance.polarization-core
d_polarization'45'core_130 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_polarization'45'core_130 = erased
-- DASHI.Physics.QuadraticPolarizationCoreInstance.polarizationCore
d_polarizationCore_150 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14
d_polarizationCore_150 ~v0 = du_polarizationCore_150
du_polarizationCore_150 ::
  MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14
du_polarizationCore_150
  = coe
      MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.C_Polarization'46'constructor_1095
      (coe
         MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du_Q'770'core_186)
      (coe MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du_dotℤ_122)
      (2 :: Integer)

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

module MAlonzo.Code.DASHI.Metric.AgreementUltrametric where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.DASHI.Algebra.Trit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Ultrametric

-- DASHI.Metric.AgreementUltrametric.agreeDepth
d_agreeDepth_8 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_agreeDepth_8 v0 v1 v2
  = let v3 = 0 :: Integer in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
           -> case coe v2 of
                MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe (0 :: Integer)
                _ -> coe v3
         MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5 v6
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
                    let v7 = subInt (coe v0) (coe (1 :: Integer)) in
                    coe
                      (case coe v5 of
                         MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                           -> case coe v2 of
                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                                  -> case coe v9 of
                                       MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                         -> coe
                                              addInt (coe (1 :: Integer))
                                              (coe d_agreeDepth_8 (coe v7) (coe v6) (coe v10))
                                       _ -> coe v3
                                _ -> coe v3
                         MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                           -> case coe v2 of
                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                                  -> case coe v9 of
                                       MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                         -> coe
                                              addInt (coe (1 :: Integer))
                                              (coe d_agreeDepth_8 (coe v7) (coe v6) (coe v10))
                                       _ -> coe v3
                                _ -> coe v3
                         MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                           -> case coe v2 of
                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                                  -> case coe v9 of
                                       MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                         -> coe
                                              addInt (coe (1 :: Integer))
                                              (coe d_agreeDepth_8 (coe v7) (coe v6) (coe v10))
                                       _ -> coe v3
                                _ -> coe v3
                         _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Metric.AgreementUltrametric.dNat
d_dNat_24 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_dNat_24 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0
      (d_agreeDepth_8 (coe v0) (coe v1) (coe v2))
-- DASHI.Metric.AgreementUltrametric.agreeDepth-self
d_agreeDepth'45'self_36 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agreeDepth'45'self_36 = erased
-- DASHI.Metric.AgreementUltrametric.agreeDepth-sym
d_agreeDepth'45'sym_62 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agreeDepth'45'sym_62 = erased
-- DASHI.Metric.AgreementUltrametric.agreeDepth-inv
d_agreeDepth'45'inv_118 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agreeDepth'45'inv_118 = erased
-- DASHI.Metric.AgreementUltrametric.dNat-inv
d_dNat'45'inv_174 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dNat'45'inv_174 = erased
-- DASHI.Metric.AgreementUltrametric.agreeDepth≤n
d_agreeDepth'8804'n_190 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_agreeDepth'8804'n_190 ~v0 v1 v2 = du_agreeDepth'8804'n_190 v1 v2
du_agreeDepth'8804'n_190 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_agreeDepth'8804'n_190 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe seq (coe v1) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> case coe v3 of
             MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
               -> case coe v1 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                             -> coe
                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                  (coe du_agreeDepth'8804'n_190 (coe v4) (coe v7))
                           MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                             -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                           MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                             -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
               -> case coe v1 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                             -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                           MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                             -> coe
                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                  (coe du_agreeDepth'8804'n_190 (coe v4) (coe v7))
                           MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                             -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
               -> case coe v1 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                             -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                           MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                             -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                           MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                             -> coe
                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                  (coe du_agreeDepth'8804'n_190 (coe v4) (coe v7))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Metric.AgreementUltrametric.agreeDepth-eq→eq
d_agreeDepth'45'eq'8594'eq_234 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agreeDepth'45'eq'8594'eq_234 = erased
-- DASHI.Metric.AgreementUltrametric.dNat-zero→eq
d_dNat'45'zero'8594'eq_290 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dNat'45'zero'8594'eq_290 = erased
-- DASHI.Metric.AgreementUltrametric.dNat-nonzero
d_dNat'45'nonzero_312 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_dNat'45'nonzero_312 = erased
-- DASHI.Metric.AgreementUltrametric.dNat-positive
d_dNat'45'positive_324 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dNat'45'positive_324 v0 v1 v2 ~v3
  = du_dNat'45'positive_324 v0 v1 v2
du_dNat'45'positive_324 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_dNat'45'positive_324 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_n'8802'0'8658'n'62'0_3090
      (coe d_dNat_24 (coe v0) (coe v1) (coe v2))
-- DASHI.Metric.AgreementUltrametric.agreeDepth-triangle
d_agreeDepth'45'triangle_336 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_agreeDepth'45'triangle_336 ~v0 v1 v2 v3
  = du_agreeDepth'45'triangle_336 v1 v2 v3
du_agreeDepth'45'triangle_336 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_agreeDepth'45'triangle_336 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe
             seq (coe v1)
             (coe seq (coe v2) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
                      -> case coe v4 of
                           MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                             -> case coe v7 of
                                  MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                    -> case coe v10 of
                                         MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                           -> coe
                                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                (coe
                                                   du_agreeDepth'45'triangle_336 (coe v5) (coe v8)
                                                   (coe v11))
                                         MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                           -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                         MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                           -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                    -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                  MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                    -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                             -> case coe v7 of
                                  MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                    -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                  MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                    -> case coe v10 of
                                         MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                           -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                         MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                           -> coe
                                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                (coe
                                                   du_agreeDepth'45'triangle_336 (coe v5) (coe v8)
                                                   (coe v11))
                                         MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                           -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                    -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                             -> case coe v7 of
                                  MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                    -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                  MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                    -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                  MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                    -> case coe v10 of
                                         MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                           -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                         MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                           -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                         MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                           -> coe
                                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                (coe
                                                   du_agreeDepth'45'triangle_336 (coe v5) (coe v8)
                                                   (coe v11))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Metric.AgreementUltrametric.ultraNat
d_ultraNat_542 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ultraNat_542 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Data.Nat.Properties.d_'8804''45'total_2790
              (coe d_agreeDepth_8 (coe v0) (coe v1) (coe v2))
              (coe d_agreeDepth_8 (coe v0) (coe v2) (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
           -> coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono_5076 (coe v0)
                   (coe v0) (coe d_agreeDepth_8 (coe v0) (coe v1) (coe v3))
                   (coe d_agreeDepth_8 (coe v0) (coe v1) (coe v2))
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776 (coe v0))
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
                         (coe d_agreeDepth_8 (coe v0) (coe v1) (coe v2)))
                      (coe du_agreeDepth'45'triangle_336 (coe v1) (coe v2) (coe v3))))
                (let v6
                       = MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2822 in
                 coe
                   (let v7
                          = MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4440 in
                    coe
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
                         (coe
                            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                            (coe v6))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                            (coe v7))
                         (coe d_dNat_24 (coe v0) (coe v1) (coe v2))
                         (coe d_dNat_24 (coe v0) (coe v2) (coe v3)))))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
           -> coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono_5076 (coe v0)
                   (coe v0) (coe d_agreeDepth_8 (coe v0) (coe v1) (coe v3))
                   (coe d_agreeDepth_8 (coe v0) (coe v2) (coe v3))
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776 (coe v0))
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
                         (coe d_agreeDepth_8 (coe v0) (coe v2) (coe v3)))
                      (coe du_agreeDepth'45'triangle_336 (coe v1) (coe v2) (coe v3))))
                (let v6
                       = MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2822 in
                 coe
                   (let v7
                          = MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4440 in
                    coe
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
                         (coe
                            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                            (coe v6))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                            (coe v7))
                         (coe d_dNat_24 (coe v0) (coe v1) (coe v2))
                         (coe d_dNat_24 (coe v0) (coe v2) (coe v3)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Metric.AgreementUltrametric.ultrametricVec
d_ultrametricVec_598 ::
  Integer -> MAlonzo.Code.Ultrametric.T_Ultrametric_6
d_ultrametricVec_598 v0
  = coe
      MAlonzo.Code.Ultrametric.C_Ultrametric'46'constructor_391
      (d_dNat_24 (coe v0)) (d_ultraNat_542 (coe v0))

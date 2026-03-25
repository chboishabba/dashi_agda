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

module MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Algebra.Trit
import qualified MAlonzo.Code.DASHI.Metric.AgreementUltrametric
import qualified MAlonzo.Code.DASHI.Physics.TailCollapseProof
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Ultrametric

-- DASHI.Metric.FineAgreementUltrametric.cong₂
d_cong'8322'_22 ::
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8322'_22 = erased
-- DASHI.Metric.FineAgreementUltrametric.agreeDepthFine
d_agreeDepthFine_28 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_agreeDepthFine_28 v0 v1 v2
  = coe
      MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
      (coe v0) (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v1)
      (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
-- DASHI.Metric.FineAgreementUltrametric.dNatFine
d_dNatFine_36 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_dNatFine_36 v0 v1 v2
  = coe
      MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_dNat_24 (coe v0)
      (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v1)
      (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-inv
d_dNatFine'45'inv_48 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dNatFine'45'inv_48 = erased
-- DASHI.Metric.FineAgreementUltrametric.reverse≢
d_reverse'8802'_72 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_reverse'8802'_72 = erased
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-zero→eq
d_dNatFine'45'zero'8594'eq_84 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dNatFine'45'zero'8594'eq_84 = erased
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-positive
d_dNatFine'45'positive_98 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dNatFine'45'positive_98 v0 v1 v2 ~v3
  = du_dNatFine'45'positive_98 v0 v1 v2
du_dNatFine'45'positive_98 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_dNatFine'45'positive_98 v0 v1 v2
  = coe
      MAlonzo.Code.DASHI.Metric.AgreementUltrametric.du_dNat'45'positive_324
      (coe v0) (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v1)
      (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
-- DASHI.Metric.FineAgreementUltrametric.agreeDepth-map≤
d_agreeDepth'45'map'8804'_110 ::
  Integer ->
  (MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
   MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_agreeDepth'45'map'8804'_110 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe
             seq (coe v2)
             (coe seq (coe v3) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                         -> case coe v3 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                                -> case coe v9 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> let v11 = coe v1 v9 in
                                          coe
                                            (coe
                                               seq (coe v11)
                                               (coe
                                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                  (d_agreeDepth'45'map'8804'_110
                                                     (coe v4) (coe v1) (coe v7) (coe v10))))
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                         -> case coe v3 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                                -> case coe v9 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> let v11 = coe v1 v9 in
                                          coe
                                            (coe
                                               seq (coe v11)
                                               (coe
                                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                  (d_agreeDepth'45'map'8804'_110
                                                     (coe v4) (coe v1) (coe v7) (coe v10))))
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                         -> case coe v3 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                                -> case coe v9 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> let v11 = coe v1 v9 in
                                          coe
                                            (coe
                                               seq (coe v11)
                                               (coe
                                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                  (d_agreeDepth'45'map'8804'_110
                                                     (coe v4) (coe v1) (coe v7) (coe v10))))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-map≤
d_dNatFine'45'map'8804'_278 ::
  Integer ->
  (MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
   MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dNatFine'45'map'8804'_278 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
         (coe
            d_dNatFine_36 (coe v0)
            (coe MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v1) (coe v2))
            (coe MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v1) (coe v3))))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''8804'_5098
         (coe
            MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
            (coe v0) (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3))
         (coe
            MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
            (coe v0)
            (coe
               MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v1)
               (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2))
            (coe
               MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v1)
               (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))
         (coe v0)
         (coe
            d_agreeDepth'45'map'8804'_110 (coe v0) (coe v1)
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))
-- DASHI.Metric.FineAgreementUltrametric.agreeDepth-++≥
d_agreeDepth'45''43''43''8805'_304 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_agreeDepth'45''43''43''8805'_304 v0 ~v1 v2 v3 ~v4
  = du_agreeDepth'45''43''43''8805'_304 v0 v2 v3
du_agreeDepth'45''43''43''8805'_304 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_agreeDepth'45''43''43''8805'_304 v0 v1 v2
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe seq (coe v2) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                         -> case coe v2 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                            (coe
                                               du_agreeDepth'45''43''43''8805'_304 (coe v3) (coe v6)
                                               (coe v9))
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                         -> case coe v2 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                            (coe
                                               du_agreeDepth'45''43''43''8805'_304 (coe v3) (coe v6)
                                               (coe v9))
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                         -> case coe v2 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                            (coe
                                               du_agreeDepth'45''43''43''8805'_304 (coe v3) (coe v6)
                                               (coe v9))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Metric.FineAgreementUltrametric.reverse-∷ʳ
d_reverse'45''8759''691'_406 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45''8759''691'_406 = erased
-- DASHI.Metric.FineAgreementUltrametric.agreeDepth-cast
d_agreeDepth'45'cast_438 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agreeDepth'45'cast_438 = erased
-- DASHI.Metric.FineAgreementUltrametric.dNat-cast
d_dNat'45'cast_462 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dNat'45'cast_462 = erased
-- DASHI.Metric.FineAgreementUltrametric.agreeDepth-++-mono
d_agreeDepth'45''43''43''45'mono_492 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_agreeDepth'45''43''43''45'mono_492 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v0 of
      0 -> coe
             seq (coe v2)
             (coe
                seq (coe v3)
                (coe
                   seq (coe v4)
                   (coe
                      seq (coe v5)
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                         (coe
                            MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
                            (coe v1)
                            (coe
                               MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                               (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32) (coe v6))
                            (coe
                               MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                               (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32) (coe v7)))))))
      _ -> let v9 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
                  -> case coe v11 of
                       MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                         -> case coe v3 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> case coe v4 of
                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v17 v18
                                              -> coe
                                                   seq (coe v17)
                                                   (case coe v5 of
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v20 v21
                                                        -> coe
                                                             seq (coe v20)
                                                             (case coe v8 of
                                                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v24
                                                                  -> coe
                                                                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                       (d_agreeDepth'45''43''43''45'mono_492
                                                                          (coe v9) (coe v1)
                                                                          (coe v12) (coe v15)
                                                                          (coe v18) (coe v21)
                                                                          (coe v6) (coe v7)
                                                                          (coe v24))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                         -> case coe v3 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> case coe v4 of
                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v17 v18
                                              -> coe
                                                   seq (coe v17)
                                                   (case coe v5 of
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v20 v21
                                                        -> coe
                                                             seq (coe v20)
                                                             (case coe v8 of
                                                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v24
                                                                  -> coe
                                                                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                       (d_agreeDepth'45''43''43''45'mono_492
                                                                          (coe v9) (coe v1)
                                                                          (coe v12) (coe v15)
                                                                          (coe v18) (coe v21)
                                                                          (coe v6) (coe v7)
                                                                          (coe v24))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                         -> case coe v3 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> case coe v4 of
                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v17 v18
                                              -> coe
                                                   seq (coe v17)
                                                   (case coe v5 of
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v20 v21
                                                        -> coe
                                                             seq (coe v20)
                                                             (case coe v8 of
                                                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v24
                                                                  -> coe
                                                                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                       (d_agreeDepth'45''43''43''45'mono_492
                                                                          (coe v9) (coe v1)
                                                                          (coe v12) (coe v15)
                                                                          (coe v18) (coe v21)
                                                                          (coe v6) (coe v7)
                                                                          (coe v24))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Metric.FineAgreementUltrametric.agreeDepth-++-map≤
d_agreeDepth'45''43''43''45'map'8804'_786 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
   MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_agreeDepth'45''43''43''45'map'8804'_786 v0 v1 v2 v3 v4 v5 v6
  = case coe v0 of
      0 -> coe
             seq (coe v2)
             (coe
                seq (coe v3)
                (coe
                   d_agreeDepth'45'map'8804'_110 (coe v1) (coe v6) (coe v4) (coe v5)))
      _ -> let v7 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                  -> case coe v9 of
                       MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                         -> case coe v3 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
                                -> case coe v12 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                            (d_agreeDepth'45''43''43''45'map'8804'_786
                                               (coe v7) (coe v1) (coe v10) (coe v13) (coe v4)
                                               (coe v5) (coe v6))
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                         -> case coe v3 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
                                -> case coe v12 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                            (d_agreeDepth'45''43''43''45'map'8804'_786
                                               (coe v7) (coe v1) (coe v10) (coe v13) (coe v4)
                                               (coe v5) (coe v6))
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                         -> case coe v3 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
                                -> case coe v12 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                            (d_agreeDepth'45''43''43''45'map'8804'_786
                                               (coe v7) (coe v1) (coe v10) (coe v13) (coe v4)
                                               (coe v5) (coe v6))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Metric.FineAgreementUltrametric.agreeDepth-∷ʳ≤
d_agreeDepth'45''8759''691''8804'_932 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_agreeDepth'45''8759''691''8804'_932 v0 v1 v2 v3 v4
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (case coe v3 of
                   MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                     -> case coe v4 of
                          MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                            -> coe
                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                 (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                          MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                            -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                          MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                            -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                     -> case coe v4 of
                          MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                            -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                          MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                            -> coe
                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                 (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                          MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                            -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                     -> case coe v4 of
                          MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                            -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                          MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                            -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                          MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                            -> coe
                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                 (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                         -> case coe v2 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
                                -> case coe v10 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                            (d_agreeDepth'45''8759''691''8804'_932
                                               (coe v5) (coe v8) (coe v11) (coe v3) (coe v4))
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                         -> case coe v2 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
                                -> case coe v10 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                            (d_agreeDepth'45''8759''691''8804'_932
                                               (coe v5) (coe v8) (coe v11) (coe v3) (coe v4))
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                         -> case coe v2 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
                                -> case coe v10 of
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
                                       -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                     MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                            (d_agreeDepth'45''8759''691''8804'_932
                                               (coe v5) (coe v8) (coe v11) (coe v3) (coe v4))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Metric.FineAgreementUltrametric.agreeDepth-∷≤
d_agreeDepth'45''8759''8804'_1034 ::
  Integer ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_agreeDepth'45''8759''8804'_1034 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
        -> case coe v2 of
             MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                       (coe
                          MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
                          (coe v0) (coe v3) (coe v4)))
             MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
        -> case coe v2 of
             MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                       (coe
                          MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
                          (coe v0) (coe v3) (coe v4)))
             MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
        -> case coe v2 of
             MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                       (coe
                          MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
                          (coe v0) (coe v3) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Metric.FineAgreementUltrametric.agreeDepthFine-shiftTail≥
d_agreeDepthFine'45'shiftTail'8805'_1078 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_agreeDepthFine'45'shiftTail'8805'_1078 v0 v1 v2
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe seq (coe v2) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5 v6
                  -> case coe v2 of
                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8 v9
                         -> coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
                              (coe
                                 d_agreeDepth'45''8759''691''8804'_932 (coe v3)
                                 (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v6)
                                 (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v9) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
                                 (coe
                                    addInt (coe (1 :: Integer))
                                    (coe
                                       MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
                                       (coe v3) (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v6)
                                       (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v9))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Metric.FineAgreementUltrametric._.lhs1
d_lhs1_1094 ::
  Integer ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lhs1_1094 = erased
-- DASHI.Metric.FineAgreementUltrametric._.lhs
d_lhs_1104 ::
  Integer ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lhs_1104 = erased
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-shiftTail≤
d_dNatFine'45'shiftTail'8804'_1122 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dNatFine'45'shiftTail'8804'_1122 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''8804'_5098
      (coe d_agreeDepthFine_28 (coe v0) (coe v1) (coe v2))
      (coe
         d_agreeDepthFine_28 (coe v0)
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_shiftTail_106
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_shiftTail_106
            (coe v0) (coe v2)))
      (coe v0)
      (coe
         d_agreeDepthFine'45'shiftTail'8805'_1078 (coe v0) (coe v1)
         (coe v2))
-- DASHI.Metric.FineAgreementUltrametric.agreeDepthFine-projTail≥
d_agreeDepthFine'45'projTail'8805'_1136 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_agreeDepthFine'45'projTail'8805'_1136 v0 v1 v2
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe seq (coe v2) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5 v6
                  -> case coe v2 of
                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8 v9
                         -> coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
                              (coe d_bound_1202 (coe v3) (coe v5) (coe v6) (coe v8) (coe v9))
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
                                 (coe
                                    addInt (coe (1 :: Integer))
                                    (coe
                                       MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Data.Vec.Base.du_reverse_616
                                          (coe
                                             MAlonzo.Code.Data.Vec.Base.du_init_658 (coe v3)
                                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5 v6)))
                                       (coe
                                          MAlonzo.Code.Data.Vec.Base.du_reverse_616
                                          (coe
                                             MAlonzo.Code.Data.Vec.Base.du_init_658 (coe v3)
                                             (coe
                                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8 v9))))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Metric.FineAgreementUltrametric._.init-∷ʳ-last
d_init'45''8759''691''45'last_1156 ::
  Integer ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_init'45''8759''691''45'last_1156 = erased
-- DASHI.Metric.FineAgreementUltrametric._.reverse-init-last
d_reverse'45'init'45'last_1176 ::
  Integer ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'init'45'last_1176 = erased
-- DASHI.Metric.FineAgreementUltrametric._.r1
d_r1_1180 ::
  Integer ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r1_1180 = erased
-- DASHI.Metric.FineAgreementUltrametric._.r2
d_r2_1190 ::
  Integer ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r2_1190 = erased
-- DASHI.Metric.FineAgreementUltrametric._.lhs1
d_lhs1_1192 ::
  Integer ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lhs1_1192 = erased
-- DASHI.Metric.FineAgreementUltrametric._.bound
d_bound_1202 ::
  Integer ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound_1202 v0 v1 v2 v3 v4
  = coe
      d_agreeDepth'45''8759''8804'_1034 (coe v0)
      (coe
         MAlonzo.Code.Data.Vec.Base.du_last_662 (coe v0)
         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v1 v2))
      (coe
         MAlonzo.Code.Data.Vec.Base.du_last_662 (coe v0)
         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4))
      (coe
         MAlonzo.Code.Data.Vec.Base.du_reverse_616
         (coe
            MAlonzo.Code.Data.Vec.Base.du_init_658 (coe v0)
            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v1 v2)))
      (coe
         MAlonzo.Code.Data.Vec.Base.du_reverse_616
         (coe
            MAlonzo.Code.Data.Vec.Base.du_init_658 (coe v0)
            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4)))
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-projTail≤
d_dNatFine'45'projTail'8804'_1212 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dNatFine'45'projTail'8804'_1212 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''8804'_5098
      (coe d_agreeDepthFine_28 (coe v0) (coe v1) (coe v2))
      (coe
         d_agreeDepthFine_28 (coe v0)
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_projTail_116
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_projTail_116
            (coe v0) (coe v2)))
      (coe v0)
      (coe
         d_agreeDepthFine'45'projTail'8805'_1136 (coe v0) (coe v1) (coe v2))
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-++
d_dNatFine'45''43''43'_1232 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dNatFine'45''43''43'_1232 = erased
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-++-map≤
d_dNatFine'45''43''43''45'map'8804'_1266 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
   MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dNatFine'45''43''43''45'map'8804'_1266 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
         (coe
            d_dNatFine_36 (coe addInt (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
               (coe MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v6) (coe v2))
               (coe v4))
            (coe
               MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
               (coe MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v6) (coe v3))
               (coe v5))))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''8804'_5098
            (coe
               MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
               (coe addInt (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))
            (coe
               MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
               (coe addInt (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
                  (coe
                     MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v6)
                     (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
                  (coe
                     MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v6)
                     (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3))))
            (coe addInt (coe v0) (coe v1))
            (coe
               d_agreeDepth'45''43''43''45'map'8804'_786 (coe v1) (coe v0)
               (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
               (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
               (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
               (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3) (coe v6)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
            (coe
               MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_dNat_24
               (coe addInt (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))))
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-++-map≤-tail
d_dNatFine'45''43''43''45'map'8804''45'tail_1314 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
   MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dNatFine'45''43''43''45'map'8804''45'tail_1314 v0 v1 v2 v3 v4 v5
                                                 v6
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
         (coe
            d_dNatFine_36 (coe addInt (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Data.Vec.Base.du__'43''43'__188 (coe v2)
               (coe MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v6) (coe v4)))
            (coe
               MAlonzo.Code.Data.Vec.Base.du__'43''43'__188 (coe v3)
               (coe MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v6) (coe v5)))))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''8804'_5098
            (coe
               MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
               (coe addInt (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))
            (coe
               MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
               (coe addInt (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe
                     MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v6)
                     (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4))
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe
                     MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v6)
                     (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5))
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))
            (coe addInt (coe v0) (coe v1))
            (coe
               d_agreeDepth'45''43''43''45'mono_492 (coe v1) (coe v0)
               (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
               (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
               (coe
                  MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v6)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v6)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5))
               (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
               (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)
               (coe
                  d_agreeDepth'45'map'8804'_110 (coe v1) (coe v6)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
            (coe
               MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_dNat_24
               (coe addInt (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2))
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
                  (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))))
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-++-shiftTail≤
d_dNatFine'45''43''43''45'shiftTail'8804'_1362 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dNatFine'45''43''43''45'shiftTail'8804'_1362 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''8804'_5098
      (coe
         MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
         (coe addInt (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2))
         (coe
            MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))
      (coe
         MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
         (coe addInt (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
            (coe
               MAlonzo.Code.Data.Vec.Base.du_reverse_616
               (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_shiftTail_106
                  (coe v1) (coe v4)))
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2))
         (coe
            MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
            (coe
               MAlonzo.Code.Data.Vec.Base.du_reverse_616
               (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_shiftTail_106
                  (coe v1) (coe v5)))
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))
      (coe addInt (coe v0) (coe v1))
      (coe
         d_agreeDepth'45''43''43''45'mono_492 (coe v1) (coe v0)
         (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
         (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
         (coe
            MAlonzo.Code.Data.Vec.Base.du_reverse_616
            (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_shiftTail_106
               (coe v1) (coe v4)))
         (coe
            MAlonzo.Code.Data.Vec.Base.du_reverse_616
            (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_shiftTail_106
               (coe v1) (coe v5)))
         (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
         (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)
         (coe
            d_agreeDepthFine'45'shiftTail'8805'_1078 (coe v1) (coe v4)
            (coe v5)))
-- DASHI.Metric.FineAgreementUltrametric.dNatFine-++-projTail≤
d_dNatFine'45''43''43''45'projTail'8804'_1398 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dNatFine'45''43''43''45'projTail'8804'_1398 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''8804'_5098
      (coe
         MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
         (coe addInt (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2))
         (coe
            MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))
      (coe
         MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_agreeDepth_8
         (coe addInt (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
            (coe
               MAlonzo.Code.Data.Vec.Base.du_reverse_616
               (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_projTail_116
                  (coe v1) (coe v4)))
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2))
         (coe
            MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
            (coe
               MAlonzo.Code.Data.Vec.Base.du_reverse_616
               (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_projTail_116
                  (coe v1) (coe v5)))
            (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)))
      (coe addInt (coe v0) (coe v1))
      (coe
         d_agreeDepth'45''43''43''45'mono_492 (coe v1) (coe v0)
         (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v4)
         (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v5)
         (coe
            MAlonzo.Code.Data.Vec.Base.du_reverse_616
            (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_projTail_116
               (coe v1) (coe v4)))
         (coe
            MAlonzo.Code.Data.Vec.Base.du_reverse_616
            (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_projTail_116
               (coe v1) (coe v5)))
         (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
         (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)
         (coe
            d_agreeDepthFine'45'projTail'8805'_1136 (coe v1) (coe v4)
            (coe v5)))
-- DASHI.Metric.FineAgreementUltrametric.ultrametricVec
d_ultrametricVec_1424 ::
  Integer -> MAlonzo.Code.Ultrametric.T_Ultrametric_6
d_ultrametricVec_1424 v0
  = coe
      MAlonzo.Code.Ultrametric.C_Ultrametric'46'constructor_391
      (d_dNatFine_36 (coe v0))
      (\ v1 v2 v3 ->
         MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_ultraNat_542
           (coe v0) (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v1)
           (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
           (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3))

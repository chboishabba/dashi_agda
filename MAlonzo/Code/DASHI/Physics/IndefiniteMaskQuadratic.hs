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

module MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Algebra.Trit
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning._IsRelatedTo_
d__IsRelatedTo__8 a0 a1 = ()
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning._∎
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.begin_
d_begin__12 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__12 = erased
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.start
d_start_16 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_start_16 = erased
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.step-≈
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.step-≈-⟨
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.step-≈-⟩
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.step-≈˘
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.step-≡
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.step-≡-∣
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.step-≡-⟨
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.step-≡-⟩
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.step-≡˘
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.stop
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.∼-go
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
-- DASHI.Physics.IndefiniteMaskQuadratic.ℤ-Reasoning.≡-go
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
-- DASHI.Physics.IndefiniteMaskQuadratic.Sign
d_Sign_46 = ()
data T_Sign_46 = C_plus_48 | C_minus_50
-- DASHI.Physics.IndefiniteMaskQuadratic.signℤ
d_signℤ_52 :: T_Sign_46 -> Integer
d_signℤ_52 v0
  = case coe v0 of
      C_plus_48 -> coe (1 :: Integer)
      C_minus_50 -> coe (-1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.IndefiniteMaskQuadratic.toℤTrit
d_toℤTrit_54 :: MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 -> Integer
d_toℤTrit_54 v0
  = case coe v0 of
      MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8 -> coe (-1 :: Integer)
      MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10 -> coe (0 :: Integer)
      MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.IndefiniteMaskQuadratic.sqℤ
d_sqℤ_56 :: Integer -> Integer
d_sqℤ_56 v0
  = coe MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v0)
-- DASHI.Physics.IndefiniteMaskQuadratic.sumℤ
d_sumℤ_62 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_sumℤ_62 ~v0 v1 = du_sumℤ_62 v1
du_sumℤ_62 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_sumℤ_62 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe (0 :: Integer)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v2)
             (coe du_sumℤ_62 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.IndefiniteMaskQuadratic.Qσ
d_Qσ_70 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_Qσ_70 ~v0 v1 v2 = du_Qσ_70 v1 v2
du_Qσ_70 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_Qσ_70 v0 v1
  = coe
      du_sumℤ_62
      (coe
         MAlonzo.Code.Data.Vec.Base.du_zipWith_242
         (coe
            (\ v2 v3 ->
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                 (coe d_signℤ_52 (coe v2))
                 (coe d_sqℤ_56 (coe d_toℤTrit_54 (coe v3)))))
         (coe v0) (coe v1))
-- DASHI.Physics.IndefiniteMaskQuadratic.dotσ
d_dotσ_82 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_dotσ_82 ~v0 v1 v2 v3 = du_dotσ_82 v1 v2 v3
du_dotσ_82 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_dotσ_82 v0 v1 v2
  = coe
      du_sumℤ_62
      (coe
         MAlonzo.Code.Data.Vec.Base.du_zipWith_242
         (coe
            (\ v3 v4 ->
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                 (coe d_signℤ_52 (coe v3))
                 (coe
                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))))
         (coe v0)
         (coe
            MAlonzo.Code.Data.Vec.Base.du_zipWith_242
            (coe
               (\ v3 v4 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_toℤTrit_54 (coe v3)) (coe d_toℤTrit_54 (coe v4))))
            (coe v1) (coe v2)))
-- DASHI.Physics.IndefiniteMaskQuadratic.B2σ
d_B2σ_100 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_B2σ_100 ~v0 v1 v2 v3 = du_B2σ_100 v1 v2 v3
du_B2σ_100 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_B2σ_100 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe seq (coe v1) (coe seq (coe v2) (coe (0 :: Integer)))
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
                      -> coe
                           MAlonzo.Code.Data.Integer.Base.d__'43'__276
                           (coe
                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                              (coe d_signℤ_52 (coe v4))
                              (coe
                                 MAlonzo.Code.Data.Integer.Base.d__'45'__294
                                 (coe
                                    MAlonzo.Code.Data.Integer.Base.d__'45'__294
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                          (coe d_toℤTrit_54 (coe v7)) (coe d_toℤTrit_54 (coe v10)))
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                          (coe d_toℤTrit_54 (coe v7)) (coe d_toℤTrit_54 (coe v10))))
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                       (coe d_toℤTrit_54 (coe v7)) (coe d_toℤTrit_54 (coe v7))))
                                 (coe
                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                    (coe d_toℤTrit_54 (coe v10)) (coe d_toℤTrit_54 (coe v10)))))
                           (coe du_B2σ_100 (coe v5) (coe v8) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.IndefiniteMaskQuadratic.b2-trit
d_b2'45'trit_118 ::
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b2'45'trit_118 = erased
-- DASHI.Physics.IndefiniteMaskQuadratic.swap2
d_swap2_124 ::
  T_Sign_46 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_swap2_124 = erased
-- DASHI.Physics.IndefiniteMaskQuadratic.B2σ≡2dotσ
d_B2σ'8801'2dotσ_160 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_B2σ'8801'2dotσ_160 = erased

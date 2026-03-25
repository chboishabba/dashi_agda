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

module MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.DASHI.Algebra.Trit
import qualified MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic
import qualified MAlonzo.Code.DASHI.Physics.SignatureFromMask
import qualified MAlonzo.Code.DASHI.Physics.SignedPerm4
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- DASHI.Physics.OrbitProfileComputedSignedPerm.concat
d_concat_8 :: () -> [[AgdaAny]] -> [AgdaAny]
d_concat_8 ~v0 v1 = du_concat_8 v1
du_concat_8 :: [[AgdaAny]] -> [AgdaAny]
du_concat_8 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe du__'43''43'__20 (coe v1) (coe du_concat_8 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm._._++_
d__'43''43'__20 ::
  () ->
  [AgdaAny] ->
  [[AgdaAny]] -> () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d__'43''43'__20 ~v0 ~v1 ~v2 ~v3 v4 v5 = du__'43''43'__20 v4 v5
du__'43''43'__20 :: [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du__'43''43'__20 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe du__'43''43'__20 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm.concatMap
d_concatMap_34 ::
  () -> () -> (AgdaAny -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d_concatMap_34 ~v0 ~v1 v2 v3 = du_concatMap_34 v2 v3
du_concatMap_34 :: (AgdaAny -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du_concatMap_34 v0 v1
  = coe
      du_concat_8
      (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v1))
-- DASHI.Physics.OrbitProfileComputedSignedPerm.decEqTrit
d_decEqTrit_44 ::
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEqTrit_44 v0 v1
  = case coe v0 of
      MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
        -> case coe v1 of
             MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
        -> case coe v1 of
             MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
        -> case coe v1 of
             MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm.decEqVec
d_decEqVec_52 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEqVec_52 ~v0 v1 v2 = du_decEqVec_52 v1 v2
du_decEqVec_52 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decEqVec_52 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> let v8 = d_decEqTrit_44 (coe v3) (coe v6) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then coe
                                     seq (coe v10)
                                     (let v11 = coe du_decEqVec_52 (coe v4) (coe v7) in
                                      coe
                                        (case coe v11 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                             -> if coe v12
                                                  then coe
                                                         seq (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                               erased))
                                                  else coe
                                                         seq (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                              else coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v9)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm.allTrit
d_allTrit_110 :: [MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6]
d_allTrit_110
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- DASHI.Physics.OrbitProfileComputedSignedPerm.allVecTrit
d_allVecTrit_114 ::
  Integer -> [MAlonzo.Code.Data.Vec.Base.T_Vec_28]
d_allVecTrit_114 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_concatMap_34
                (coe
                   (\ v2 ->
                      coe
                        MAlonzo.Code.Data.List.Base.du_map_22
                        (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 (coe v2))
                        (coe d_allVecTrit_114 (coe v1))))
                (coe d_allTrit_110))
-- DASHI.Physics.OrbitProfileComputedSignedPerm.mask31
d_mask31_122 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_mask31_122
  = coe
      MAlonzo.Code.DASHI.Physics.SignatureFromMask.d_oneMinusRestPlus_36
      (coe (3 :: Integer))
-- DASHI.Physics.OrbitProfileComputedSignedPerm.isShell
d_isShell_126 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Bool
d_isShell_126 v0 v1
  = let v2
          = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2692
              (coe
                 MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.du_sumℤ_62
                 (coe
                    MAlonzo.Code.Data.Vec.Base.du_zipWith_242
                    (coe
                       (\ v2 v3 ->
                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                            (coe
                               MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.d_signℤ_52
                               (coe v2))
                            (coe
                               MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.d_sqℤ_56
                               (coe
                                  MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.d_toℤTrit_54
                                  (coe v3)))))
                    (coe
                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                       (coe MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.C_minus_50)
                       (MAlonzo.Code.DASHI.Physics.SignatureFromMask.d_replicatePlus_30
                          (coe (3 :: Integer))))
                    (coe v1)))
              (coe v0) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe seq (coe v4) (coe v3)
                else coe
                       seq (coe v4)
                       (let v5
                              = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2692
                                  (coe
                                     MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.du_sumℤ_62
                                     (coe
                                        MAlonzo.Code.Data.Vec.Base.du_zipWith_242
                                        (coe
                                           (\ v5 v6 ->
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe
                                                   MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.d_signℤ_52
                                                   (coe v5))
                                                (coe
                                                   MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.d_sqℤ_56
                                                   (coe
                                                      MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.d_toℤTrit_54
                                                      (coe v6)))))
                                        (coe
                                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                           (coe
                                              MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.C_minus_50)
                                           (MAlonzo.Code.DASHI.Physics.SignatureFromMask.d_replicatePlus_30
                                              (coe (3 :: Integer))))
                                        (coe v1)))
                                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0)) in
                        coe
                          (case coe v5 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                               -> if coe v6
                                    then coe seq (coe v7) (coe v6)
                                    else coe seq (coe v7) (coe v6)
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Physics.OrbitProfileComputedSignedPerm.shellList
d_shellList_156 :: Integer -> [MAlonzo.Code.Data.Vec.Base.T_Vec_28]
d_shellList_156 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_filter'7495'_690
      (d_isShell_126 (coe v0)) (d_allVecTrit_114 (coe (4 :: Integer)))
-- DASHI.Physics.OrbitProfileComputedSignedPerm.flipTrit
d_flipTrit_160 ::
  Bool ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6
d_flipTrit_160 v0 v1
  = if coe v0
      then coe v1
      else coe MAlonzo.Code.DASHI.Algebra.Trit.d_inv_14 (coe v1)
-- DASHI.Physics.OrbitProfileComputedSignedPerm.flipBy3
d_flipBy3_166 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_flipBy3_166 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> coe
                           seq (coe v10)
                           (case coe v1 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
                                -> case coe v13 of
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v18 v19
                                              -> coe
                                                   seq (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                      (d_flipTrit_160 (coe v3) (coe v12))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         (d_flipTrit_160 (coe v6) (coe v15))
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            (d_flipTrit_160 (coe v9) (coe v18))
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm.actSigned4
d_actSigned4_180 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_actSigned4_180 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
                             -> coe
                                  seq (coe v13)
                                  (coe
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                     (d_flipTrit_160
                                        (coe
                                           MAlonzo.Code.DASHI.Physics.SignedPerm4.d_flipT_96
                                           (coe v0))
                                        (coe v3))
                                     (d_flipBy3_166
                                        (coe
                                           MAlonzo.Code.DASHI.Physics.SignedPerm4.d_flipS_98
                                           (coe v0))
                                        (coe
                                           MAlonzo.Code.DASHI.Physics.SignedPerm4.du_permute3_22
                                           (coe
                                              MAlonzo.Code.DASHI.Physics.SignedPerm4.d_perm_94
                                              (coe v0))
                                           (coe
                                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                              (coe
                                                 MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                                 (coe
                                                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12
                                                    (coe
                                                       MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm.allBool
d_allBool_192 :: [Bool]
d_allBool_192
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- DASHI.Physics.OrbitProfileComputedSignedPerm.allVecBool
d_allVecBool_196 ::
  Integer -> [MAlonzo.Code.Data.Vec.Base.T_Vec_28]
d_allVecBool_196 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_concatMap_34
                (coe
                   (\ v2 ->
                      coe
                        MAlonzo.Code.Data.List.Base.du_map_22
                        (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 (coe v2))
                        (coe d_allVecBool_196 (coe v1))))
                (coe d_allBool_192))
-- DASHI.Physics.OrbitProfileComputedSignedPerm.allFlips3
d_allFlips3_204 :: [MAlonzo.Code.Data.Vec.Base.T_Vec_28]
d_allFlips3_204 = coe d_allVecBool_196 (coe (3 :: Integer))
-- DASHI.Physics.OrbitProfileComputedSignedPerm.allSignedPerm4
d_allSignedPerm4_206 ::
  [MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86]
d_allSignedPerm4_206
  = coe
      du_concatMap_34
      (coe
         (\ v0 ->
            coe
              du_concatMap_34
              (coe
                 (\ v1 ->
                    coe
                      MAlonzo.Code.Data.List.Base.du_map_22
                      (coe
                         (\ v2 ->
                            coe
                              MAlonzo.Code.DASHI.Physics.SignedPerm4.C_SignedPerm4'46'constructor_4457
                              (coe v0) (coe v1) (coe v2)))
                      (coe d_allFlips3_204)))
              (coe d_allBool_192)))
      (coe MAlonzo.Code.DASHI.Physics.SignedPerm4.d_allPerm3_84)
-- DASHI.Physics.OrbitProfileComputedSignedPerm.member
d_member_220 ::
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> [AgdaAny] -> Bool
d_member_220 ~v0 v1 v2 v3 = du_member_220 v1 v2 v3
du_member_220 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> [AgdaAny] -> Bool
du_member_220 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v3 v4
        -> let v5 = coe v0 v1 v3 in
           coe
             (case coe v5 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                  -> if coe v6
                       then coe seq (coe v7) (coe v6)
                       else coe
                              seq (coe v7) (coe du_member_220 (coe v0) (coe v1) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm.nub
d_nub_260 ::
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
d_nub_260 ~v0 v1 v2 = du_nub_260 v1 v2
du_nub_260 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
du_nub_260 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4 = coe du_member_220 (coe v0) (coe v2) (coe v3) in
           coe
             (if coe v4
                then coe du_nub_260 (coe v0) (coe v3)
                else coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe du_nub_260 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm.orbitSizes
d_orbitSizes_288 ::
  [MAlonzo.Code.Data.Vec.Base.T_Vec_28] -> [Integer]
d_orbitSizes_288 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Data.List.Base.du_length_284
                (coe
                   du_nub_260 (coe du_decEqVec_52)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_map_22
                      (coe (\ v3 -> d_actSigned4_180 (coe v3) (coe v1)))
                      (coe d_allSignedPerm4_206))))
             (coe
                d_orbitSizes_288
                (coe
                   MAlonzo.Code.Data.List.Base.du_filter'7495'_690
                   (\ v3 ->
                      coe
                        du_not_298
                        (coe
                           du_member_220 (coe du_decEqVec_52) (coe v3)
                           (coe
                              du_nub_260 (coe du_decEqVec_52)
                              (coe
                                 MAlonzo.Code.Data.List.Base.du_map_22
                                 (coe (\ v4 -> d_actSigned4_180 (coe v4) (coe v1)))
                                 (coe d_allSignedPerm4_206)))))
                   v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm._.not
d_not_298 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  [MAlonzo.Code.Data.Vec.Base.T_Vec_28] -> Bool -> Bool
d_not_298 ~v0 ~v1 v2 = du_not_298 v2
du_not_298 :: Bool -> Bool
du_not_298 v0
  = if coe v0
      then coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      else coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
-- DASHI.Physics.OrbitProfileComputedSignedPerm.insertDesc
d_insertDesc_308 :: Integer -> [Integer] -> [Integer]
d_insertDesc_308 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1)
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2746
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2758)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
                        (coe
                           MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0)
                           (coe v2))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe
                              seq (coe v6)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                                 (coe d_insertDesc_308 (coe v0) (coe v3)))
                       else coe
                              seq (coe v6)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm.sortDesc
d_sortDesc_334 :: [Integer] -> [Integer]
d_sortDesc_334 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe d_insertDesc_308 (coe v1) (coe d_sortDesc_334 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitProfileComputedSignedPerm.shell1_p3_q1_computed
d_shell1_p3_q1_computed_340 :: [Integer]
d_shell1_p3_q1_computed_340
  = coe
      d_sortDesc_334
      (coe d_orbitSizes_288 (coe d_shellList_156 (coe (1 :: Integer))))
-- DASHI.Physics.OrbitProfileComputedSignedPerm.shell2_p3_q1_computed
d_shell2_p3_q1_computed_342 :: [Integer]
d_shell2_p3_q1_computed_342
  = coe
      d_sortDesc_334
      (coe d_orbitSizes_288 (coe d_shellList_156 (coe (2 :: Integer))))

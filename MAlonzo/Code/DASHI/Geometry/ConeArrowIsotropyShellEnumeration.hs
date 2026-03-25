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

module MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellEnumeration where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.ShellOrbitEnumerationDerivation
d_ShellOrbitEnumerationDerivation_18 a0 a1 a2 a3 a4 a5 = ()
data T_ShellOrbitEnumerationDerivation_18
  = C_ShellOrbitEnumerationDerivation'46'constructor_267 [Integer]
                                                         [Integer]
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.ShellOrbitEnumerationDerivation.shell1OrbitSizes
d_shell1OrbitSizes_36 ::
  T_ShellOrbitEnumerationDerivation_18 -> [Integer]
d_shell1OrbitSizes_36 v0
  = case coe v0 of
      C_ShellOrbitEnumerationDerivation'46'constructor_267 v1 v2
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.ShellOrbitEnumerationDerivation.shell2OrbitSizes
d_shell2OrbitSizes_38 ::
  T_ShellOrbitEnumerationDerivation_18 -> [Integer]
d_shell2OrbitSizes_38 v0
  = case coe v0 of
      C_ShellOrbitEnumerationDerivation'46'constructor_267 v1 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteCarrierShellDerivation
d_FiniteCarrierShellDerivation_60 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  = ()
data T_FiniteCarrierShellDerivation_60
  = C_FiniteCarrierShellDerivation'46'constructor_1333 (AgdaAny ->
                                                        AgdaAny ->
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                                                       [AgdaAny] (AgdaAny -> Bool) (AgdaAny -> Bool)
                                                       [AgdaAny] (AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteCarrierShellDerivation.decEq
d_decEq_102 ::
  T_FiniteCarrierShellDerivation_60 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEq_102 v0
  = case coe v0 of
      C_FiniteCarrierShellDerivation'46'constructor_1333 v1 v2 v3 v4 v5 v6
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteCarrierShellDerivation.carrierPoints
d_carrierPoints_104 ::
  T_FiniteCarrierShellDerivation_60 -> [AgdaAny]
d_carrierPoints_104 v0
  = case coe v0 of
      C_FiniteCarrierShellDerivation'46'constructor_1333 v1 v2 v3 v4 v5 v6
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteCarrierShellDerivation.shell1Pred
d_shell1Pred_106 ::
  T_FiniteCarrierShellDerivation_60 -> AgdaAny -> Bool
d_shell1Pred_106 v0
  = case coe v0 of
      C_FiniteCarrierShellDerivation'46'constructor_1333 v1 v2 v3 v4 v5 v6
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteCarrierShellDerivation.shell2Pred
d_shell2Pred_108 ::
  T_FiniteCarrierShellDerivation_60 -> AgdaAny -> Bool
d_shell2Pred_108 v0
  = case coe v0 of
      C_FiniteCarrierShellDerivation'46'constructor_1333 v1 v2 v3 v4 v5 v6
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteCarrierShellDerivation.actions
d_actions_110 :: T_FiniteCarrierShellDerivation_60 -> [AgdaAny]
d_actions_110 v0
  = case coe v0 of
      C_FiniteCarrierShellDerivation'46'constructor_1333 v1 v2 v3 v4 v5 v6
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteCarrierShellDerivation.act
d_act_112 ::
  T_FiniteCarrierShellDerivation_60 -> AgdaAny -> AgdaAny -> AgdaAny
d_act_112 v0
  = case coe v0 of
      C_FiniteCarrierShellDerivation'46'constructor_1333 v1 v2 v3 v4 v5 v6
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteShellEnumerationDerivation
d_FiniteShellEnumerationDerivation_134 a0 a1 a2 a3 a4 a5 a6 a7 a8
                                       a9
  = ()
data T_FiniteShellEnumerationDerivation_134
  = C_FiniteShellEnumerationDerivation'46'constructor_2783 (AgdaAny ->
                                                            AgdaAny ->
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                                                           [AgdaAny] [AgdaAny] [AgdaAny]
                                                           (AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteShellEnumerationDerivation.decEq
d_decEq_174 ::
  T_FiniteShellEnumerationDerivation_134 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEq_174 v0
  = case coe v0 of
      C_FiniteShellEnumerationDerivation'46'constructor_2783 v1 v2 v3 v4 v5
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteShellEnumerationDerivation.shell1Points
d_shell1Points_176 ::
  T_FiniteShellEnumerationDerivation_134 -> [AgdaAny]
d_shell1Points_176 v0
  = case coe v0 of
      C_FiniteShellEnumerationDerivation'46'constructor_2783 v1 v2 v3 v4 v5
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteShellEnumerationDerivation.shell2Points
d_shell2Points_178 ::
  T_FiniteShellEnumerationDerivation_134 -> [AgdaAny]
d_shell2Points_178 v0
  = case coe v0 of
      C_FiniteShellEnumerationDerivation'46'constructor_2783 v1 v2 v3 v4 v5
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteShellEnumerationDerivation.actions
d_actions_180 ::
  T_FiniteShellEnumerationDerivation_134 -> [AgdaAny]
d_actions_180 v0
  = case coe v0 of
      C_FiniteShellEnumerationDerivation'46'constructor_2783 v1 v2 v3 v4 v5
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.FiniteShellEnumerationDerivation.act
d_act_182 ::
  T_FiniteShellEnumerationDerivation_134 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_act_182 v0
  = case coe v0 of
      C_FiniteShellEnumerationDerivation'46'constructor_2783 v1 v2 v3 v4 v5
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.member
d_member_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> [AgdaAny] -> Bool
d_member_192 ~v0 ~v1 v2 v3 v4 = du_member_192 v2 v3 v4
du_member_192 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> [AgdaAny] -> Bool
du_member_192 v0 v1 v2
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
                              seq (coe v7) (coe du_member_192 (coe v0) (coe v1) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.nub
d_nub_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
d_nub_234 ~v0 ~v1 v2 v3 = du_nub_234 v2 v3
du_nub_234 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
du_nub_234 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4 = coe du_member_192 (coe v0) (coe v2) (coe v3) in
           coe
             (if coe v4
                then coe du_nub_234 (coe v0) (coe v3)
                else coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe du_nub_234 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.orbitSizes
d_orbitSizes_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> [Integer]
d_orbitSizes_272 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_orbitSizes_272 v4 v5 v6 v7
du_orbitSizes_272 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> [Integer]
du_orbitSizes_272 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe v3
      (:) v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Data.List.Base.du_length_284
                (coe
                   du_nub_234 (coe v0)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_map_22 (coe (\ v6 -> coe v2 v6 v4))
                      (coe v1))))
             (coe
                du_orbitSizes_272 (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Data.List.Base.du_filter'7495'_690
                   (\ v6 ->
                      coe
                        du_not_294
                        (coe
                           du_member_192 (coe v0) (coe v6)
                           (coe
                              du_nub_234 (coe v0)
                              (coe
                                 MAlonzo.Code.Data.List.Base.du_map_22 (coe (\ v7 -> coe v2 v7 v4))
                                 (coe v1)))))
                   v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration._.not
d_not_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> Bool -> Bool
d_not_294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_not_294 v9
du_not_294 :: Bool -> Bool
du_not_294 v0
  = if coe v0
      then coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      else coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.insertDesc
d_insertDesc_304 :: Integer -> [Integer] -> [Integer]
d_insertDesc_304 v0 v1
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
                                 (coe d_insertDesc_304 (coe v0) (coe v3)))
                       else coe
                              seq (coe v6)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.sortDesc
d_sortDesc_330 :: [Integer] -> [Integer]
d_sortDesc_330 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe d_insertDesc_304 (coe v1) (coe d_sortDesc_330 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.filterBy
d_filterBy_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
d_filterBy_340 ~v0 ~v1 = du_filterBy_340
du_filterBy_340 :: (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
du_filterBy_340
  = coe MAlonzo.Code.Data.List.Base.du_filter'7495'_690
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.buildShellOrbitEnumeration
d_buildShellOrbitEnumeration_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  T_ShellOrbitEnumerationDerivation_18 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
d_buildShellOrbitEnumeration_354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_buildShellOrbitEnumeration_354 v6
du_buildShellOrbitEnumeration_354 ::
  T_ShellOrbitEnumerationDerivation_18 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
du_buildShellOrbitEnumeration_354 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_ShellOrbitEnumeration'46'constructor_1915
      (coe d_shell1OrbitSizes_36 (coe v0))
      (coe d_shell2OrbitSizes_38 (coe v0))
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.buildShellOrbitEnumerationFromFinite
d_buildShellOrbitEnumerationFromFinite_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  () ->
  () ->
  T_FiniteShellEnumerationDerivation_134 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
d_buildShellOrbitEnumerationFromFinite_378 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6 ~v7 ~v8 ~v9 v10
  = du_buildShellOrbitEnumerationFromFinite_378 v10
du_buildShellOrbitEnumerationFromFinite_378 ::
  T_FiniteShellEnumerationDerivation_134 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
du_buildShellOrbitEnumerationFromFinite_378 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_ShellOrbitEnumeration'46'constructor_1915
      (coe
         d_sortDesc_330
         (coe
            du_orbitSizes_272 (coe d_decEq_174 (coe v0))
            (coe d_actions_180 (coe v0)) (coe d_act_182 (coe v0))
            (coe d_shell1Points_176 (coe v0))))
      (coe
         d_sortDesc_330
         (coe
            du_orbitSizes_272 (coe d_decEq_174 (coe v0))
            (coe d_actions_180 (coe v0)) (coe d_act_182 (coe v0))
            (coe d_shell2Points_178 (coe v0))))
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.act
d_act_384 ::
  T_FiniteShellEnumerationDerivation_134 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_act_384 v0 = coe d_act_182 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.actions
d_actions_386 ::
  T_FiniteShellEnumerationDerivation_134 -> [AgdaAny]
d_actions_386 v0 = coe d_actions_180 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.decEq
d_decEq_388 ::
  T_FiniteShellEnumerationDerivation_134 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEq_388 v0 = coe d_decEq_174 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.shell1Points
d_shell1Points_390 ::
  T_FiniteShellEnumerationDerivation_134 -> [AgdaAny]
d_shell1Points_390 v0 = coe d_shell1Points_176 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.shell2Points
d_shell2Points_392 ::
  T_FiniteShellEnumerationDerivation_134 -> [AgdaAny]
d_shell2Points_392 v0 = coe d_shell2Points_178 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.buildFiniteShellEnumeration
d_buildFiniteShellEnumeration_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  () ->
  () ->
  T_FiniteCarrierShellDerivation_60 ->
  T_FiniteShellEnumerationDerivation_134
d_buildFiniteShellEnumeration_414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 v10
  = du_buildFiniteShellEnumeration_414 v10
du_buildFiniteShellEnumeration_414 ::
  T_FiniteCarrierShellDerivation_60 ->
  T_FiniteShellEnumerationDerivation_134
du_buildFiniteShellEnumeration_414 v0
  = coe
      C_FiniteShellEnumerationDerivation'46'constructor_2783
      (coe d_decEq_102 (coe v0))
      (coe
         du_filterBy_340 (d_shell1Pred_106 (coe v0))
         (d_carrierPoints_104 (coe v0)))
      (coe
         du_filterBy_340 (d_shell2Pred_108 (coe v0))
         (d_carrierPoints_104 (coe v0)))
      (coe d_actions_110 (coe v0)) (coe d_act_112 (coe v0))
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.act
d_act_420 ::
  T_FiniteCarrierShellDerivation_60 -> AgdaAny -> AgdaAny -> AgdaAny
d_act_420 v0 = coe d_act_112 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.actions
d_actions_422 :: T_FiniteCarrierShellDerivation_60 -> [AgdaAny]
d_actions_422 v0 = coe d_actions_110 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.carrierPoints
d_carrierPoints_424 ::
  T_FiniteCarrierShellDerivation_60 -> [AgdaAny]
d_carrierPoints_424 v0 = coe d_carrierPoints_104 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.decEq
d_decEq_426 ::
  T_FiniteCarrierShellDerivation_60 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEq_426 v0 = coe d_decEq_102 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.shell1Pred
d_shell1Pred_428 ::
  T_FiniteCarrierShellDerivation_60 -> AgdaAny -> Bool
d_shell1Pred_428 v0 = coe d_shell1Pred_106 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.D.shell2Pred
d_shell2Pred_430 ::
  T_FiniteCarrierShellDerivation_60 -> AgdaAny -> Bool
d_shell2Pred_430 v0 = coe d_shell2Pred_108 (coe v0)
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.buildFiniteShellEnumerationFromShellAction
d_buildFiniteShellEnumerationFromShellAction_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  T_FiniteShellEnumerationDerivation_134
d_buildFiniteShellEnumerationFromShellAction_444 ~v0 ~v1 ~v2 ~v3
                                                 ~v4 v5
  = du_buildFiniteShellEnumerationFromShellAction_444 v5
du_buildFiniteShellEnumerationFromShellAction_444 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  T_FiniteShellEnumerationDerivation_134
du_buildFiniteShellEnumerationFromShellAction_444 v0
  = coe
      C_FiniteShellEnumerationDerivation'46'constructor_2783
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_decEq_210
         (coe
            MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.d_finiteShell_56
            (coe v0)))
      (coe
         du_filterBy_340 (coe du_shell1Pred''_478 (coe v0))
         (coe du_carrierPts_476 (coe v0)))
      (coe
         du_filterBy_340 (coe du_shell2Pred''_480 (coe v0))
         (coe du_carrierPts_476 (coe v0)))
      (coe du_groupPts_482 (coe v0)) (coe du_actFinite''_484 (coe v0))
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration._.Fin.CarrierPoint
d_CarrierPoint_454 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  ()
d_CarrierPoint_454 = erased
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration._.Iso.GroupPoint
d_GroupPoint_468 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  ()
d_GroupPoint_468 = erased
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration._.carrierPts
d_carrierPts_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  [AgdaAny]
d_carrierPts_476 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_carrierPts_476 v5
du_carrierPts_476 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  [AgdaAny]
du_carrierPts_476 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_carrierPoints_212
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.d_finiteShell_56
         (coe v0))
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration._.shell1Pred'
d_shell1Pred''_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  AgdaAny -> Bool
d_shell1Pred''_478 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_shell1Pred''_478 v5
du_shell1Pred''_478 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  AgdaAny -> Bool
du_shell1Pred''_478 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_shell1Pred_216
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.d_finiteShell_56
         (coe v0))
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration._.shell2Pred'
d_shell2Pred''_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  AgdaAny -> Bool
d_shell2Pred''_480 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_shell2Pred''_480 v5
du_shell2Pred''_480 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  AgdaAny -> Bool
du_shell2Pred''_480 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_shell2Pred_218
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.d_finiteShell_56
         (coe v0))
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration._.groupPts
d_groupPts_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  [AgdaAny]
d_groupPts_482 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_groupPts_482 v5
du_groupPts_482 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  [AgdaAny]
du_groupPts_482 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_groupPoints_252
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.d_finiteIso_58
         (coe v0))
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration._.actFinite'
d_actFinite''_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_actFinite''_484 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_actFinite''_484 v5
du_actFinite''_484 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_actFinite''_484 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_actFinite_254
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.d_finiteIso_58
         (coe v0))
-- DASHI.Geometry.ConeArrowIsotropyShellEnumeration.buildShellOrbitEnumerationFromShellAction
d_buildShellOrbitEnumerationFromShellAction_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
d_buildShellOrbitEnumerationFromShellAction_498 ~v0 ~v1 ~v2 ~v3 ~v4
                                                v5
  = du_buildShellOrbitEnumerationFromShellAction_498 v5
du_buildShellOrbitEnumerationFromShellAction_498 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
du_buildShellOrbitEnumerationFromShellAction_498 v0
  = coe
      du_buildShellOrbitEnumerationFromFinite_378
      (coe du_buildFiniteShellEnumerationFromShellAction_444 (coe v0))

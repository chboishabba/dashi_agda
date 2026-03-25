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

module MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- DASHI.Geometry.ConeTimeIsotropy.ConeStructure
d_ConeStructure_10 a0 a1 = ()
newtype T_ConeStructure_10
  = C_ConeStructure'46'constructor_13 MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
-- DASHI.Geometry.ConeTimeIsotropy.ConeStructure.Cone
d_Cone_20 :: T_ConeStructure_10 -> AgdaAny -> ()
d_Cone_20 = erased
-- DASHI.Geometry.ConeTimeIsotropy.ConeStructure.ConeNontrivial
d_ConeNontrivial_22 ::
  T_ConeStructure_10 -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_ConeNontrivial_22 v0
  = case coe v0 of
      C_ConeStructure'46'constructor_13 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.TimeArrow
d_TimeArrow_28 a0 a1 = ()
data T_TimeArrow_28
  = C_TimeArrow'46'constructor_115 (AgdaAny ->
                                    MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6)
                                   (AgdaAny ->
                                    AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6)
-- DASHI.Geometry.ConeTimeIsotropy.TimeArrow._≺_
d__'8826'__48 :: T_TimeArrow_28 -> AgdaAny -> AgdaAny -> ()
d__'8826'__48 = erased
-- DASHI.Geometry.ConeTimeIsotropy.TimeArrow.Irreflexive
d_Irreflexive_52 ::
  T_TimeArrow_28 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_Irreflexive_52 v0
  = case coe v0 of
      C_TimeArrow'46'constructor_115 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.TimeArrow.Transitive
d_Transitive_60 ::
  T_TimeArrow_28 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_Transitive_60 v0
  = case coe v0 of
      C_TimeArrow'46'constructor_115 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.IsotropyAction
d_IsotropyAction_66 a0 a1 = ()
data T_IsotropyAction_66
  = C_IsotropyAction'46'constructor_293 (AgdaAny ->
                                         AgdaAny -> AgdaAny)
                                        (AgdaAny ->
                                         AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6)
                                        (AgdaAny ->
                                         AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6)
-- DASHI.Geometry.ConeTimeIsotropy.IsotropyAction.G
d_G_88 :: T_IsotropyAction_66 -> ()
d_G_88 = erased
-- DASHI.Geometry.ConeTimeIsotropy.IsotropyAction._•_
d__'8226'__90 ::
  T_IsotropyAction_66 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8226'__90 v0
  = case coe v0 of
      C_IsotropyAction'46'constructor_293 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.IsotropyAction.PresCone
d_PresCone_96 ::
  T_IsotropyAction_66 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_PresCone_96 v0
  = case coe v0 of
      C_IsotropyAction'46'constructor_293 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.IsotropyAction.PresQ
d_PresQ_102 ::
  T_IsotropyAction_66 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_PresQ_102 v0
  = case coe v0 of
      C_IsotropyAction'46'constructor_293 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.ShellStructure
d_ShellStructure_108 a0 a1 = ()
data T_ShellStructure_108 = C_ShellStructure'46'constructor_435
-- DASHI.Geometry.ConeTimeIsotropy.ShellStructure.Shell1
d_Shell1_118 :: T_ShellStructure_108 -> AgdaAny -> ()
d_Shell1_118 = erased
-- DASHI.Geometry.ConeTimeIsotropy.ShellStructure.Shell2
d_Shell2_120 :: T_ShellStructure_108 -> AgdaAny -> ()
d_Shell2_120 = erased
-- DASHI.Geometry.ConeTimeIsotropy.AdmissibleMove
d_AdmissibleMove_126 a0 a1 = ()
data T_AdmissibleMove_126 = C_AdmissibleMove'46'constructor_503
-- DASHI.Geometry.ConeTimeIsotropy.AdmissibleMove._↦_
d__'8614'__134 :: T_AdmissibleMove_126 -> AgdaAny -> AgdaAny -> ()
d__'8614'__134 = erased
-- DASHI.Geometry.ConeTimeIsotropy.ShellIsotropyAction
d_ShellIsotropyAction_144 a0 a1 a2 a3 = ()
data T_ShellIsotropyAction_144
  = C_ShellIsotropyAction'46'constructor_765 (AgdaAny ->
                                              AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6)
                                             (AgdaAny ->
                                              AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6)
-- DASHI.Geometry.ConeTimeIsotropy.ShellIsotropyAction.PresShell1
d_PresShell1_170 ::
  T_ShellIsotropyAction_144 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_PresShell1_170 v0
  = case coe v0 of
      C_ShellIsotropyAction'46'constructor_765 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.ShellIsotropyAction.PresShell2
d_PresShell2_176 ::
  T_ShellIsotropyAction_144 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_PresShell2_176 v0
  = case coe v0 of
      C_ShellIsotropyAction'46'constructor_765 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.FiniteShellRealization
d_FiniteShellRealization_182 a0 a1 = ()
data T_FiniteShellRealization_182
  = C_FiniteShellRealization'46'constructor_1089 (AgdaAny ->
                                                  AgdaAny ->
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                                                 [AgdaAny] (AgdaAny -> AgdaAny) (AgdaAny -> Bool)
                                                 (AgdaAny -> Bool)
-- DASHI.Geometry.ConeTimeIsotropy.FiniteShellRealization.CarrierPoint
d_CarrierPoint_204 :: T_FiniteShellRealization_182 -> ()
d_CarrierPoint_204 = erased
-- DASHI.Geometry.ConeTimeIsotropy.FiniteShellRealization.decEq
d_decEq_210 ::
  T_FiniteShellRealization_182 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEq_210 v0
  = case coe v0 of
      C_FiniteShellRealization'46'constructor_1089 v2 v3 v4 v5 v6
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.FiniteShellRealization.carrierPoints
d_carrierPoints_212 :: T_FiniteShellRealization_182 -> [AgdaAny]
d_carrierPoints_212 v0
  = case coe v0 of
      C_FiniteShellRealization'46'constructor_1089 v2 v3 v4 v5 v6
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.FiniteShellRealization.embed
d_embed_214 :: T_FiniteShellRealization_182 -> AgdaAny -> AgdaAny
d_embed_214 v0
  = case coe v0 of
      C_FiniteShellRealization'46'constructor_1089 v2 v3 v4 v5 v6
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.FiniteShellRealization.shell1Pred
d_shell1Pred_216 :: T_FiniteShellRealization_182 -> AgdaAny -> Bool
d_shell1Pred_216 v0
  = case coe v0 of
      C_FiniteShellRealization'46'constructor_1089 v2 v3 v4 v5 v6
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.FiniteShellRealization.shell2Pred
d_shell2Pred_218 :: T_FiniteShellRealization_182 -> AgdaAny -> Bool
d_shell2Pred_218 v0
  = case coe v0 of
      C_FiniteShellRealization'46'constructor_1089 v2 v3 v4 v5 v6
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.FiniteIsotropyRealization
d_FiniteIsotropyRealization_228 a0 a1 a2 a3 = ()
data T_FiniteIsotropyRealization_228
  = C_FiniteIsotropyRealization'46'constructor_1717 [AgdaAny]
                                                    (AgdaAny -> AgdaAny -> AgdaAny)
                                                    (AgdaAny ->
                                                     AgdaAny ->
                                                     MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6)
-- DASHI.Geometry.ConeTimeIsotropy.FiniteIsotropyRealization.GroupPoint
d_GroupPoint_250 :: T_FiniteIsotropyRealization_228 -> ()
d_GroupPoint_250 = erased
-- DASHI.Geometry.ConeTimeIsotropy.FiniteIsotropyRealization.groupPoints
d_groupPoints_252 :: T_FiniteIsotropyRealization_228 -> [AgdaAny]
d_groupPoints_252 v0
  = case coe v0 of
      C_FiniteIsotropyRealization'46'constructor_1717 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.FiniteIsotropyRealization.actFinite
d_actFinite_254 ::
  T_FiniteIsotropyRealization_228 -> AgdaAny -> AgdaAny -> AgdaAny
d_actFinite_254 v0
  = case coe v0 of
      C_FiniteIsotropyRealization'46'constructor_1717 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.FiniteIsotropyRealization.actCompat
d_actCompat_260 ::
  T_FiniteIsotropyRealization_228 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_actCompat_260 v0
  = case coe v0 of
      C_FiniteIsotropyRealization'46'constructor_1717 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.ShellOrbitEnumeration
d_ShellOrbitEnumeration_262 = ()
data T_ShellOrbitEnumeration_262
  = C_ShellOrbitEnumeration'46'constructor_1915 [Integer] [Integer]
-- DASHI.Geometry.ConeTimeIsotropy.ShellOrbitEnumeration.shell1OrbitSizes
d_shell1OrbitSizes_268 :: T_ShellOrbitEnumeration_262 -> [Integer]
d_shell1OrbitSizes_268 v0
  = case coe v0 of
      C_ShellOrbitEnumeration'46'constructor_1915 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.ShellOrbitEnumeration.shell2OrbitSizes
d_shell2OrbitSizes_270 :: T_ShellOrbitEnumeration_262 -> [Integer]
d_shell2OrbitSizes_270 v0
  = case coe v0 of
      C_ShellOrbitEnumeration'46'constructor_1915 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.OrbitProfileData
d_OrbitProfileData_272 = ()
data T_OrbitProfileData_272
  = C_OrbitProfileData'46'constructor_1961 Integer [Integer]
                                           [Integer]
-- DASHI.Geometry.ConeTimeIsotropy.OrbitProfileData.orientationTag
d_orientationTag_280 :: T_OrbitProfileData_272 -> Integer
d_orientationTag_280 v0
  = case coe v0 of
      C_OrbitProfileData'46'constructor_1961 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.OrbitProfileData.shell1Profile
d_shell1Profile_282 :: T_OrbitProfileData_272 -> [Integer]
d_shell1Profile_282 v0
  = case coe v0 of
      C_OrbitProfileData'46'constructor_1961 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.OrbitProfileData.shell2Profile
d_shell2Profile_284 :: T_OrbitProfileData_272 -> [Integer]
d_shell2Profile_284 v0
  = case coe v0 of
      C_OrbitProfileData'46'constructor_1961 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeTimeIsotropy.Signature
d_Signature_286 = ()
data T_Signature_286 = C_sig31_288 | C_sig13_290 | C_other_292

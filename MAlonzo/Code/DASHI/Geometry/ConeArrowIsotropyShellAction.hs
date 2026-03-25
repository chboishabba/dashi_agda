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

module MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy

-- DASHI.Geometry.ConeArrowIsotropyShellAction.AbstractShellAction
d_AbstractShellAction_16 a0 a1 a2 a3 a4 = ()
data T_AbstractShellAction_16
  = C_AbstractShellAction'46'constructor_1087 MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ConeStructure_10
                                              MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_TimeArrow_28
                                              MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_IsotropyAction_66
                                              MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellIsotropyAction_144
                                              MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_FiniteShellRealization_182
                                              MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_FiniteIsotropyRealization_228
-- DASHI.Geometry.ConeArrowIsotropyShellAction.AbstractShellAction.coneS
d_coneS_44 ::
  T_AbstractShellAction_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ConeStructure_10
d_coneS_44 v0
  = case coe v0 of
      C_AbstractShellAction'46'constructor_1087 v1 v2 v3 v6 v7 v8
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellAction.AbstractShellAction.arrow
d_arrow_46 ::
  T_AbstractShellAction_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_TimeArrow_28
d_arrow_46 v0
  = case coe v0 of
      C_AbstractShellAction'46'constructor_1087 v1 v2 v3 v6 v7 v8
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellAction.AbstractShellAction.iso
d_iso_48 ::
  T_AbstractShellAction_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_IsotropyAction_66
d_iso_48 v0
  = case coe v0 of
      C_AbstractShellAction'46'constructor_1087 v1 v2 v3 v6 v7 v8
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellAction.AbstractShellAction.shellS
d_shellS_50 ::
  T_AbstractShellAction_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellStructure_108
d_shellS_50 = erased
-- DASHI.Geometry.ConeArrowIsotropyShellAction.AbstractShellAction.moveS
d_moveS_52 ::
  T_AbstractShellAction_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_AdmissibleMove_126
d_moveS_52 = erased
-- DASHI.Geometry.ConeArrowIsotropyShellAction.AbstractShellAction.shellIso
d_shellIso_54 ::
  T_AbstractShellAction_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellIsotropyAction_144
d_shellIso_54 v0
  = case coe v0 of
      C_AbstractShellAction'46'constructor_1087 v1 v2 v3 v6 v7 v8
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellAction.AbstractShellAction.finiteShell
d_finiteShell_56 ::
  T_AbstractShellAction_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_FiniteShellRealization_182
d_finiteShell_56 v0
  = case coe v0 of
      C_AbstractShellAction'46'constructor_1087 v1 v2 v3 v6 v7 v8
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellAction.AbstractShellAction.finiteIso
d_finiteIso_58 ::
  T_AbstractShellAction_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_FiniteIsotropyRealization_228
d_finiteIso_58 v0
  = case coe v0 of
      C_AbstractShellAction'46'constructor_1087 v1 v2 v3 v6 v7 v8
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowIsotropyShellAction.buildShellAction
d_buildShellAction_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.T_SignatureAxioms_16 ->
  T_AbstractShellAction_16
d_buildShellAction_72 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_buildShellAction_72 v5
du_buildShellAction_72 ::
  MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.T_SignatureAxioms_16 ->
  T_AbstractShellAction_16
du_buildShellAction_72 v0
  = coe
      C_AbstractShellAction'46'constructor_1087
      (MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.d_ConeS_116
         (coe v0))
      (MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.d_Arrow_118
         (coe v0))
      (MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.d_Iso_120
         (coe v0))
      (MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.d_ShellIso_126
         (coe v0))
      (MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.d_FiniteShell_128
         (coe v0))
      (MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.d_FiniteIso_130
         (coe v0))

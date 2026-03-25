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

module MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm

-- DASHI.Geometry.Signature31FromConeArrowIsotropy.SignatureAxioms
d_SignatureAxioms_16 a0 a1 a2 a3 a4 = ()
data T_SignatureAxioms_16
  = C_SignatureAxioms'46'constructor_1573 MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ConeStructure_10
                                          MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_TimeArrow_28
                                          MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_IsotropyAction_66
                                          MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellIsotropyAction_144
                                          MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_FiniteShellRealization_182
                                          MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_FiniteIsotropyRealization_228
                                          (AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6)
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.SignatureAxioms.ConeS
d_ConeS_116 ::
  T_SignatureAxioms_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ConeStructure_10
d_ConeS_116 v0
  = case coe v0 of
      C_SignatureAxioms'46'constructor_1573 v1 v2 v3 v6 v7 v8 v9
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.SignatureAxioms.Arrow
d_Arrow_118 ::
  T_SignatureAxioms_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_TimeArrow_28
d_Arrow_118 v0
  = case coe v0 of
      C_SignatureAxioms'46'constructor_1573 v1 v2 v3 v6 v7 v8 v9
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.SignatureAxioms.Iso
d_Iso_120 ::
  T_SignatureAxioms_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_IsotropyAction_66
d_Iso_120 v0
  = case coe v0 of
      C_SignatureAxioms'46'constructor_1573 v1 v2 v3 v6 v7 v8 v9
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.SignatureAxioms.ShellS
d_ShellS_122 ::
  T_SignatureAxioms_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellStructure_108
d_ShellS_122 = erased
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.SignatureAxioms.MoveS
d_MoveS_124 ::
  T_SignatureAxioms_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_AdmissibleMove_126
d_MoveS_124 = erased
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.SignatureAxioms.ShellIso
d_ShellIso_126 ::
  T_SignatureAxioms_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellIsotropyAction_144
d_ShellIso_126 v0
  = case coe v0 of
      C_SignatureAxioms'46'constructor_1573 v1 v2 v3 v6 v7 v8 v9
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.SignatureAxioms.FiniteShell
d_FiniteShell_128 ::
  T_SignatureAxioms_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_FiniteShellRealization_182
d_FiniteShell_128 v0
  = case coe v0 of
      C_SignatureAxioms'46'constructor_1573 v1 v2 v3 v6 v7 v8 v9
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.SignatureAxioms.FiniteIso
d_FiniteIso_130 ::
  T_SignatureAxioms_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_FiniteIsotropyRealization_228
d_FiniteIso_130 v0
  = case coe v0 of
      C_SignatureAxioms'46'constructor_1573 v1 v2 v3 v6 v7 v8 v9
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.SignatureAxioms.Timelike↔Cone
d_Timelike'8596'Cone_134 ::
  T_SignatureAxioms_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_Timelike'8596'Cone_134 v0
  = case coe v0 of
      C_SignatureAxioms'46'constructor_1573 v1 v2 v3 v6 v7 v8 v9
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.Signature31FromConeArrowIsotropyAxioms
d_Signature31FromConeArrowIsotropyAxioms_146 a0 a1 a2 a3 a4 = ()
newtype T_Signature31FromConeArrowIsotropyAxioms_146
  = C_Signature31FromConeArrowIsotropyAxioms'46'constructor_3413 (T_SignatureAxioms_16 ->
                                                                  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286)
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.Signature31FromConeArrowIsotropyAxioms.Signature31Theorem
d_Signature31Theorem_164 ::
  T_Signature31FromConeArrowIsotropyAxioms_146 ->
  T_SignatureAxioms_16 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_Signature31Theorem_164 v0
  = case coe v0 of
      C_Signature31FromConeArrowIsotropyAxioms'46'constructor_3413 v1
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromConeArrowIsotropy.Signature31Theorem
d_Signature31Theorem_178 ::
  T_SignatureAxioms_16 ->
  T_Signature31FromConeArrowIsotropyAxioms_146 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_Signature31Theorem_178 v0 v1 = coe d_Signature31Theorem_164 v1 v0

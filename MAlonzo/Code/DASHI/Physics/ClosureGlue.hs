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

module MAlonzo.Code.DASHI.Physics.ClosureGlue where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Contraction
import qualified MAlonzo.Code.DASHI.Combinatorics.Entropy
import qualified MAlonzo.Code.DASHI.Geometry.FiniteSpeed
import qualified MAlonzo.Code.DASHI.Geometry.Isotropy
import qualified MAlonzo.Code.Ultrametric

-- DASHI.Physics.ClosureGlue.ClosureAxioms
d_ClosureAxioms_6 = ()
data T_ClosureAxioms_6
  = C_ClosureAxioms'46'constructor_153 MAlonzo.Code.Ultrametric.T_Ultrametric_6
                                       (AgdaAny -> AgdaAny)
                                       MAlonzo.Code.Contraction.T_StrictContraction_108
                                       MAlonzo.Code.DASHI.Combinatorics.Entropy.T_Involution_34
                                       MAlonzo.Code.DASHI.Geometry.Isotropy.T_Isotropy_62
                                       MAlonzo.Code.DASHI.Geometry.FiniteSpeed.T_FiniteSpeed_10
-- DASHI.Physics.ClosureGlue.ClosureAxioms.S
d_S_22 :: T_ClosureAxioms_6 -> ()
d_S_22 = erased
-- DASHI.Physics.ClosureGlue.ClosureAxioms.U
d_U_24 ::
  T_ClosureAxioms_6 -> MAlonzo.Code.Ultrametric.T_Ultrametric_6
d_U_24 v0
  = case coe v0 of
      C_ClosureAxioms'46'constructor_153 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureGlue.ClosureAxioms.T
d_T_26 :: T_ClosureAxioms_6 -> AgdaAny -> AgdaAny
d_T_26 v0
  = case coe v0 of
      C_ClosureAxioms'46'constructor_153 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureGlue.ClosureAxioms.sc
d_sc_28 ::
  T_ClosureAxioms_6 ->
  MAlonzo.Code.Contraction.T_StrictContraction_108
d_sc_28 v0
  = case coe v0 of
      C_ClosureAxioms'46'constructor_153 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureGlue.ClosureAxioms.inv
d_inv_30 ::
  T_ClosureAxioms_6 ->
  MAlonzo.Code.DASHI.Combinatorics.Entropy.T_Involution_34
d_inv_30 v0
  = case coe v0 of
      C_ClosureAxioms'46'constructor_153 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureGlue.ClosureAxioms.iso
d_iso_32 ::
  T_ClosureAxioms_6 ->
  MAlonzo.Code.DASHI.Geometry.Isotropy.T_Isotropy_62
d_iso_32 v0
  = case coe v0 of
      C_ClosureAxioms'46'constructor_153 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureGlue.ClosureAxioms.fs
d_fs_34 ::
  T_ClosureAxioms_6 ->
  MAlonzo.Code.DASHI.Geometry.FiniteSpeed.T_FiniteSpeed_10
d_fs_34 v0
  = case coe v0 of
      C_ClosureAxioms'46'constructor_153 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureGlue.fp
d_fp_38 :: T_ClosureAxioms_6 -> AgdaAny
d_fp_38 v0
  = coe MAlonzo.Code.Contraction.d_fp_128 (coe d_sc_28 (coe v0))
-- DASHI.Physics.ClosureGlue.T-fixes-fp
d_T'45'fixes'45'fp_44 ::
  T_ClosureAxioms_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'45'fixes'45'fp_44 = erased
-- DASHI.Physics.ClosureGlue.fixed→fp
d_fixed'8594'fp_52 ::
  T_ClosureAxioms_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fixed'8594'fp_52 = erased
-- DASHI.Physics.ClosureGlue.contractive≢
d_contractive'8802'_62 ::
  T_ClosureAxioms_6 ->
  MAlonzo.Code.Contraction.T_Contractive'8802'_62
d_contractive'8802'_62 v0
  = coe
      MAlonzo.Code.Contraction.d_contractive'8802'_126
      (coe d_sc_28 (coe v0))
-- DASHI.Physics.ClosureGlue.iso-commutes
d_iso'45'commutes_72 ::
  T_ClosureAxioms_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iso'45'commutes_72 = erased
-- DASHI.Physics.ClosureGlue.preserves-locality
d_preserves'45'locality_86 ::
  T_ClosureAxioms_6 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_preserves'45'locality_86 v0 v1 v2 v3
  = coe
      MAlonzo.Code.DASHI.Geometry.FiniteSpeed.d_preservesLocality_30
      (d_fs_34 (coe v0)) v1 v2 v3
-- DASHI.Physics.ClosureGlue.defaultIso
d_defaultIso_102 ::
  () ->
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.DASHI.Geometry.Isotropy.T_Isotropy_62
d_defaultIso_102 ~v0 ~v1 ~v2 = du_defaultIso_102
du_defaultIso_102 ::
  MAlonzo.Code.DASHI.Geometry.Isotropy.T_Isotropy_62
du_defaultIso_102
  = coe MAlonzo.Code.DASHI.Geometry.Isotropy.du_trivialIsotropy_136
-- DASHI.Physics.ClosureGlue.defaultFS
d_defaultFS_112 ::
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.DASHI.Geometry.FiniteSpeed.T_FiniteSpeed_10
d_defaultFS_112 ~v0 ~v1 = du_defaultFS_112
du_defaultFS_112 ::
  MAlonzo.Code.DASHI.Geometry.FiniteSpeed.T_FiniteSpeed_10
du_defaultFS_112
  = coe
      MAlonzo.Code.DASHI.Geometry.FiniteSpeed.du_trivialFiniteSpeed_36
-- DASHI.Physics.ClosureGlue.mkDefaultClosure
d_mkDefaultClosure_126 ::
  () ->
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Contraction.T_StrictContraction_108 ->
  MAlonzo.Code.DASHI.Combinatorics.Entropy.T_Involution_34 ->
  T_ClosureAxioms_6
d_mkDefaultClosure_126 ~v0 v1 v2 v3 v4
  = du_mkDefaultClosure_126 v1 v2 v3 v4
du_mkDefaultClosure_126 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Contraction.T_StrictContraction_108 ->
  MAlonzo.Code.DASHI.Combinatorics.Entropy.T_Involution_34 ->
  T_ClosureAxioms_6
du_mkDefaultClosure_126 v0 v1 v2 v3
  = coe
      C_ClosureAxioms'46'constructor_153 v0 v1 v2 v3
      (coe du_defaultIso_102) (coe du_defaultFS_112)

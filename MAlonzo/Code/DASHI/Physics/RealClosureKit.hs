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

module MAlonzo.Code.DASHI.Physics.RealClosureKit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Contraction
import qualified MAlonzo.Code.DASHI.Combinatorics.Entropy
import qualified MAlonzo.Code.DASHI.Geometry.RealFiniteSpeed.Core
import qualified MAlonzo.Code.DASHI.Geometry.RealIsotropy.Core
import qualified MAlonzo.Code.DASHI.Geometry.StrictContractionComposition
import qualified MAlonzo.Code.DASHI.Physics.ClosureBuilder
import qualified MAlonzo.Code.DASHI.Physics.ClosureGlue
import qualified MAlonzo.Code.Ultrametric

-- DASHI.Physics.RealClosureKit.RealClosureKit
d_RealClosureKit_6 = ()
data T_RealClosureKit_6
  = C_RealClosureKit'46'constructor_1559 MAlonzo.Code.Ultrametric.T_Ultrametric_6
                                         (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                         (AgdaAny -> AgdaAny)
                                         MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
                                         MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
                                         MAlonzo.Code.Contraction.T_Contractive'8802'_62
                                         MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_OrderLaws_88
                                         AgdaAny
                                         MAlonzo.Code.DASHI.Combinatorics.Entropy.T_Involution_34
                                         MAlonzo.Code.DASHI.Geometry.RealIsotropy.Core.T_RealIsotropy_14
                                         MAlonzo.Code.DASHI.Geometry.RealFiniteSpeed.Core.T_RealFiniteSpeed_12
-- DASHI.Physics.RealClosureKit.RealClosureKit.S
d_S_42 :: T_RealClosureKit_6 -> ()
d_S_42 = erased
-- DASHI.Physics.RealClosureKit.RealClosureKit.U
d_U_44 ::
  T_RealClosureKit_6 -> MAlonzo.Code.Ultrametric.T_Ultrametric_6
d_U_44 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.C
d_C_46 :: T_RealClosureKit_6 -> AgdaAny -> AgdaAny
d_C_46 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.P
d_P_48 :: T_RealClosureKit_6 -> AgdaAny -> AgdaAny
d_P_48 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.R
d_R_50 :: T_RealClosureKit_6 -> AgdaAny -> AgdaAny
d_R_50 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.nonexpC
d_nonexpC_52 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
d_nonexpC_52 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.nonexpR
d_nonexpR_54 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
d_nonexpR_54 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.strictP
d_strictP_56 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.Contraction.T_Contractive'8802'_62
d_strictP_56 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.orderLaws
d_orderLaws_58 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_OrderLaws_88
d_orderLaws_58 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.pres≢R
d_pres'8802'R_60 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_DistinctPreserving_70
d_pres'8802'R_60 = erased
-- DASHI.Physics.RealClosureKit.RealClosureKit.fp
d_fp_62 :: T_RealClosureKit_6 -> AgdaAny
d_fp_62 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.fixedT
d_fixedT_64 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fixedT_64 = erased
-- DASHI.Physics.RealClosureKit.RealClosureKit.uniqueT
d_uniqueT_68 ::
  T_RealClosureKit_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uniqueT_68 = erased
-- DASHI.Physics.RealClosureKit.RealClosureKit.inv
d_inv_70 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.DASHI.Combinatorics.Entropy.T_Involution_34
d_inv_70 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.iso
d_iso_72 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.DASHI.Geometry.RealIsotropy.Core.T_RealIsotropy_14
d_iso_72 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.RealClosureKit.fs
d_fs_74 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.DASHI.Geometry.RealFiniteSpeed.Core.T_RealFiniteSpeed_12
d_fs_74 v0
  = case coe v0 of
      C_RealClosureKit'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.RealClosureKit.toRealStack
d_toRealStack_76 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.DASHI.Physics.ClosureBuilder.T_RealStack_6
d_toRealStack_76 v0
  = coe
      MAlonzo.Code.DASHI.Physics.ClosureBuilder.C_RealStack'46'constructor_1559
      (d_U_44 (coe v0)) (d_C_46 (coe v0)) (d_P_48 (coe v0))
      (d_R_50 (coe v0)) (d_nonexpC_52 (coe v0)) (d_nonexpR_54 (coe v0))
      (d_strictP_56 (coe v0)) (d_orderLaws_58 (coe v0))
      (d_fp_62 (coe v0)) (d_inv_70 (coe v0)) (d_iso_72 (coe v0))
      (d_fs_74 (coe v0))
-- DASHI.Physics.RealClosureKit.closureAxioms
d_closureAxioms_82 ::
  T_RealClosureKit_6 ->
  MAlonzo.Code.DASHI.Physics.ClosureGlue.T_ClosureAxioms_6
d_closureAxioms_82 v0
  = coe
      MAlonzo.Code.DASHI.Physics.ClosureBuilder.d_buildClosure_102
      (coe d_toRealStack_76 (coe v0))

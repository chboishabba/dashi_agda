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

module MAlonzo.Code.DASHI.Physics.ClosureBuilder where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Contraction
import qualified MAlonzo.Code.DASHI.Combinatorics.Entropy
import qualified MAlonzo.Code.DASHI.Geometry.FiniteSpeed
import qualified MAlonzo.Code.DASHI.Geometry.RealFiniteSpeed.Core
import qualified MAlonzo.Code.DASHI.Geometry.RealIsotropy.Core
import qualified MAlonzo.Code.DASHI.Geometry.StrictContractionComposition
import qualified MAlonzo.Code.DASHI.Physics.ClosureGlue
import qualified MAlonzo.Code.DASHI.Physics.TOperator
import qualified MAlonzo.Code.Ultrametric

-- DASHI.Physics.ClosureBuilder.RealStack
d_RealStack_6 = ()
data T_RealStack_6
  = C_RealStack'46'constructor_1559 MAlonzo.Code.Ultrametric.T_Ultrametric_6
                                    (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                    MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
                                    MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
                                    MAlonzo.Code.Contraction.T_Contractive'8802'_62
                                    MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_OrderLaws_88
                                    AgdaAny MAlonzo.Code.DASHI.Combinatorics.Entropy.T_Involution_34
                                    MAlonzo.Code.DASHI.Geometry.RealIsotropy.Core.T_RealIsotropy_14
                                    MAlonzo.Code.DASHI.Geometry.RealFiniteSpeed.Core.T_RealFiniteSpeed_12
-- DASHI.Physics.ClosureBuilder.RealStack.S
d_S_42 :: T_RealStack_6 -> ()
d_S_42 = erased
-- DASHI.Physics.ClosureBuilder.RealStack.U
d_U_44 :: T_RealStack_6 -> MAlonzo.Code.Ultrametric.T_Ultrametric_6
d_U_44 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.C
d_C_46 :: T_RealStack_6 -> AgdaAny -> AgdaAny
d_C_46 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.P
d_P_48 :: T_RealStack_6 -> AgdaAny -> AgdaAny
d_P_48 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.R
d_R_50 :: T_RealStack_6 -> AgdaAny -> AgdaAny
d_R_50 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.nonexpC
d_nonexpC_52 ::
  T_RealStack_6 ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
d_nonexpC_52 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.nonexpR
d_nonexpR_54 ::
  T_RealStack_6 ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
d_nonexpR_54 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.strictP
d_strictP_56 ::
  T_RealStack_6 -> MAlonzo.Code.Contraction.T_Contractive'8802'_62
d_strictP_56 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.orderLaws
d_orderLaws_58 ::
  T_RealStack_6 ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_OrderLaws_88
d_orderLaws_58 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.pres≢R
d_pres'8802'R_60 ::
  T_RealStack_6 ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_DistinctPreserving_70
d_pres'8802'R_60 = erased
-- DASHI.Physics.ClosureBuilder.RealStack.fp0
d_fp0_62 :: T_RealStack_6 -> AgdaAny
d_fp0_62 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.fixedT
d_fixedT_64 ::
  T_RealStack_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fixedT_64 = erased
-- DASHI.Physics.ClosureBuilder.RealStack.uniqueT
d_uniqueT_68 ::
  T_RealStack_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uniqueT_68 = erased
-- DASHI.Physics.ClosureBuilder.RealStack.inv
d_inv_70 ::
  T_RealStack_6 ->
  MAlonzo.Code.DASHI.Combinatorics.Entropy.T_Involution_34
d_inv_70 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.iso
d_iso_72 ::
  T_RealStack_6 ->
  MAlonzo.Code.DASHI.Geometry.RealIsotropy.Core.T_RealIsotropy_14
d_iso_72 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.RealStack.fs
d_fs_74 ::
  T_RealStack_6 ->
  MAlonzo.Code.DASHI.Geometry.RealFiniteSpeed.Core.T_RealFiniteSpeed_12
d_fs_74 v0
  = case coe v0 of
      C_RealStack'46'constructor_1559 v2 v3 v4 v5 v6 v7 v8 v9 v11 v14 v15 v16
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ClosureBuilder.mkOp
d_mkOp_78 ::
  T_RealStack_6 ->
  MAlonzo.Code.DASHI.Physics.TOperator.T_TOperator_22
d_mkOp_78 v0
  = coe
      MAlonzo.Code.DASHI.Physics.TOperator.C_TOperator'46'constructor_197
      (coe d_C_46 (coe v0)) (coe d_P_48 (coe v0)) (coe d_R_50 (coe v0))
-- DASHI.Physics.ClosureBuilder.T
d_T_84 :: T_RealStack_6 -> AgdaAny -> AgdaAny
d_T_84 v0
  = coe
      MAlonzo.Code.DASHI.Physics.TOperator.du_T_38
      (coe d_mkOp_78 (coe v0))
-- DASHI.Physics.ClosureBuilder.contractiveT
d_contractiveT_90 ::
  T_RealStack_6 -> MAlonzo.Code.Contraction.T_Contractive'8802'_62
d_contractiveT_90 v0
  = coe
      MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.du_composeStrict_148
      (coe d_U_44 (coe v0)) (coe d_C_46 (coe v0)) (coe d_R_50 (coe v0))
      (coe d_P_48 (coe v0)) (coe d_orderLaws_58 (coe v0))
      (coe d_nonexpC_52 (coe v0)) (coe d_nonexpR_54 (coe v0))
      (coe d_strictP_56 (coe v0))
-- DASHI.Physics.ClosureBuilder.strictT
d_strictT_96 ::
  T_RealStack_6 -> MAlonzo.Code.Contraction.T_StrictContraction_108
d_strictT_96 v0
  = coe
      MAlonzo.Code.Contraction.C_StrictContraction'46'constructor_1559
      (d_contractiveT_90 (coe v0)) (d_fp0_62 (coe v0))
-- DASHI.Physics.ClosureBuilder.buildClosure
d_buildClosure_102 ::
  T_RealStack_6 ->
  MAlonzo.Code.DASHI.Physics.ClosureGlue.T_ClosureAxioms_6
d_buildClosure_102 v0
  = coe
      MAlonzo.Code.DASHI.Physics.ClosureGlue.C_ClosureAxioms'46'constructor_153
      (d_U_44 (coe v0)) (d_T_84 (coe v0)) (d_strictT_96 (coe v0))
      (d_inv_70 (coe v0))
      (MAlonzo.Code.DASHI.Geometry.RealIsotropy.Core.d_iso_26
         (coe d_iso_72 (coe v0)))
      (coe
         MAlonzo.Code.DASHI.Geometry.FiniteSpeed.C_FiniteSpeed'46'constructor_107
         (MAlonzo.Code.DASHI.Geometry.RealFiniteSpeed.Core.d_preservesLocality_32
            (coe d_fs_74 (coe v0))))

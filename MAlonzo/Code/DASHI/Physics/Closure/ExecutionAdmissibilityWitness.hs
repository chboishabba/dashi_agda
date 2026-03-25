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

module MAlonzo.Code.DASHI.Physics.Closure.ExecutionAdmissibilityWitness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base

-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.StepClass
d_StepClass_8 = ()
data T_StepClass_8
  = C_Interior_10 | C_ArrowBoundary_12 | C_StructuralBoundary_14 |
    C_Outside_16
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.FamilyClass
d_FamilyClass_18 = ()
data T_FamilyClass_18
  = C_InteriorFamily_20 | C_ArrowLadderFamily_22 |
    C_SingleArrowBreakFamily_24 | C_MDLTailBoundaryFamily_26
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.ExecutionAdmissibilityWitness
d_ExecutionAdmissibilityWitness_30 a0 = ()
data T_ExecutionAdmissibilityWitness_30
  = C_ExecutionAdmissibilityWitness'46'constructor_867 (AgdaAny ->
                                                        T_StepClass_8)
                                                       (AgdaAny ->
                                                        MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.ExecutionAdmissibilityWitness.stepClass
d_stepClass_54 ::
  T_ExecutionAdmissibilityWitness_30 -> AgdaAny -> T_StepClass_8
d_stepClass_54 v0
  = case coe v0 of
      C_ExecutionAdmissibilityWitness'46'constructor_867 v1 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.ExecutionAdmissibilityWitness.coneOK
d_coneOK_56 :: T_ExecutionAdmissibilityWitness_30 -> AgdaAny -> ()
d_coneOK_56 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.ExecutionAdmissibilityWitness.arrowOK
d_arrowOK_58 :: T_ExecutionAdmissibilityWitness_30 -> AgdaAny -> ()
d_arrowOK_58 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.ExecutionAdmissibilityWitness.mdlOK
d_mdlOK_60 :: T_ExecutionAdmissibilityWitness_30 -> AgdaAny -> ()
d_mdlOK_60 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.ExecutionAdmissibilityWitness.basinOK
d_basinOK_62 :: T_ExecutionAdmissibilityWitness_30 -> AgdaAny -> ()
d_basinOK_62 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.ExecutionAdmissibilityWitness.eigenOK
d_eigenOK_64 :: T_ExecutionAdmissibilityWitness_30 -> AgdaAny -> ()
d_eigenOK_64 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.ExecutionAdmissibilityWitness.interiorOrBoundary
d_interiorOrBoundary_68 ::
  T_ExecutionAdmissibilityWitness_30 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_interiorOrBoundary_68 v0
  = case coe v0 of
      C_ExecutionAdmissibilityWitness'46'constructor_867 v1 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.ExecutionAdmissibilityWitness.noStructuralEscape
d_noStructuralEscape_72 ::
  T_ExecutionAdmissibilityWitness_30 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noStructuralEscape_72 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.FamilyClassificationWitness
d_FamilyClassificationWitness_76 a0 = ()
newtype T_FamilyClassificationWitness_76
  = C_FamilyClassificationWitness'46'constructor_1145 (AgdaAny ->
                                                       T_FamilyClass_18)
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.FamilyClassificationWitness.familyClass
d_familyClass_92 ::
  T_FamilyClassificationWitness_76 -> AgdaAny -> T_FamilyClass_18
d_familyClass_92 v0
  = case coe v0 of
      C_FamilyClassificationWitness'46'constructor_1145 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.FamilyClassificationWitness.coneOK
d_coneOK_94 :: T_FamilyClassificationWitness_76 -> AgdaAny -> ()
d_coneOK_94 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.FamilyClassificationWitness.fejerOK
d_fejerOK_96 :: T_FamilyClassificationWitness_76 -> AgdaAny -> ()
d_fejerOK_96 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.FamilyClassificationWitness.closestOK
d_closestOK_98 :: T_FamilyClassificationWitness_76 -> AgdaAny -> ()
d_closestOK_98 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.FamilyClassificationWitness.mdlExactOK
d_mdlExactOK_100 ::
  T_FamilyClassificationWitness_76 -> AgdaAny -> ()
d_mdlExactOK_100 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.FamilyClassificationWitness.tailLocalized
d_tailLocalized_102 ::
  T_FamilyClassificationWitness_76 -> AgdaAny -> ()
d_tailLocalized_102 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.SomeExecutionAdmissibilityWitness
d_SomeExecutionAdmissibilityWitness_104 = ()
newtype T_SomeExecutionAdmissibilityWitness_104
  = C_SomeExecutionAdmissibilityWitness'46'constructor_1295 T_ExecutionAdmissibilityWitness_30
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.SomeExecutionAdmissibilityWitness.StepId
d_StepId_110 :: T_SomeExecutionAdmissibilityWitness_104 -> ()
d_StepId_110 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.SomeExecutionAdmissibilityWitness.witness
d_witness_112 ::
  T_SomeExecutionAdmissibilityWitness_104 ->
  T_ExecutionAdmissibilityWitness_30
d_witness_112 v0
  = case coe v0 of
      C_SomeExecutionAdmissibilityWitness'46'constructor_1295 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.SomeFamilyClassificationWitness
d_SomeFamilyClassificationWitness_114 = ()
newtype T_SomeFamilyClassificationWitness_114
  = C_SomeFamilyClassificationWitness'46'constructor_1323 T_FamilyClassificationWitness_76
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.SomeFamilyClassificationWitness.FamilyId
d_FamilyId_120 :: T_SomeFamilyClassificationWitness_114 -> ()
d_FamilyId_120 = erased
-- DASHI.Physics.Closure.ExecutionAdmissibilityWitness.SomeFamilyClassificationWitness.witness
d_witness_122 ::
  T_SomeFamilyClassificationWitness_114 ->
  T_FamilyClassificationWitness_76
d_witness_122 v0
  = case coe v0 of
      C_SomeFamilyClassificationWitness'46'constructor_1323 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError

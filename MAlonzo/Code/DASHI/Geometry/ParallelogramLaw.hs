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

module MAlonzo.Code.DASHI.Geometry.ParallelogramLaw where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality

-- DASHI.Geometry.ParallelogramLaw.AdditiveSpace
d_AdditiveSpace_6 = ()
data T_AdditiveSpace_6
  = C_AdditiveSpace'46'constructor_23 (AgdaAny -> AgdaAny -> AgdaAny)
                                      (AgdaAny -> AgdaAny) AgdaAny
-- DASHI.Geometry.ParallelogramLaw.AdditiveSpace.V
d_V_16 :: T_AdditiveSpace_6 -> ()
d_V_16 = erased
-- DASHI.Geometry.ParallelogramLaw.AdditiveSpace._+_
d__'43'__18 :: T_AdditiveSpace_6 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__18 v0
  = case coe v0 of
      C_AdditiveSpace'46'constructor_23 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ParallelogramLaw.AdditiveSpace.-_
d_'45'__20 :: T_AdditiveSpace_6 -> AgdaAny -> AgdaAny
d_'45'__20 v0
  = case coe v0 of
      C_AdditiveSpace'46'constructor_23 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ParallelogramLaw.AdditiveSpace.0#
d_0'35'_22 :: T_AdditiveSpace_6 -> AgdaAny
d_0'35'_22 v0
  = case coe v0 of
      C_AdditiveSpace'46'constructor_23 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ParallelogramLaw.Normed
d_Normed_26 a0 = ()
newtype T_Normed_26
  = C_Normed'46'constructor_97 (AgdaAny -> Integer)
-- DASHI.Geometry.ParallelogramLaw._._+_
d__'43'__32 :: T_AdditiveSpace_6 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__32 v0 = coe d__'43'__18 (coe v0)
-- DASHI.Geometry.ParallelogramLaw._.-_
d_'45'__34 :: T_AdditiveSpace_6 -> AgdaAny -> AgdaAny
d_'45'__34 v0 = coe d_'45'__20 (coe v0)
-- DASHI.Geometry.ParallelogramLaw._.0#
d_0'35'_36 :: T_AdditiveSpace_6 -> AgdaAny
d_0'35'_36 v0 = coe d_0'35'_22 (coe v0)
-- DASHI.Geometry.ParallelogramLaw._.V
d_V_38 :: T_AdditiveSpace_6 -> ()
d_V_38 = erased
-- DASHI.Geometry.ParallelogramLaw.Normed._._+_
d__'43'__44 ::
  T_AdditiveSpace_6 -> T_Normed_26 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__44 v0 ~v1 = du__'43'__44 v0
du__'43'__44 :: T_AdditiveSpace_6 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__44 v0 = coe d__'43'__18 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.Normed._.-_
d_'45'__46 ::
  T_AdditiveSpace_6 -> T_Normed_26 -> AgdaAny -> AgdaAny
d_'45'__46 v0 ~v1 = du_'45'__46 v0
du_'45'__46 :: T_AdditiveSpace_6 -> AgdaAny -> AgdaAny
du_'45'__46 v0 = coe d_'45'__20 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.Normed._.0#
d_0'35'_48 :: T_AdditiveSpace_6 -> T_Normed_26 -> AgdaAny
d_0'35'_48 v0 ~v1 = du_0'35'_48 v0
du_0'35'_48 :: T_AdditiveSpace_6 -> AgdaAny
du_0'35'_48 v0 = coe d_0'35'_22 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.Normed._.V
d_V_50 :: T_AdditiveSpace_6 -> T_Normed_26 -> ()
d_V_50 = erased
-- DASHI.Geometry.ParallelogramLaw.Normed.∥_∥²
d_'8741'_'8741''178'_52 :: T_Normed_26 -> AgdaAny -> Integer
d_'8741'_'8741''178'_52 v0
  = case coe v0 of
      C_Normed'46'constructor_97 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ParallelogramLaw.Parallelogram
d_Parallelogram_58 a0 a1 = ()
data T_Parallelogram_58 = C_Parallelogram'46'constructor_259
-- DASHI.Geometry.ParallelogramLaw._._+_
d__'43'__66 ::
  T_AdditiveSpace_6 -> T_Normed_26 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__66 v0 ~v1 = du__'43'__66 v0
du__'43'__66 :: T_AdditiveSpace_6 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__66 v0 = coe d__'43'__18 (coe v0)
-- DASHI.Geometry.ParallelogramLaw._.-_
d_'45'__68 ::
  T_AdditiveSpace_6 -> T_Normed_26 -> AgdaAny -> AgdaAny
d_'45'__68 v0 ~v1 = du_'45'__68 v0
du_'45'__68 :: T_AdditiveSpace_6 -> AgdaAny -> AgdaAny
du_'45'__68 v0 = coe d_'45'__20 (coe v0)
-- DASHI.Geometry.ParallelogramLaw._.0#
d_0'35'_70 :: T_AdditiveSpace_6 -> T_Normed_26 -> AgdaAny
d_0'35'_70 v0 ~v1 = du_0'35'_70 v0
du_0'35'_70 :: T_AdditiveSpace_6 -> AgdaAny
du_0'35'_70 v0 = coe d_0'35'_22 (coe v0)
-- DASHI.Geometry.ParallelogramLaw._.V
d_V_72 :: T_AdditiveSpace_6 -> T_Normed_26 -> ()
d_V_72 = erased
-- DASHI.Geometry.ParallelogramLaw._.∥_∥²
d_'8741'_'8741''178'_76 :: T_Normed_26 -> AgdaAny -> Integer
d_'8741'_'8741''178'_76 v0 = coe d_'8741'_'8741''178'_52 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.Parallelogram._._+_
d__'43'__82 ::
  T_AdditiveSpace_6 ->
  T_Normed_26 -> T_Parallelogram_58 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__82 v0 ~v1 ~v2 = du__'43'__82 v0
du__'43'__82 :: T_AdditiveSpace_6 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__82 v0 = coe d__'43'__18 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.Parallelogram._.-_
d_'45'__84 ::
  T_AdditiveSpace_6 ->
  T_Normed_26 -> T_Parallelogram_58 -> AgdaAny -> AgdaAny
d_'45'__84 v0 ~v1 ~v2 = du_'45'__84 v0
du_'45'__84 :: T_AdditiveSpace_6 -> AgdaAny -> AgdaAny
du_'45'__84 v0 = coe d_'45'__20 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.Parallelogram._.0#
d_0'35'_86 ::
  T_AdditiveSpace_6 -> T_Normed_26 -> T_Parallelogram_58 -> AgdaAny
d_0'35'_86 v0 ~v1 ~v2 = du_0'35'_86 v0
du_0'35'_86 :: T_AdditiveSpace_6 -> AgdaAny
du_0'35'_86 v0 = coe d_0'35'_22 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.Parallelogram._.V
d_V_88 ::
  T_AdditiveSpace_6 -> T_Normed_26 -> T_Parallelogram_58 -> ()
d_V_88 = erased
-- DASHI.Geometry.ParallelogramLaw.Parallelogram._.∥_∥²
d_'8741'_'8741''178'_92 ::
  T_Normed_26 -> T_Parallelogram_58 -> AgdaAny -> Integer
d_'8741'_'8741''178'_92 v0 ~v1 = du_'8741'_'8741''178'_92 v0
du_'8741'_'8741''178'_92 :: T_Normed_26 -> AgdaAny -> Integer
du_'8741'_'8741''178'_92 v0 = coe d_'8741'_'8741''178'_52 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.Parallelogram.paral
d_paral_94 :: T_Parallelogram_58 -> ()
d_paral_94 = erased
-- DASHI.Geometry.ParallelogramLaw.AddCommMonoid
d_AddCommMonoid_98 a0 = ()
data T_AddCommMonoid_98
  = C_AddCommMonoid'46'constructor_1005 (AgdaAny ->
                                         AgdaAny -> AgdaAny)
                                        AgdaAny
-- DASHI.Geometry.ParallelogramLaw.AddCommMonoid._+_
d__'43'__124 :: T_AddCommMonoid_98 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__124 v0
  = case coe v0 of
      C_AddCommMonoid'46'constructor_1005 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ParallelogramLaw.AddCommMonoid.0#
d_0'35'_126 :: T_AddCommMonoid_98 -> AgdaAny
d_0'35'_126 v0
  = case coe v0 of
      C_AddCommMonoid'46'constructor_1005 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ParallelogramLaw.AddCommMonoid.+-assoc
d_'43''45'assoc_134 ::
  T_AddCommMonoid_98 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_134 = erased
-- DASHI.Geometry.ParallelogramLaw.AddCommMonoid.+-comm
d_'43''45'comm_140 ::
  T_AddCommMonoid_98 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_140 = erased
-- DASHI.Geometry.ParallelogramLaw.AddCommMonoid.+-id
d_'43''45'id_144 ::
  T_AddCommMonoid_98 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'id_144 = erased
-- DASHI.Geometry.ParallelogramLaw.HasNeg
d_HasNeg_148 a0 = ()
data T_HasNeg_148
  = C_HasNeg'46'constructor_1307 (AgdaAny -> AgdaAny)
                                 (AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Geometry.ParallelogramLaw.HasNeg.-_
d_'45'__162 :: T_HasNeg_148 -> AgdaAny -> AgdaAny
d_'45'__162 v0
  = case coe v0 of
      C_HasNeg'46'constructor_1307 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ParallelogramLaw.HasNeg.sub
d_sub_164 :: T_HasNeg_148 -> AgdaAny -> AgdaAny -> AgdaAny
d_sub_164 v0
  = case coe v0 of
      C_HasNeg'46'constructor_1307 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ParallelogramLaw.HasNeg.subdef
d_subdef_170 ::
  T_HasNeg_148 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subdef_170 = erased
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy
d_ParallelogramEnergy_178 a0 a1 a2 = ()
newtype T_ParallelogramEnergy_178
  = C_ParallelogramEnergy'46'constructor_1755 (AgdaAny ->
                                               AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Geometry.ParallelogramLaw._._+_
d__'43'__188 ::
  T_AddCommMonoid_98 -> T_HasNeg_148 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__188 v0 ~v1 = du__'43'__188 v0
du__'43'__188 ::
  T_AddCommMonoid_98 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__188 v0 = coe d__'43'__124 (coe v0)
-- DASHI.Geometry.ParallelogramLaw._.+-assoc
d_'43''45'assoc_190 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_190 = erased
-- DASHI.Geometry.ParallelogramLaw._.+-comm
d_'43''45'comm_192 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_192 = erased
-- DASHI.Geometry.ParallelogramLaw._.+-id
d_'43''45'id_194 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'id_194 = erased
-- DASHI.Geometry.ParallelogramLaw._.0#
d_0'35'_196 :: T_AddCommMonoid_98 -> T_HasNeg_148 -> AgdaAny
d_0'35'_196 v0 ~v1 = du_0'35'_196 v0
du_0'35'_196 :: T_AddCommMonoid_98 -> AgdaAny
du_0'35'_196 v0 = coe d_0'35'_126 (coe v0)
-- DASHI.Geometry.ParallelogramLaw._.-_
d_'45'__200 :: T_HasNeg_148 -> AgdaAny -> AgdaAny
d_'45'__200 v0 = coe d_'45'__162 (coe v0)
-- DASHI.Geometry.ParallelogramLaw._.sub
d_sub_202 :: T_HasNeg_148 -> AgdaAny -> AgdaAny -> AgdaAny
d_sub_202 v0 = coe d_sub_164 (coe v0)
-- DASHI.Geometry.ParallelogramLaw._.subdef
d_subdef_204 ::
  T_HasNeg_148 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subdef_204 = erased
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy._._+_
d__'43'__216 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 ->
  T_ParallelogramEnergy_178 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__216 v0 ~v1 ~v2 = du__'43'__216 v0
du__'43'__216 ::
  T_AddCommMonoid_98 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__216 v0 = coe d__'43'__124 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy._.+-assoc
d_'43''45'assoc_218 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 ->
  T_ParallelogramEnergy_178 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_218 = erased
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy._.+-comm
d_'43''45'comm_220 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 ->
  T_ParallelogramEnergy_178 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_220 = erased
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy._.+-id
d_'43''45'id_222 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 ->
  T_ParallelogramEnergy_178 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'id_222 = erased
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy._.0#
d_0'35'_224 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 -> T_ParallelogramEnergy_178 -> AgdaAny
d_0'35'_224 v0 ~v1 ~v2 = du_0'35'_224 v0
du_0'35'_224 :: T_AddCommMonoid_98 -> AgdaAny
du_0'35'_224 v0 = coe d_0'35'_126 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy._.-_
d_'45'__228 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 -> T_ParallelogramEnergy_178 -> AgdaAny -> AgdaAny
d_'45'__228 ~v0 v1 ~v2 = du_'45'__228 v1
du_'45'__228 :: T_HasNeg_148 -> AgdaAny -> AgdaAny
du_'45'__228 v0 = coe d_'45'__162 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy._.sub
d_sub_230 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 ->
  T_ParallelogramEnergy_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_sub_230 ~v0 v1 ~v2 = du_sub_230 v1
du_sub_230 :: T_HasNeg_148 -> AgdaAny -> AgdaAny -> AgdaAny
du_sub_230 v0 = coe d_sub_164 (coe v0)
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy._.subdef
d_subdef_232 ::
  T_AddCommMonoid_98 ->
  T_HasNeg_148 ->
  T_ParallelogramEnergy_178 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subdef_232 = erased
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy.E
d_E_234 :: T_ParallelogramEnergy_178 -> AgdaAny -> ()
d_E_234 = erased
-- DASHI.Geometry.ParallelogramLaw.ParallelogramEnergy.parallelogram
d_parallelogram_240 ::
  T_ParallelogramEnergy_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_parallelogram_240 v0
  = case coe v0 of
      C_ParallelogramEnergy'46'constructor_1755 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError

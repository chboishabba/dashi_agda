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

module MAlonzo.Code.DASHI.Physics.Closure.ContractionDiffusionPair where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive

-- DASHI.Physics.Closure.ContractionDiffusionPair.ContractionDiffusionPair
d_ContractionDiffusionPair_12 a0 a1 = ()
data T_ContractionDiffusionPair_12
  = C_ContractionDiffusionPair'46'constructor_23 (AgdaAny -> AgdaAny)
                                                 (AgdaAny -> AgdaAny)
-- DASHI.Physics.Closure.ContractionDiffusionPair.ContractionDiffusionPair.K
d_K_22 :: T_ContractionDiffusionPair_12 -> AgdaAny -> AgdaAny
d_K_22 v0
  = case coe v0 of
      C_ContractionDiffusionPair'46'constructor_23 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionDiffusionPair.ContractionDiffusionPair.D
d_D_24 :: T_ContractionDiffusionPair_12 -> AgdaAny -> AgdaAny
d_D_24 v0
  = case coe v0 of
      C_ContractionDiffusionPair'46'constructor_23 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionDiffusionPair.ContractionDiffusionPair.updateKD
d_updateKD_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_ContractionDiffusionPair_12 -> AgdaAny -> AgdaAny
d_updateKD_26 ~v0 ~v1 v2 v3 = du_updateKD_26 v2 v3
du_updateKD_26 ::
  T_ContractionDiffusionPair_12 -> AgdaAny -> AgdaAny
du_updateKD_26 v0 v1 = coe d_K_22 v0 (coe d_D_24 v0 v1)
-- DASHI.Physics.Closure.ContractionDiffusionPair.ContractionDiffusionPair.updateDK
d_updateDK_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_ContractionDiffusionPair_12 -> AgdaAny -> AgdaAny
d_updateDK_30 ~v0 ~v1 v2 v3 = du_updateDK_30 v2 v3
du_updateDK_30 ::
  T_ContractionDiffusionPair_12 -> AgdaAny -> AgdaAny
du_updateDK_30 v0 v1 = coe d_D_24 v0 (coe d_K_22 v0 v1)
-- DASHI.Physics.Closure.ContractionDiffusionPair.ContractionDiffusionPair.updateKD-law
d_updateKD'45'law_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_ContractionDiffusionPair_12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_updateKD'45'law_36 = erased
-- DASHI.Physics.Closure.ContractionDiffusionPair.ContractionDiffusionPair.updateDK-law
d_updateDK'45'law_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_ContractionDiffusionPair_12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_updateDK'45'law_40 = erased
-- DASHI.Physics.Closure.ContractionDiffusionPair.ContractionDiffusionPair.upToNormalization
d_upToNormalization_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_ContractionDiffusionPair_12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_upToNormalization_42 ~v0 ~v1 ~v2 = du_upToNormalization_42
du_upToNormalization_42 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_upToNormalization_42 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- DASHI.Physics.Closure.ContractionDiffusionPair.mkContractionDiffusionPair
d_mkContractionDiffusionPair_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_ContractionDiffusionPair_12
d_mkContractionDiffusionPair_52 ~v0 ~v1 v2 v3
  = du_mkContractionDiffusionPair_52 v2 v3
du_mkContractionDiffusionPair_52 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_ContractionDiffusionPair_12
du_mkContractionDiffusionPair_52 v0 v1
  = coe
      C_ContractionDiffusionPair'46'constructor_23 (coe v0) (coe v1)

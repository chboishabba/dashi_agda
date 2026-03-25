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

module MAlonzo.Code.DASHI.Physics.TOperator where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Combinatorics.Entropy

-- DASHI.Physics.TOperator._∘_
d__'8728'__12 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'8728'__12 ~v0 ~v1 ~v2 v3 v4 v5 = du__'8728'__12 v3 v4 v5
du__'8728'__12 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'8728'__12 v0 v1 v2 = coe v0 (coe v1 v2)
-- DASHI.Physics.TOperator.TOperator
d_TOperator_22 a0 = ()
data T_TOperator_22
  = C_TOperator'46'constructor_197 (AgdaAny -> AgdaAny)
                                   (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- DASHI.Physics.TOperator.TOperator.C
d_C_32 :: T_TOperator_22 -> AgdaAny -> AgdaAny
d_C_32 v0
  = case coe v0 of
      C_TOperator'46'constructor_197 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.TOperator.TOperator.P
d_P_34 :: T_TOperator_22 -> AgdaAny -> AgdaAny
d_P_34 v0
  = case coe v0 of
      C_TOperator'46'constructor_197 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.TOperator.TOperator.R
d_R_36 :: T_TOperator_22 -> AgdaAny -> AgdaAny
d_R_36 v0
  = case coe v0 of
      C_TOperator'46'constructor_197 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.TOperator.TOperator.T
d_T_38 :: () -> T_TOperator_22 -> AgdaAny -> AgdaAny
d_T_38 ~v0 v1 = du_T_38 v1
du_T_38 :: T_TOperator_22 -> AgdaAny -> AgdaAny
du_T_38 v0
  = coe
      du__'8728'__12 (coe d_C_32 (coe v0))
      (coe du__'8728'__12 (coe d_P_34 (coe v0)) (coe d_R_36 (coe v0)))
-- DASHI.Physics.TOperator.TEquivariant
d_TEquivariant_46 a0 a1 a2 = ()
data T_TEquivariant_46 = C_TEquivariant'46'constructor_611
-- DASHI.Physics.TOperator.TEquivariant.involutionCommutes
d_involutionCommutes_60 ::
  T_TEquivariant_46 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_involutionCommutes_60 = erased

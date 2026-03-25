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

module MAlonzo.Code.DASHI.Physics.UniversalityTheorem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality

-- DASHI.Physics.UniversalityTheorem.Universality
d_Universality_10 a0 a1 = ()
data T_Universality_10
  = C_Universality'46'constructor_711 (AgdaAny -> AgdaAny)
                                      (() ->
                                       (AgdaAny -> AgdaAny) ->
                                       (AgdaAny ->
                                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
                                       AgdaAny -> AgdaAny)
-- DASHI.Physics.UniversalityTheorem.Universality.Q
d_Q_40 :: T_Universality_10 -> ()
d_Q_40 = erased
-- DASHI.Physics.UniversalityTheorem.Universality.π
d_π_42 :: T_Universality_10 -> AgdaAny -> AgdaAny
d_π_42 v0
  = case coe v0 of
      C_Universality'46'constructor_711 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.UniversalityTheorem.Universality.lift
d_lift_50 ::
  T_Universality_10 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_lift_50 v0
  = case coe v0 of
      C_Universality'46'constructor_711 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.UniversalityTheorem.Universality.fac
d_fac_62 ::
  T_Universality_10 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fac_62 = erased
-- DASHI.Physics.UniversalityTheorem.canonicalUniversality
d_canonicalUniversality_68 ::
  () -> (AgdaAny -> AgdaAny) -> T_Universality_10
d_canonicalUniversality_68 ~v0 v1 = du_canonicalUniversality_68 v1
du_canonicalUniversality_68 ::
  (AgdaAny -> AgdaAny) -> T_Universality_10
du_canonicalUniversality_68 v0
  = coe C_Universality'46'constructor_711 v0 (\ v1 v2 v3 -> v2)

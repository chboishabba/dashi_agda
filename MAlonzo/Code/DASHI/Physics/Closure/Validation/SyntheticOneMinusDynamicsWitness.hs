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

module MAlonzo.Code.DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String

-- DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness.SyntheticOneMinusDynamicsWitness
d_SyntheticOneMinusDynamicsWitness_10 = ()
data T_SyntheticOneMinusDynamicsWitness_10
  = C_SyntheticOneMinusDynamicsWitness'46'constructor_187 MAlonzo.Code.Agda.Builtin.String.T_String_6
                                                          Integer
                                                          MAlonzo.Code.Agda.Builtin.String.T_String_6
-- DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness.SyntheticOneMinusDynamicsWitness.label
d_label_24 ::
  T_SyntheticOneMinusDynamicsWitness_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_label_24 v0
  = case coe v0 of
      C_SyntheticOneMinusDynamicsWitness'46'constructor_187 v1 v2 v3
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness.SyntheticOneMinusDynamicsWitness.stateCardinality
d_stateCardinality_26 ::
  T_SyntheticOneMinusDynamicsWitness_10 -> Integer
d_stateCardinality_26 v0
  = case coe v0 of
      C_SyntheticOneMinusDynamicsWitness'46'constructor_187 v1 v2 v3
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness.SyntheticOneMinusDynamicsWitness.updateLaw
d_updateLaw_28 ::
  T_SyntheticOneMinusDynamicsWitness_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_updateLaw_28 v0
  = case coe v0 of
      C_SyntheticOneMinusDynamicsWitness'46'constructor_187 v1 v2 v3
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness.SyntheticOneMinusDynamicsWitness.shellNeighborhoodPreserved
d_shellNeighborhoodPreserved_30 ::
  T_SyntheticOneMinusDynamicsWitness_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shellNeighborhoodPreserved_30 = erased
-- DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness.SyntheticOneMinusDynamicsWitness.shell1ProfilePreserved
d_shell1ProfilePreserved_32 ::
  T_SyntheticOneMinusDynamicsWitness_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shell1ProfilePreserved_32 = erased
-- DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness.SyntheticOneMinusDynamicsWitness.shell2ProfilePreserved
d_shell2ProfilePreserved_34 ::
  T_SyntheticOneMinusDynamicsWitness_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shell2ProfilePreserved_34 = erased
-- DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness.syntheticDynamicsWitness
d_syntheticDynamicsWitness_36 ::
  T_SyntheticOneMinusDynamicsWitness_10
d_syntheticDynamicsWitness_36
  = coe
      C_SyntheticOneMinusDynamicsWitness'46'constructor_187
      ("synthetic-one-minus-admissible-dynamics" :: Data.Text.Text)
      (2 :: Integer)
      ("two-state profile-preserving synthetic update" :: Data.Text.Text)

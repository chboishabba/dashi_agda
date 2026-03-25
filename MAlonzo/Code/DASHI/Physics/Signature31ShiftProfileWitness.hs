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

module MAlonzo.Code.DASHI.Physics.Signature31ShiftProfileWitness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm
import qualified MAlonzo.Code.DASHI.Physics.OrbitSignatureDiscriminant

-- DASHI.Physics.Signature31ShiftProfileWitness.computedProfile
d_computedProfile_6 :: [Integer]
d_computedProfile_6
  = coe
      MAlonzo.Code.DASHI.Physics.OrbitSignatureDiscriminant.d_append3_20
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (31 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm.d_shell1_p3_q1_computed_340)
      (coe
         MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm.d_shell2_p3_q1_computed_342)
-- DASHI.Physics.Signature31ShiftProfileWitness.measured≡computed
d_measured'8801'computed_8 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_measured'8801'computed_8 = erased
-- DASHI.Physics.Signature31ShiftProfileWitness.computed≡sig31Profile
d_computed'8801'sig31Profile_10 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_computed'8801'sig31Profile_10 = erased
-- DASHI.Physics.Signature31ShiftProfileWitness._.sym
d_sym_22 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_22 = erased

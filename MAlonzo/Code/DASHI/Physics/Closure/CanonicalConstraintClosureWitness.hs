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

module MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintClosureWitness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Closure

-- DASHI.Physics.Closure.CanonicalConstraintClosureWitness.CanonicalConstraintClosureWitness
d_CanonicalConstraintClosureWitness_8 = ()
newtype T_CanonicalConstraintClosureWitness_8
  = C_CanonicalConstraintClosureWitness'46'constructor_119 MAlonzo.Code.DASHI.Physics.Constraints.Closure.T_ClosureLaw_12
-- DASHI.Physics.Closure.CanonicalConstraintClosureWitness.CanonicalConstraintClosureWitness.crcpCloses
d_crcpCloses_18 ::
  T_CanonicalConstraintClosureWitness_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_crcpCloses_18 = erased
-- DASHI.Physics.Closure.CanonicalConstraintClosureWitness.CanonicalConstraintClosureWitness.cpccCloses
d_cpccCloses_20 ::
  T_CanonicalConstraintClosureWitness_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cpccCloses_20 = erased
-- DASHI.Physics.Closure.CanonicalConstraintClosureWitness.CanonicalConstraintClosureWitness.crccCloses
d_crccCloses_22 ::
  T_CanonicalConstraintClosureWitness_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_crccCloses_22 = erased
-- DASHI.Physics.Closure.CanonicalConstraintClosureWitness.CanonicalConstraintClosureWitness.closureWitness
d_closureWitness_24 ::
  T_CanonicalConstraintClosureWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Constraints.Closure.T_ClosureLaw_12
d_closureWitness_24 v0
  = case coe v0 of
      C_CanonicalConstraintClosureWitness'46'constructor_119 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.CanonicalConstraintClosureWitness.canonicalConstraintClosureWitness
d_canonicalConstraintClosureWitness_26 ::
  T_CanonicalConstraintClosureWitness_8
d_canonicalConstraintClosureWitness_26
  = coe
      C_CanonicalConstraintClosureWitness'46'constructor_119
      MAlonzo.Code.DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem.d_canonicalPathInducedConstraintClosure_28

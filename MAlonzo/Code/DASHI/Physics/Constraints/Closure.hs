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

module MAlonzo.Code.DASHI.Physics.Constraints.Closure where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Bracket
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Generators

-- DASHI.Physics.Constraints.Closure.ClosureLaw
d_ClosureLaw_12 a0 a1 = ()
newtype T_ClosureLaw_12
  = C_ClosureLaw'46'constructor_269 (AgdaAny ->
                                     AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- DASHI.Physics.Constraints.Closure.ClosureLaw.closes
d_closes_64 ::
  T_ClosureLaw_12 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closes_64 v0
  = case coe v0 of
      C_ClosureLaw'46'constructor_269 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError

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

module MAlonzo.Code.DASHI.Physics.Constraints.Generators where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- DASHI.Physics.Constraints.Generators.ConstraintSystem
d_ConstraintSystem_8 = ()
newtype T_ConstraintSystem_8
  = C_ConstraintSystem'46'constructor_23 (() ->
                                          AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Physics.Constraints.Generators.ConstraintSystem.Constraint
d_Constraint_18 :: T_ConstraintSystem_8 -> ()
d_Constraint_18 = erased
-- DASHI.Physics.Constraints.Generators.ConstraintSystem.actsOn
d_actsOn_20 :: T_ConstraintSystem_8 -> () -> ()
d_actsOn_20 = erased
-- DASHI.Physics.Constraints.Generators.ConstraintSystem.apply
d_apply_24 ::
  T_ConstraintSystem_8 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_apply_24 v0
  = case coe v0 of
      C_ConstraintSystem'46'constructor_23 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError

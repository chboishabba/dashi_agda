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

module MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Bracket
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Closure
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Generators

-- DASHI.Physics.Constraints.ConcreteInstance.C
d_C_8 = ()
data T_C_8 = C_CR_10 | C_CP_12 | C_CC_14
-- DASHI.Physics.Constraints.ConcreteInstance.CS
d_CS_16 ::
  MAlonzo.Code.DASHI.Physics.Constraints.Generators.T_ConstraintSystem_8
d_CS_16
  = coe
      MAlonzo.Code.DASHI.Physics.Constraints.Generators.C_ConstraintSystem'46'constructor_23
      (\ v0 v1 v2 -> v2)
-- DASHI.Physics.Constraints.ConcreteInstance.L
d_L_26 ::
  MAlonzo.Code.DASHI.Physics.Constraints.Bracket.T_LieLike_10
d_L_26
  = coe
      MAlonzo.Code.DASHI.Physics.Constraints.Bracket.C_LieLike'46'constructor_19
      d_bracket_32
-- DASHI.Physics.Constraints.ConcreteInstance._.bracket
d_bracket_32 :: T_C_8 -> T_C_8 -> T_C_8
d_bracket_32 v0 v1
  = case coe v0 of
      C_CR_10
        -> case coe v1 of
             C_CR_10 -> coe v1
             C_CP_12 -> coe C_CC_14
             C_CC_14 -> coe C_CP_12
             _ -> MAlonzo.RTE.mazUnreachableError
      C_CP_12
        -> case coe v1 of
             C_CR_10 -> coe C_CC_14
             C_CP_12 -> coe v1
             C_CC_14 -> coe C_CR_10
             _ -> MAlonzo.RTE.mazUnreachableError
      C_CC_14
        -> case coe v1 of
             C_CR_10 -> coe C_CP_12
             C_CP_12 -> coe C_CR_10
             C_CC_14 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Constraints.ConcreteInstance.closure
d_closure_34 ::
  MAlonzo.Code.DASHI.Physics.Constraints.Closure.T_ClosureLaw_12
d_closure_34
  = coe
      MAlonzo.Code.DASHI.Physics.Constraints.Closure.C_ClosureLaw'46'constructor_269
      (coe
         (\ v0 v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe d_bracket_32 (coe v0) (coe v1)) erased))

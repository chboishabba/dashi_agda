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

module MAlonzo.Code.DASHI.Algebra.Trit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality

-- DASHI.Algebra.Trit.Trit
d_Trit_6 = ()
data T_Trit_6 = C_neg_8 | C_zer_10 | C_pos_12
-- DASHI.Algebra.Trit.inv
d_inv_14 :: T_Trit_6 -> T_Trit_6
d_inv_14 v0
  = case coe v0 of
      C_neg_8 -> coe C_pos_12
      C_zer_10 -> coe v0
      C_pos_12 -> coe C_neg_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Algebra.Trit.inv-invol
d_inv'45'invol_18 ::
  T_Trit_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'invol_18 = erased

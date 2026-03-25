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

module MAlonzo.Code.DASHI.Physics.Constraints.Bracket where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Generators

-- DASHI.Physics.Constraints.Bracket.LieLike
d_LieLike_10 a0 = ()
newtype T_LieLike_10
  = C_LieLike'46'constructor_19 (AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Physics.Constraints.Bracket.LieLike._[_,]_
d__'91'_'44''93'__36 ::
  T_LieLike_10 -> AgdaAny -> AgdaAny -> AgdaAny
d__'91'_'44''93'__36 v0
  = case coe v0 of
      C_LieLike'46'constructor_19 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Constraints.Bracket.LieLike.antisym
d_antisym_38 :: T_LieLike_10 -> ()
d_antisym_38 = erased
-- DASHI.Physics.Constraints.Bracket.LieLike.jacobi
d_jacobi_40 :: T_LieLike_10 -> ()
d_jacobi_40 = erased

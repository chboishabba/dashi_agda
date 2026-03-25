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

module MAlonzo.Code.DASHI.Geometry.RealFiniteSpeed.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- DASHI.Geometry.RealFiniteSpeed.Core.RealFiniteSpeed
d_RealFiniteSpeed_12 a0 a1 = ()
newtype T_RealFiniteSpeed_12
  = C_RealFiniteSpeed'46'constructor_107 (AgdaAny ->
                                          AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Geometry.RealFiniteSpeed.Core.RealFiniteSpeed.local
d_local_26 :: T_RealFiniteSpeed_12 -> AgdaAny -> AgdaAny -> ()
d_local_26 = erased
-- DASHI.Geometry.RealFiniteSpeed.Core.RealFiniteSpeed.preservesLocality
d_preservesLocality_32 ::
  T_RealFiniteSpeed_12 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_preservesLocality_32 v0
  = case coe v0 of
      C_RealFiniteSpeed'46'constructor_107 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError

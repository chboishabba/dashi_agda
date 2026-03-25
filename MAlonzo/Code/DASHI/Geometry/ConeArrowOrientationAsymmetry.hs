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

module MAlonzo.Code.DASHI.Geometry.ConeArrowOrientationAsymmetry where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality

-- DASHI.Geometry.ConeArrowOrientationAsymmetry.IntrinsicOrientation
d_IntrinsicOrientation_6 = ()
newtype T_IntrinsicOrientation_6
  = C_IntrinsicOrientation'46'constructor_23 Integer
-- DASHI.Geometry.ConeArrowOrientationAsymmetry.IntrinsicOrientation.orientationTag
d_orientationTag_12 :: T_IntrinsicOrientation_6 -> Integer
d_orientationTag_12 v0
  = case coe v0 of
      C_IntrinsicOrientation'46'constructor_23 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ConeArrowOrientationAsymmetry.IntrinsicOrientation.orientationTag≡sig31
d_orientationTag'8801'sig31_14 ::
  T_IntrinsicOrientation_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_orientationTag'8801'sig31_14 = erased

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

module MAlonzo.Code.DASHI.Physics.ShellOrbitProfileGenerator where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Physics.DimensionBoundAssumptions
import qualified MAlonzo.Code.Data.List.Base

-- DASHI.Physics.ShellOrbitProfileGenerator.profileFromSorted
d_profileFromSorted_8 ::
  Integer ->
  [Integer] ->
  MAlonzo.Code.DASHI.Physics.DimensionBoundAssumptions.T_ShellOrbitProfile_34
d_profileFromSorted_8 ~v0 v1 = du_profileFromSorted_8 v1
du_profileFromSorted_8 ::
  [Integer] ->
  MAlonzo.Code.DASHI.Physics.DimensionBoundAssumptions.T_ShellOrbitProfile_34
du_profileFromSorted_8 v0
  = coe
      MAlonzo.Code.DASHI.Physics.DimensionBoundAssumptions.C_ShellOrbitProfile'46'constructor_277
      (coe MAlonzo.Code.Data.List.Base.du_length_284 v0)
      (coe du_top1Of_18 (coe v0)) (coe du_top2Of_22 (coe v0))
      (coe du_top3Of_26 (coe v0))
-- DASHI.Physics.ShellOrbitProfileGenerator._.top1Of
d_top1Of_18 :: Integer -> [Integer] -> [Integer] -> Integer
d_top1Of_18 ~v0 ~v1 v2 = du_top1Of_18 v2
du_top1Of_18 :: [Integer] -> Integer
du_top1Of_18 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ShellOrbitProfileGenerator._.top2Of
d_top2Of_22 :: Integer -> [Integer] -> [Integer] -> Integer
d_top2Of_22 ~v0 ~v1 v2 = du_top2Of_22 v2
du_top2Of_22 :: [Integer] -> Integer
du_top2Of_22 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v3 of
                (:) v4 v5 -> coe v4
                _ -> coe v1
         _ -> coe v1)
-- DASHI.Physics.ShellOrbitProfileGenerator._.top3Of
d_top3Of_26 :: Integer -> [Integer] -> [Integer] -> Integer
d_top3Of_26 ~v0 ~v1 v2 = du_top3Of_26 v2
du_top3Of_26 :: [Integer] -> Integer
du_top3Of_26 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v3 of
                (:) v4 v5
                  -> case coe v5 of
                       (:) v6 v7 -> coe v6
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)

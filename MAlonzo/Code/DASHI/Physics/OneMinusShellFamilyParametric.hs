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

module MAlonzo.Code.DASHI.Physics.OneMinusShellFamilyParametric where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass

-- DASHI.Physics.OneMinusShellFamilyParametric.familyFormulaNeighborhood
d_familyFormulaNeighborhood_6 ::
  Integer ->
  MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass.T_ShellNeighborhoodClass_6
d_familyFormulaNeighborhood_6 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass.C_unknownShellNeighborhood_16
      1 -> coe
             MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass.C_unknownShellNeighborhood_16
      2 -> coe
             MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass.C_oneMinusShellNeighborhood_10
      3 -> coe
             MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass.C_oneMinusShellNeighborhood_10
      _ -> coe
             MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass.d_classifyTriple_110
             (coe
                mulInt
                (coe
                   mulInt (coe (2 :: Integer))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                      (subInt (coe v0) (coe (1 :: Integer))) (1 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (mulInt
                      (coe (2 :: Integer))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                         (subInt (coe v0) (coe (1 :: Integer))) (1 :: Integer)))
                   (2 :: Integer)))
             (coe
                mulInt (coe (2 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (subInt (coe v0) (coe (1 :: Integer))) (1 :: Integer)))
             (coe (2 :: Integer))
-- DASHI.Physics.OneMinusShellFamilyParametric.familyFormulaNeighborhood-theorem
d_familyFormulaNeighborhood'45'theorem_14 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_familyFormulaNeighborhood'45'theorem_14 = erased
-- DASHI.Physics.OneMinusShellFamilyParametric.shiftMatchesParametricFamily
d_shiftMatchesParametricFamily_18 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shiftMatchesParametricFamily_18 = erased

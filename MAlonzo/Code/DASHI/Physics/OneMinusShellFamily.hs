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

module MAlonzo.Code.DASHI.Physics.OneMinusShellFamily where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.DASHI.Physics.OrbitProfileData

-- DASHI.Physics.OneMinusShellFamily.OneMinusShell1Member
d_OneMinusShell1Member_6 = ()
data T_OneMinusShell1Member_6
  = C_OneMinusShell1Member'46'constructor_11 Integer [Integer]
-- DASHI.Physics.OneMinusShellFamily.OneMinusShell1Member.dimension
d_dimension_12 :: T_OneMinusShell1Member_6 -> Integer
d_dimension_12 v0
  = case coe v0 of
      C_OneMinusShell1Member'46'constructor_11 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OneMinusShellFamily.OneMinusShell1Member.shell1Top
d_shell1Top_14 :: T_OneMinusShell1Member_6 -> [Integer]
d_shell1Top_14 v0
  = case coe v0 of
      C_OneMinusShell1Member'46'constructor_11 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OneMinusShellFamily.oneMinusShell1TopFromB
d_oneMinusShell1TopFromB_16 :: Integer -> [Integer]
d_oneMinusShell1TopFromB_16 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         mulInt (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (2 :: Integer)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- DASHI.Physics.OneMinusShellFamily.formula≥4
d_formula'8805'4_20 :: Integer -> [Integer]
d_formula'8805'4_20 v0
  = coe
      d_oneMinusShell1TopFromB_16
      (coe
         mulInt (coe (2 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (1 :: Integer)))
-- DASHI.Physics.OneMinusShellFamily.familyFormulaShell1
d_familyFormulaShell1_26 :: Integer -> [Integer]
d_familyFormulaShell1_26 v0
  = let v1 = d_formula'8805'4_20 (coe v0) in
    coe
      (case coe v0 of
         0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         2 -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         3 -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (8 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (4 :: Integer))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         _ -> coe v1)
-- DASHI.Physics.OneMinusShellFamily.member2
d_member2_30 :: T_OneMinusShell1Member_6
d_member2_30
  = coe
      C_OneMinusShell1Member'46'constructor_11 (coe (2 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- DASHI.Physics.OneMinusShellFamily.member3
d_member3_32 :: T_OneMinusShell1Member_6
d_member3_32
  = coe
      C_OneMinusShell1Member'46'constructor_11 (coe (3 :: Integer))
      (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell1_p2_q1_18)
-- DASHI.Physics.OneMinusShellFamily.member4
d_member4_34 :: T_OneMinusShell1Member_6
d_member4_34
  = coe
      C_OneMinusShell1Member'46'constructor_11 (coe (4 :: Integer))
      (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell1_p3_q1_26)
-- DASHI.Physics.OneMinusShellFamily.member5
d_member5_36 :: T_OneMinusShell1Member_6
d_member5_36
  = coe
      C_OneMinusShell1Member'46'constructor_11 (coe (5 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (48 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (8 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- DASHI.Physics.OneMinusShellFamily.member6
d_member6_38 :: T_OneMinusShell1Member_6
d_member6_38
  = coe
      C_OneMinusShell1Member'46'constructor_11 (coe (6 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (80 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (10 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- DASHI.Physics.OneMinusShellFamily.member7
d_member7_40 :: T_OneMinusShell1Member_6
d_member7_40
  = coe
      C_OneMinusShell1Member'46'constructor_11 (coe (7 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (120 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (12 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- DASHI.Physics.OneMinusShellFamily.member8
d_member8_42 :: T_OneMinusShell1Member_6
d_member8_42
  = coe
      C_OneMinusShell1Member'46'constructor_11 (coe (8 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (168 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (14 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- DASHI.Physics.OneMinusShellFamily.member2-formula
d_member2'45'formula_44 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member2'45'formula_44 = erased
-- DASHI.Physics.OneMinusShellFamily.member3-formula
d_member3'45'formula_46 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member3'45'formula_46 = erased
-- DASHI.Physics.OneMinusShellFamily.member4-formula
d_member4'45'formula_48 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member4'45'formula_48 = erased
-- DASHI.Physics.OneMinusShellFamily.member5-formula
d_member5'45'formula_50 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member5'45'formula_50 = erased
-- DASHI.Physics.OneMinusShellFamily.member6-formula
d_member6'45'formula_52 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member6'45'formula_52 = erased
-- DASHI.Physics.OneMinusShellFamily.member7-formula
d_member7'45'formula_54 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member7'45'formula_54 = erased
-- DASHI.Physics.OneMinusShellFamily.member8-formula
d_member8'45'formula_56 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member8'45'formula_56 = erased
-- DASHI.Physics.OneMinusShellFamily.member2-neighborhood
d_member2'45'neighborhood_58 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member2'45'neighborhood_58 = erased
-- DASHI.Physics.OneMinusShellFamily.member3-neighborhood
d_member3'45'neighborhood_60 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member3'45'neighborhood_60 = erased
-- DASHI.Physics.OneMinusShellFamily.member4-neighborhood
d_member4'45'neighborhood_62 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member4'45'neighborhood_62 = erased
-- DASHI.Physics.OneMinusShellFamily.member5-neighborhood
d_member5'45'neighborhood_64 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member5'45'neighborhood_64 = erased
-- DASHI.Physics.OneMinusShellFamily.member6-neighborhood
d_member6'45'neighborhood_66 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member6'45'neighborhood_66 = erased
-- DASHI.Physics.OneMinusShellFamily.member7-neighborhood
d_member7'45'neighborhood_68 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member7'45'neighborhood_68 = erased
-- DASHI.Physics.OneMinusShellFamily.member8-neighborhood
d_member8'45'neighborhood_70 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_member8'45'neighborhood_70 = erased

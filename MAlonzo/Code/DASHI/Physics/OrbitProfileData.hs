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

module MAlonzo.Code.DASHI.Physics.OrbitProfileData where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm

-- DASHI.Physics.OrbitProfileData.shell1_p0_q4
d_shell1_p0_q4_6 :: [Integer]
d_shell1_p0_q4_6
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (8 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- DASHI.Physics.OrbitProfileData.shell2_p0_q4
d_shell2_p0_q4_8 :: [Integer]
d_shell2_p0_q4_8
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (24 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- DASHI.Physics.OrbitProfileData.shell1_p1_q2
d_shell1_p1_q2_10 :: [Integer]
d_shell1_p1_q2_10
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (8 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (4 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- DASHI.Physics.OrbitProfileData.shell2_p1_q2
d_shell2_p1_q2_12 :: [Integer]
d_shell2_p1_q2_12
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (4 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- DASHI.Physics.OrbitProfileData.shell1_p1_q3
d_shell1_p1_q3_14 :: [Integer]
d_shell1_p1_q3_14
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (24 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (6 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- DASHI.Physics.OrbitProfileData.shell2_p1_q3
d_shell2_p1_q3_16 :: [Integer]
d_shell2_p1_q3_16
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (16 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (12 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- DASHI.Physics.OrbitProfileData.shell1_p2_q1
d_shell1_p2_q1_18 :: [Integer]
d_shell1_p2_q1_18
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (8 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (4 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (2 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- DASHI.Physics.OrbitProfileData.shell2_p2_q1
d_shell2_p2_q1_20 :: [Integer]
d_shell2_p2_q1_20
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (4 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- DASHI.Physics.OrbitProfileData.shell1_p2_q2
d_shell1_p2_q2_22 :: [Integer]
d_shell1_p2_q2_22
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (16 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (16 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (4 :: Integer))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- DASHI.Physics.OrbitProfileData.shell2_p2_q2
d_shell2_p2_q2_24 :: [Integer]
d_shell2_p2_q2_24
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (4 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (4 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- DASHI.Physics.OrbitProfileData.shell1_p3_q1
d_shell1_p3_q1_26 :: [Integer]
d_shell1_p3_q1_26
  = coe
      MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm.d_shell1_p3_q1_computed_340
-- DASHI.Physics.OrbitProfileData.shell2_p3_q1
d_shell2_p3_q1_28 :: [Integer]
d_shell2_p3_q1_28
  = coe
      MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm.d_shell2_p3_q1_computed_342
-- DASHI.Physics.OrbitProfileData.shell1_p4_q0
d_shell1_p4_q0_30 :: [Integer]
d_shell1_p4_q0_30
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (8 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- DASHI.Physics.OrbitProfileData.shell2_p4_q0
d_shell2_p4_q0_32 :: [Integer]
d_shell2_p4_q0_32
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (24 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)

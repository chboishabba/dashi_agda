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

module MAlonzo.Code.DASHI.Physics.SyntheticOneMinusShellRealization where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.DASHI.Physics.OneMinusShellFamily
import qualified MAlonzo.Code.DASHI.Physics.OrbitProfileData
import qualified MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass

-- DASHI.Physics.SyntheticOneMinusShellRealization.label
d_label_6 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_label_6
  = coe ("synthetic-one-minus-shell-family" :: Data.Text.Text)
-- DASHI.Physics.SyntheticOneMinusShellRealization.shell1Profile
d_shell1Profile_8 :: [Integer]
d_shell1Profile_8
  = coe
      MAlonzo.Code.DASHI.Physics.OneMinusShellFamily.d_familyFormulaShell1_26
      (coe (4 :: Integer))
-- DASHI.Physics.SyntheticOneMinusShellRealization.shell2Profile
d_shell2Profile_10 :: [Integer]
d_shell2Profile_10
  = coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell2_p3_q1_28
-- DASHI.Physics.SyntheticOneMinusShellRealization.shellNeighborhood
d_shellNeighborhood_12 ::
  MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass.T_ShellNeighborhoodClass_6
d_shellNeighborhood_12
  = coe
      MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass.d_classifyShell1Neighborhood_134
      (coe d_shell1Profile_8)
-- DASHI.Physics.SyntheticOneMinusShellRealization.shellNeighborhood-theorem
d_shellNeighborhood'45'theorem_14 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shellNeighborhood'45'theorem_14 = erased

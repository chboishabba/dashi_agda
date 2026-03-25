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

module MAlonzo.Code.DASHI.Physics.DimensionBoundAssumptions where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma

-- DASHI.Physics.DimensionBoundAssumptions.IndefiniteSignature
d_IndefiniteSignature_10 a0 a1 = ()
data T_IndefiniteSignature_10
  = C_IndefiniteSignature'46'constructor_169 (AgdaAny -> Integer)
                                             MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- DASHI.Physics.DimensionBoundAssumptions.IndefiniteSignature.Q
d_Q_24 :: T_IndefiniteSignature_10 -> AgdaAny -> Integer
d_Q_24 v0
  = case coe v0 of
      C_IndefiniteSignature'46'constructor_169 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.DimensionBoundAssumptions.IndefiniteSignature.Q-def
d_Q'45'def_28 ::
  T_IndefiniteSignature_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Q'45'def_28 = erased
-- DASHI.Physics.DimensionBoundAssumptions.IndefiniteSignature.sig
d_sig_30 ::
  T_IndefiniteSignature_10 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sig_30 v0
  = case coe v0 of
      C_IndefiniteSignature'46'constructor_169 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.DimensionBoundAssumptions.ShellOrbitProfile
d_ShellOrbitProfile_34 a0 = ()
data T_ShellOrbitProfile_34
  = C_ShellOrbitProfile'46'constructor_277 Integer Integer Integer
                                           Integer
-- DASHI.Physics.DimensionBoundAssumptions.ShellOrbitProfile.orbitCount
d_orbitCount_46 :: T_ShellOrbitProfile_34 -> Integer
d_orbitCount_46 v0
  = case coe v0 of
      C_ShellOrbitProfile'46'constructor_277 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.DimensionBoundAssumptions.ShellOrbitProfile.top1
d_top1_48 :: T_ShellOrbitProfile_34 -> Integer
d_top1_48 v0
  = case coe v0 of
      C_ShellOrbitProfile'46'constructor_277 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.DimensionBoundAssumptions.ShellOrbitProfile.top2
d_top2_50 :: T_ShellOrbitProfile_34 -> Integer
d_top2_50 v0
  = case coe v0 of
      C_ShellOrbitProfile'46'constructor_277 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.DimensionBoundAssumptions.ShellOrbitProfile.top3
d_top3_52 :: T_ShellOrbitProfile_34 -> Integer
d_top3_52 v0
  = case coe v0 of
      C_ShellOrbitProfile'46'constructor_277 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.DimensionBoundAssumptions.DimensionBoundGate
d_DimensionBoundGate_54 = ()
data T_DimensionBoundGate_54
  = C_DimensionBoundGate'46'constructor_353
-- DASHI.Physics.DimensionBoundAssumptions.DimensionBoundGate.hasBound
d_hasBound_58 :: T_DimensionBoundGate_54 -> ()
d_hasBound_58 = erased

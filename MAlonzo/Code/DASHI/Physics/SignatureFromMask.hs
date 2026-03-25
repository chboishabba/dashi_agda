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

module MAlonzo.Code.DASHI.Physics.SignatureFromMask where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.SignatureFromMask.countPlus
d_countPlus_8 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_countPlus_8 ~v0 v1 = du_countPlus_8 v1
du_countPlus_8 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_countPlus_8 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe (0 :: Integer)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> case coe v2 of
             MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.C_plus_48
               -> coe addInt (coe (1 :: Integer)) (coe du_countPlus_8 (coe v3))
             MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.C_minus_50
               -> coe du_countPlus_8 (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.SignatureFromMask.countMinus
d_countMinus_16 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_countMinus_16 ~v0 v1 = du_countMinus_16 v1
du_countMinus_16 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_countMinus_16 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe (0 :: Integer)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> case coe v2 of
             MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.C_plus_48
               -> coe du_countMinus_16 (coe v3)
             MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.C_minus_50
               -> coe addInt (coe (1 :: Integer)) (coe du_countMinus_16 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.SignatureFromMask.signature
d_signature_24 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_signature_24 ~v0 v1 = du_signature_24 v1
du_signature_24 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_signature_24 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_countMinus_16 (coe v0)) (coe du_countPlus_8 (coe v0))
-- DASHI.Physics.SignatureFromMask.replicatePlus
d_replicatePlus_30 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_replicatePlus_30 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                (coe MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.C_plus_48)
                (d_replicatePlus_30 (coe v1)))
-- DASHI.Physics.SignatureFromMask.oneMinusRestPlus
d_oneMinusRestPlus_36 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_oneMinusRestPlus_36 v0
  = coe
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38
      (coe MAlonzo.Code.DASHI.Physics.IndefiniteMaskQuadratic.C_minus_50)
      (d_replicatePlus_30 (coe v0))
-- DASHI.Physics.SignatureFromMask.countPlus-replicatePlus
d_countPlus'45'replicatePlus_42 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_countPlus'45'replicatePlus_42 = erased
-- DASHI.Physics.SignatureFromMask.countMinus-replicatePlus
d_countMinus'45'replicatePlus_48 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_countMinus'45'replicatePlus_48 = erased
-- DASHI.Physics.SignatureFromMask.signature-oneMinus
d_signature'45'oneMinus_54 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_signature'45'oneMinus_54 = erased

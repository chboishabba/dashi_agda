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

module MAlonzo.Code.DASHI.Physics.RealTernaryCarrier where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Algebra.Trit
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.RealTernaryCarrier.Carrier
d_Carrier_6 :: Integer -> ()
d_Carrier_6 = erased
-- DASHI.Physics.RealTernaryCarrier.invVec
d_invVec_12 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_invVec_12 ~v0 = du_invVec_12
du_invVec_12 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_invVec_12
  = coe
      MAlonzo.Code.Data.Vec.Base.du_map_178
      (coe MAlonzo.Code.DASHI.Algebra.Trit.d_inv_14)
-- DASHI.Physics.RealTernaryCarrier.invVec-invol
d_invVec'45'invol_20 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_invVec'45'invol_20 = erased
-- DASHI.Physics.RealTernaryCarrier.zeroVec
d_zeroVec_36 :: Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_zeroVec_36 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                (coe MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10)
                (d_zeroVec_36 (coe v1)))

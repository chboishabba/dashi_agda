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

module MAlonzo.Code.DASHI.Geometry.Signature.HyperbolicFormZ90Z where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Geometry.Signature.HyperbolicFormZ.CausalCountsZ
d_CausalCountsZ_10 a0 = ()
data T_CausalCountsZ_10
  = C_CausalCountsZ'46'constructor_23 Integer
                                      MAlonzo.Code.Data.Vec.Base.T_Vec_28
-- DASHI.Geometry.Signature.HyperbolicFormZ.CausalCountsZ.tau
d_tau_18 :: T_CausalCountsZ_10 -> Integer
d_tau_18 v0
  = case coe v0 of
      C_CausalCountsZ'46'constructor_23 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature.HyperbolicFormZ.CausalCountsZ.sigma
d_sigma_20 ::
  T_CausalCountsZ_10 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_sigma_20 v0
  = case coe v0 of
      C_CausalCountsZ'46'constructor_23 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature.HyperbolicFormZ.sumSq
d_sumSq_24 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_sumSq_24 ~v0 v1 = du_sumSq_24 v1
du_sumSq_24 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_sumSq_24 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe (0 :: Integer)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'43'__276
             (coe MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2) (coe v2))
             (coe du_sumSq_24 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature.HyperbolicFormZ.F
d_F_32 ::
  Integer -> Integer -> Integer -> T_CausalCountsZ_10 -> Integer
d_F_32 ~v0 v1 v2 v3 = du_F_32 v1 v2 v3
du_F_32 :: Integer -> Integer -> T_CausalCountsZ_10 -> Integer
du_F_32 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'45'__294
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0)
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe d_tau_18 (coe v2))
            (coe d_tau_18 (coe v2))))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v1)
         (coe du_sumSq_24 (coe d_sigma_20 (coe v2))))
-- DASHI.Geometry.Signature.HyperbolicFormZ.ConeBound
d_ConeBound_44 :: Integer -> Integer -> T_CausalCountsZ_10 -> ()
d_ConeBound_44 = erased
-- DASHI.Geometry.Signature.HyperbolicFormZ.ConeBoundary
d_ConeBoundary_54 :: Integer -> Integer -> T_CausalCountsZ_10 -> ()
d_ConeBoundary_54 = erased

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

module MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility
import qualified MAlonzo.Code.DASHI.Geometry.ParallelogramLaw

-- DASHI.Geometry.SignatureUniqueness31.Signature
d_Signature_6 = ()
data T_Signature_6 = C_sig31_8 | C_sig13_10 | C_other_12
-- DASHI.Geometry.SignatureUniqueness31.SignatureLaw
d_SignatureLaw_14 = ()
newtype T_SignatureLaw_14
  = C_SignatureLaw'46'constructor_1 T_Signature_6
-- DASHI.Geometry.SignatureUniqueness31.SignatureLaw.forced
d_forced_18 :: T_SignatureLaw_14 -> T_Signature_6
d_forced_18 v0
  = case coe v0 of
      C_SignatureLaw'46'constructor_1 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.SignatureUniqueness31.Signature31Theorem
d_Signature31Theorem_20 = ()
newtype T_Signature31Theorem_20
  = C_Signature31Theorem'46'constructor_57 (MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
                                            MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
                                            MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
                                            MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
                                            () -> () -> () -> T_SignatureLaw_14)
-- DASHI.Geometry.SignatureUniqueness31.Signature31Theorem.prove
d_prove_48 ::
  T_Signature31Theorem_20 ->
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () -> () -> () -> T_SignatureLaw_14
d_prove_48 v0
  = case coe v0 of
      C_Signature31Theorem'46'constructor_57 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError

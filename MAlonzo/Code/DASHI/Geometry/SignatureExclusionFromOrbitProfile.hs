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

module MAlonzo.Code.DASHI.Geometry.SignatureExclusionFromOrbitProfile where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31

-- DASHI.Geometry.SignatureExclusionFromOrbitProfile.signatureLawFromProfileEq
d_signatureLawFromProfileEq_8 ::
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
d_signatureLawFromProfileEq_8 ~v0 ~v1
  = du_signatureLawFromProfileEq_8
du_signatureLawFromProfileEq_8 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
du_signatureLawFromProfileEq_8
  = coe
      MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.C_SignatureLaw'46'constructor_1
      (coe MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.C_sig31_8)
-- DASHI.Geometry.SignatureExclusionFromOrbitProfile.signatureFromProfileEq
d_signatureFromProfileEq_16 ::
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_signatureFromProfileEq_16 ~v0 ~v1 = du_signatureFromProfileEq_16
du_signatureFromProfileEq_16 ::
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
du_signatureFromProfileEq_16
  = coe MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_sig31_288

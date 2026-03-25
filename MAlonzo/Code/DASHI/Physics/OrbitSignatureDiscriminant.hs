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

module MAlonzo.Code.DASHI.Physics.OrbitSignatureDiscriminant where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.DASHI.Physics.OrbitProfileData
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base

-- DASHI.Physics.OrbitSignatureDiscriminant.Signature
d_Signature_6 = ()
data T_Signature_6
  = C_sig40_8 | C_sig31_10 | C_sig22_12 | C_sig13_14 | C_sig04_16
-- DASHI.Physics.OrbitSignatureDiscriminant.Profile
d_Profile_18 :: ()
d_Profile_18 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.append3
d_append3_20 :: [Integer] -> [Integer] -> [Integer] -> [Integer]
d_append3_20 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v1))
      (coe v2)
-- DASHI.Physics.OrbitSignatureDiscriminant.OrbitProfile
d_OrbitProfile_30 a0 = ()
newtype T_OrbitProfile_30
  = C_OrbitProfile'46'constructor_133 [Integer]
-- DASHI.Physics.OrbitSignatureDiscriminant.OrbitProfile.profile
d_profile_36 :: T_OrbitProfile_30 -> [Integer]
d_profile_36 v0
  = case coe v0 of
      C_OrbitProfile'46'constructor_133 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitSignatureDiscriminant.OrientationTag
d_OrientationTag_38 :: T_Signature_6 -> Integer
d_OrientationTag_38 v0
  = case coe v0 of
      C_sig40_8 -> coe (40 :: Integer)
      C_sig31_10 -> coe (31 :: Integer)
      C_sig22_12 -> coe (22 :: Integer)
      C_sig13_14 -> coe (13 :: Integer)
      C_sig04_16 -> coe (4 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitSignatureDiscriminant.ProfileOf
d_ProfileOf_40 :: T_Signature_6 -> [Integer]
d_ProfileOf_40 v0
  = case coe v0 of
      C_sig40_8
        -> coe
             d_append3_20
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_OrientationTag_38 (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell1_p4_q0_30)
             (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell2_p4_q0_32)
      C_sig31_10
        -> coe
             d_append3_20
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_OrientationTag_38 (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell1_p3_q1_26)
             (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell2_p3_q1_28)
      C_sig22_12
        -> coe
             d_append3_20
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_OrientationTag_38 (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell1_p2_q2_22)
             (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell2_p2_q2_24)
      C_sig13_14
        -> coe
             d_append3_20
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_OrientationTag_38 (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell1_p1_q3_14)
             (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell2_p1_q3_16)
      C_sig04_16
        -> coe
             d_append3_20
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_OrientationTag_38 (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell1_p0_q4_6)
             (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell2_p0_q4_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitSignatureDiscriminant.MeasuredProfile
d_MeasuredProfile_42 :: [Integer]
d_MeasuredProfile_42
  = coe
      d_append3_20
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (31 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell1_p3_q1_26)
      (coe MAlonzo.Code.DASHI.Physics.OrbitProfileData.d_shell2_p3_q1_28)
-- DASHI.Physics.OrbitSignatureDiscriminant.MeasuredSignature
d_MeasuredSignature_44 :: T_Signature_6
d_MeasuredSignature_44 = coe C_sig31_10
-- DASHI.Physics.OrbitSignatureDiscriminant.measured-profile-def
d_measured'45'profile'45'def_46 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_measured'45'profile'45'def_46 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.OrientationTag-diff
d_OrientationTag'45'diff_48 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_OrientationTag'45'diff_48 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.OrientationTag-neq31-sig40
d_OrientationTag'45'neq31'45'sig40_50 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_OrientationTag'45'neq31'45'sig40_50 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.OrientationTag-neq31-sig22
d_OrientationTag'45'neq31'45'sig22_52 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_OrientationTag'45'neq31'45'sig22_52 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.OrientationTag-neq31-sig13
d_OrientationTag'45'neq31'45'sig13_54 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_OrientationTag'45'neq31'45'sig13_54 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.OrientationTag-neq31-sig04
d_OrientationTag'45'neq31'45'sig04_56 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_OrientationTag'45'neq31'45'sig04_56 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.headProfile
d_headProfile_58 :: [Integer] -> Integer
d_headProfile_58 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.OrbitSignatureDiscriminant.headMeasured
d_headMeasured_62 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_headMeasured_62 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.headProfileOf
d_headProfileOf_66 ::
  T_Signature_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_headProfileOf_66 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.Profile-sig31≢sig13
d_Profile'45'sig31'8802'sig13_68 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_Profile'45'sig31'8802'sig13_68 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.SignatureFromMeasuredProfile
d_SignatureFromMeasuredProfile_72 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_SignatureFromMeasuredProfile_72 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant.SignatureFromMeasuredProfileUnique
d_SignatureFromMeasuredProfileUnique_76 ::
  T_Signature_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_SignatureFromMeasuredProfileUnique_76 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant._.h
d_h_84 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h_84 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant._.h
d_h_92 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h_92 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant._.h
d_h_100 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h_100 = erased
-- DASHI.Physics.OrbitSignatureDiscriminant._.h
d_h_108 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h_108 = erased

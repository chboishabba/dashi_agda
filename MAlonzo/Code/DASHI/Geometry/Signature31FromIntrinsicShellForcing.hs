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

module MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowOrientationAsymmetry
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowShellStratification
import qualified MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.ParallelogramLaw
import qualified MAlonzo.Code.DASHI.Geometry.SignatureExclusionFromOrbitProfile
import qualified MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong

-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.IntrinsicSignatureCoreAxioms
d_IntrinsicSignatureCoreAxioms_6 = ()
data T_IntrinsicSignatureCoreAxioms_6
  = C_IntrinsicSignatureCoreAxioms'46'constructor_3 MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78
                                                    MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.T_CausalSymmetryPackage_6
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.IntrinsicSignatureCoreAxioms.strengthenedContraction
d_strengthenedContraction_12 ::
  T_IntrinsicSignatureCoreAxioms_6 ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78
d_strengthenedContraction_12 v0
  = case coe v0 of
      C_IntrinsicSignatureCoreAxioms'46'constructor_3 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.IntrinsicSignatureCoreAxioms.causalSymmetry
d_causalSymmetry_14 ::
  T_IntrinsicSignatureCoreAxioms_6 ->
  MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.T_CausalSymmetryPackage_6
d_causalSymmetry_14 v0
  = case coe v0 of
      C_IntrinsicSignatureCoreAxioms'46'constructor_3 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.IntrinsicProfileWitness
d_IntrinsicProfileWitness_18 a0 = ()
data T_IntrinsicProfileWitness_18
  = C_IntrinsicProfileWitness'46'constructor_89 MAlonzo.Code.DASHI.Geometry.ConeArrowShellStratification.T_IntrinsicShellStratification_6
                                                MAlonzo.Code.DASHI.Geometry.ConeArrowOrientationAsymmetry.T_IntrinsicOrientation_6
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.IntrinsicProfileWitness.shellStratification
d_shellStratification_28 ::
  T_IntrinsicProfileWitness_18 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowShellStratification.T_IntrinsicShellStratification_6
d_shellStratification_28 v0
  = case coe v0 of
      C_IntrinsicProfileWitness'46'constructor_89 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.IntrinsicProfileWitness.orientation
d_orientation_30 ::
  T_IntrinsicProfileWitness_18 ->
  MAlonzo.Code.DASHI.Geometry.ConeArrowOrientationAsymmetry.T_IntrinsicOrientation_6
d_orientation_30 v0
  = case coe v0 of
      C_IntrinsicProfileWitness'46'constructor_89 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.IntrinsicProfileWitness.profileMatches31
d_profileMatches31_32 ::
  T_IntrinsicProfileWitness_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_profileMatches31_32 = erased
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.profileEqFromIntrinsic
d_profileEqFromIntrinsic_38 ::
  T_IntrinsicProfileWitness_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_profileEqFromIntrinsic_38 = erased
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.signature31-theoremFromIntrinsic
d_signature31'45'theoremFromIntrinsic_42 ::
  T_IntrinsicSignatureCoreAxioms_6 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
d_signature31'45'theoremFromIntrinsic_42 ~v0
  = du_signature31'45'theoremFromIntrinsic_42
du_signature31'45'theoremFromIntrinsic_42 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
du_signature31'45'theoremFromIntrinsic_42
  = coe
      MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.du_lorentz31'45'from'45'causal'45'axioms_440
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.profileSignatureLawFromIntrinsic
d_profileSignatureLawFromIntrinsic_48 ::
  T_IntrinsicSignatureCoreAxioms_6 ->
  T_IntrinsicProfileWitness_18 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
d_profileSignatureLawFromIntrinsic_48 ~v0 ~v1
  = du_profileSignatureLawFromIntrinsic_48
du_profileSignatureLawFromIntrinsic_48 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
du_profileSignatureLawFromIntrinsic_48
  = coe
      MAlonzo.Code.DASHI.Geometry.SignatureExclusionFromOrbitProfile.du_signatureLawFromProfileEq_8
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.signature31FromIntrinsic
d_signature31FromIntrinsic_52 ::
  T_IntrinsicSignatureCoreAxioms_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_signature31FromIntrinsic_52 ~v0 = du_signature31FromIntrinsic_52
du_signature31FromIntrinsic_52 ::
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
du_signature31FromIntrinsic_52
  = coe
      MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.du_signature31'45'from'45'causal'45'axioms_462
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing.lorentzLockFromIntrinsic
d_lorentzLockFromIntrinsic_70 ::
  T_IntrinsicSignatureCoreAxioms_6 ->
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.T_LorentzSignatureLock_90
d_lorentzLockFromIntrinsic_70 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_lorentzLockFromIntrinsic_70
du_lorentzLockFromIntrinsic_70 ::
  MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.T_LorentzSignatureLock_90
du_lorentzLockFromIntrinsic_70
  = coe
      MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.du_lorentzSignatureLockFromCausalAxioms_416

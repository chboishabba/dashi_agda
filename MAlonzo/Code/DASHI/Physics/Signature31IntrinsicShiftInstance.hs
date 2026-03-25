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

module MAlonzo.Code.DASHI.Physics.Signature31IntrinsicShiftInstance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowOrbitStructure
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowOrientationAsymmetry
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowShellStratification
import qualified MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.ParallelogramLaw
import qualified MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing
import qualified MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong
import qualified MAlonzo.Code.DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration

-- DASHI.Physics.Signature31IntrinsicShiftInstance.shiftShellStratification
d_shiftShellStratification_6 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowShellStratification.T_IntrinsicShellStratification_6
d_shiftShellStratification_6
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeArrowShellStratification.C_IntrinsicShellStratification'46'constructor_13
      (coe
         MAlonzo.Code.DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.d_shell1Derived_10)
      (coe
         MAlonzo.Code.DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.d_shell2Derived_12)
-- DASHI.Physics.Signature31IntrinsicShiftInstance.shiftOrbitStructure
d_shiftOrbitStructure_8 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowOrbitStructure.T_IntrinsicOrbitStructure_6
d_shiftOrbitStructure_8
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeArrowOrbitStructure.d_buildIntrinsicOrbitStructure_12
      (coe d_shiftShellStratification_6)
-- DASHI.Physics.Signature31IntrinsicShiftInstance.shiftOrientation
d_shiftOrientation_10 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowOrientationAsymmetry.T_IntrinsicOrientation_6
d_shiftOrientation_10
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeArrowOrientationAsymmetry.C_IntrinsicOrientation'46'constructor_23
      (31 :: Integer)
-- DASHI.Physics.Signature31IntrinsicShiftInstance.shiftProfileMatches31
d_shiftProfileMatches31_12 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shiftProfileMatches31_12 = erased
-- DASHI.Physics.Signature31IntrinsicShiftInstance.shiftIntrinsicCoreAxioms
d_shiftIntrinsicCoreAxioms_26 ::
  MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.T_IntrinsicSignatureCoreAxioms_6
d_shiftIntrinsicCoreAxioms_26
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.C_IntrinsicSignatureCoreAxioms'46'constructor_3
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.d_canonicalNontrivialInvariantStrong_218)
      (coe
         MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.C_CausalSymmetryPackage'46'constructor_43
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- DASHI.Physics.Signature31IntrinsicShiftInstance.shiftProfileWitness
d_shiftProfileWitness_28 ::
  MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.T_IntrinsicProfileWitness_18
d_shiftProfileWitness_28
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.C_IntrinsicProfileWitness'46'constructor_89
      d_shiftShellStratification_6 d_shiftOrientation_10
-- DASHI.Physics.Signature31IntrinsicShiftInstance.profileEq
d_profileEq_30 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_profileEq_30 = erased
-- DASHI.Physics.Signature31IntrinsicShiftInstance.signature31-theorem
d_signature31'45'theorem_32 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
d_signature31'45'theorem_32
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.du_signature31'45'theoremFromIntrinsic_42
-- DASHI.Physics.Signature31IntrinsicShiftInstance.signature31
d_signature31_34 ::
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_signature31_34
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.du_signature31FromIntrinsic_52
-- DASHI.Physics.Signature31IntrinsicShiftInstance.lorentzLock
d_lorentzLock_48 ::
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.T_LorentzSignatureLock_90
d_lorentzLock_48 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_lorentzLock_48
du_lorentzLock_48 ::
  MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.T_LorentzSignatureLock_90
du_lorentzLock_48
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.du_lorentzLockFromIntrinsic_70

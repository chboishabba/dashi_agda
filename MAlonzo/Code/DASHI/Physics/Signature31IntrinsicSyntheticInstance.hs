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

module MAlonzo.Code.DASHI.Physics.Signature31IntrinsicSyntheticInstance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31
import qualified MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong
import qualified MAlonzo.Code.DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness

-- DASHI.Physics.Signature31IntrinsicSyntheticInstance.syntheticIntrinsicCoreAxioms
d_syntheticIntrinsicCoreAxioms_6 ::
  MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.T_IntrinsicSignatureCoreAxioms_6
d_syntheticIntrinsicCoreAxioms_6
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.C_IntrinsicSignatureCoreAxioms'46'constructor_3
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.d_canonicalIdentityInvariantStrong_198
         (coe (4 :: Integer)))
      (coe
         MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31.C_CausalSymmetryPackage'46'constructor_43
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- DASHI.Physics.Signature31IntrinsicSyntheticInstance.syntheticLabel
d_syntheticLabel_8 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_syntheticLabel_8
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness.d_label_24
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness.d_syntheticDynamicsWitness_36)

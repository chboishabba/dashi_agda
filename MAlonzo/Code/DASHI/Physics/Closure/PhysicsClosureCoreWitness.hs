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

module MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintClosureWitness
import qualified MAlonzo.Code.DASHI.Physics.Closure.ClosureObservableWitness
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem
import qualified MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosure
import qualified MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureWitness
import qualified MAlonzo.Code.DASHI.Physics.Closure.ExecutionAdmissibilityWitness
import qualified MAlonzo.Code.DASHI.Physics.Closure.QQuadraticToCliffordBridgeTheorem
import qualified MAlonzo.Code.DASHI.Physics.RealClosureKit
import qualified MAlonzo.Code.DASHI.Physics.Signature31Canonical
import qualified MAlonzo.Code.DASHI.Physics.UniversalityTheorem

-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness
d_PhysicsClosureCoreWitness_8 = ()
data T_PhysicsClosureCoreWitness_8
  = C_PhysicsClosureCoreWitness'46'constructor_327 MAlonzo.Code.DASHI.Physics.RealClosureKit.T_RealClosureKit_6
                                                   MAlonzo.Code.DASHI.Physics.UniversalityTheorem.T_Universality_10
                                                   MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78
                                                   MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.T_ContractionQuadraticToSignatureBridgeTheorem_8
                                                   MAlonzo.Code.DASHI.Physics.Closure.QQuadraticToCliffordBridgeTheorem.T_QuadraticToCliffordBridgeTheorem_204
                                                   MAlonzo.Code.DASHI.Physics.Signature31Canonical.T_IntrinsicCoreProvider_14
                                                   MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintClosureWitness.T_CanonicalConstraintClosureWitness_8
                                                   MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosure.T_DynamicalClosure_8
                                                   MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureWitness.T_DynamicalClosureWitness_8
                                                   MAlonzo.Code.DASHI.Physics.Closure.ExecutionAdmissibilityWitness.T_SomeExecutionAdmissibilityWitness_104
                                                   MAlonzo.Code.DASHI.Physics.Closure.ExecutionAdmissibilityWitness.T_SomeFamilyClassificationWitness_114
                                                   MAlonzo.Code.DASHI.Physics.Closure.ClosureObservableWitness.T_ClosureObservableWitness_8
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.kit
d_kit_36 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.RealClosureKit.T_RealClosureKit_6
d_kit_36 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.universality
d_universality_38 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.UniversalityTheorem.T_Universality_10
d_universality_38 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.contractionQuadraticWitness
d_contractionQuadraticWitness_40 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78
d_contractionQuadraticWitness_40 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.contractionSignatureWitness
d_contractionSignatureWitness_42 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.T_ContractionQuadraticToSignatureBridgeTheorem_8
d_contractionSignatureWitness_42 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.quadraticCliffordWitness
d_quadraticCliffordWitness_44 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.QQuadraticToCliffordBridgeTheorem.T_QuadraticToCliffordBridgeTheorem_204
d_quadraticCliffordWitness_44 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.signatureCoreProvider
d_signatureCoreProvider_46 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Signature31Canonical.T_IntrinsicCoreProvider_14
d_signatureCoreProvider_46 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.constraintClosureWitness
d_constraintClosureWitness_48 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintClosureWitness.T_CanonicalConstraintClosureWitness_8
d_constraintClosureWitness_48 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.dynamics
d_dynamics_50 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosure.T_DynamicalClosure_8
d_dynamics_50 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.dynamicsWitness
d_dynamicsWitness_52 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureWitness.T_DynamicalClosureWitness_8
d_dynamicsWitness_52 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.executionAdmissibilityWitness
d_executionAdmissibilityWitness_54 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.ExecutionAdmissibilityWitness.T_SomeExecutionAdmissibilityWitness_104
d_executionAdmissibilityWitness_54 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.familyClassificationWitness
d_familyClassificationWitness_56 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.ExecutionAdmissibilityWitness.T_SomeFamilyClassificationWitness_114
d_familyClassificationWitness_56 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.observables
d_observables_58 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.ClosureObservableWitness.T_ClosureObservableWitness_8
d_observables_58 v0
  = case coe v0 of
      C_PhysicsClosureCoreWitness'46'constructor_327 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.observableSignatureAgreement
d_observableSignatureAgreement_60 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_observableSignatureAgreement_60 = erased
-- DASHI.Physics.Closure.PhysicsClosureCoreWitness.PhysicsClosureCoreWitness.closureSignature
d_closureSignature_62 ::
  T_PhysicsClosureCoreWitness_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_closureSignature_62 ~v0 = du_closureSignature_62
du_closureSignature_62 ::
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
du_closureSignature_62
  = coe
      MAlonzo.Code.DASHI.Physics.Signature31Canonical.du_signature31FromProvider_32

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

module MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureFull where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31
import qualified MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintClosureWitness
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem
import qualified MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosure
import qualified MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureWitness
import qualified MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift
import qualified MAlonzo.Code.DASHI.Physics.Closure.OrthogonalityZ90ZLift
import qualified MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Bracket
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Closure
import qualified MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Generators
import qualified MAlonzo.Code.DASHI.Physics.RealClosureKit
import qualified MAlonzo.Code.DASHI.Physics.Signature31Canonical
import qualified MAlonzo.Code.DASHI.Physics.UniversalityTheorem
import qualified MAlonzo.Code.MDL.Core

-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull
d_PhysicsClosureFull_8 = ()
data T_PhysicsClosureFull_8
  = C_PhysicsClosureFull'46'constructor_1079 MAlonzo.Code.DASHI.Physics.RealClosureKit.T_RealClosureKit_6
                                             (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                              MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                              MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
                                              MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
                                              MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.T_ProjectionDefectParallelogramPackage_14 ->
                                              MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                                             (Integer ->
                                              MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44)
                                             (Integer ->
                                              MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14)
                                             (Integer ->
                                              MAlonzo.Code.DASHI.Physics.Closure.OrthogonalityZ90ZLift.T_OrthogonalityZLift_10)
                                             MAlonzo.Code.DASHI.Physics.Signature31Canonical.T_IntrinsicCoreProvider_14
                                             MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
                                             MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
                                             MAlonzo.Code.DASHI.Physics.Constraints.Generators.T_ConstraintSystem_8
                                             MAlonzo.Code.DASHI.Physics.Constraints.Bracket.T_LieLike_10
                                             MAlonzo.Code.DASHI.Physics.Constraints.Closure.T_ClosureLaw_12
                                             (Integer ->
                                              Integer -> MAlonzo.Code.MDL.Core.T_Lyapunov_116)
                                             MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift.T_MDLFejerAxiomsShift_28
                                             MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosure.T_DynamicalClosure_8
                                             MAlonzo.Code.DASHI.Physics.UniversalityTheorem.T_Universality_10
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.kit
d_kit_62 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.DASHI.Physics.RealClosureKit.T_RealClosureKit_6
d_kit_62 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.metricEmergence
d_metricEmergence_76 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_Additive_8 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_ScalarField_8 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.T_ProjectionDefectParallelogramPackage_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_metricEmergence_76 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.quadraticFormZ
d_quadraticFormZ_80 ::
  T_PhysicsClosureFull_8 ->
  Integer ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
d_quadraticFormZ_80 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.polarizationZ
d_polarizationZ_84 ::
  T_PhysicsClosureFull_8 ->
  Integer ->
  MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14
d_polarizationZ_84 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.orthogonalityZ
d_orthogonalityZ_88 ::
  T_PhysicsClosureFull_8 ->
  Integer ->
  MAlonzo.Code.DASHI.Physics.Closure.OrthogonalityZ90ZLift.T_OrthogonalityZLift_10
d_orthogonalityZ_88 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.signatureCoreProvider
d_signatureCoreProvider_90 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.DASHI.Physics.Signature31Canonical.T_IntrinsicCoreProvider_14
d_signatureCoreProvider_90 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.signature31Theorem
d_signature31Theorem_92 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
d_signature31Theorem_92 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.signature31
d_signature31_94 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_signature31_94 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.CS
d_CS_96 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.DASHI.Physics.Constraints.Generators.T_ConstraintSystem_8
d_CS_96 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.L
d_L_98 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.DASHI.Physics.Constraints.Bracket.T_LieLike_10
d_L_98 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.constraintClosure
d_constraintClosure_100 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.DASHI.Physics.Constraints.Closure.T_ClosureLaw_12
d_constraintClosure_100 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.mdlLyap
d_mdlLyap_106 ::
  T_PhysicsClosureFull_8 ->
  Integer -> Integer -> MAlonzo.Code.MDL.Core.T_Lyapunov_116
d_mdlLyap_106 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.mdlFejer
d_mdlFejer_108 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift.T_MDLFejerAxiomsShift_28
d_mdlFejer_108 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.dynamics
d_dynamics_110 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosure.T_DynamicalClosure_8
d_dynamics_110 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.PhysicsClosureFull.universality
d_universality_112 ::
  T_PhysicsClosureFull_8 ->
  MAlonzo.Code.DASHI.Physics.UniversalityTheorem.T_Universality_10
d_universality_112 v0
  = case coe v0 of
      C_PhysicsClosureFull'46'constructor_1079 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.canonicalContractionQuadraticTheorem
d_canonicalContractionQuadraticTheorem_114 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.T_ContractionForcesQuadraticTheorem_26
d_canonicalContractionQuadraticTheorem_114
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.d_canonicalRealStackContractionForcesQuadraticTheorem_146
-- DASHI.Physics.Closure.PhysicsClosureFull.canonicalContractionQuadraticToSignatureBridge
d_canonicalContractionQuadraticToSignatureBridge_116 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.T_ContractionQuadraticToSignatureBridgeTheorem_8
d_canonicalContractionQuadraticToSignatureBridge_116
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.d_canonicalContractionQuadraticToSignatureBridgeTheorem_50
-- DASHI.Physics.Closure.PhysicsClosureFull.LegacyExternalInputs
d_LegacyExternalInputs_118 = ()
data T_LegacyExternalInputs_118
  = C_LegacyExternalInputs'46'constructor_1935 MAlonzo.Code.DASHI.Physics.RealClosureKit.T_RealClosureKit_6
                                               (Integer ->
                                                MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14)
                                               (Integer ->
                                                MAlonzo.Code.DASHI.Physics.Closure.OrthogonalityZ90ZLift.T_OrthogonalityZLift_10)
                                               MAlonzo.Code.DASHI.Physics.Signature31Canonical.T_IntrinsicCoreProvider_14
                                               (Integer ->
                                                Integer -> MAlonzo.Code.MDL.Core.T_Lyapunov_116)
                                               MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift.T_MDLFejerAxiomsShift_28
                                               MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosure.T_DynamicalClosure_8
                                               MAlonzo.Code.DASHI.Physics.UniversalityTheorem.T_Universality_10
-- DASHI.Physics.Closure.PhysicsClosureFull.LegacyExternalInputs.kit
d_kit_144 ::
  T_LegacyExternalInputs_118 ->
  MAlonzo.Code.DASHI.Physics.RealClosureKit.T_RealClosureKit_6
d_kit_144 v0
  = case coe v0 of
      C_LegacyExternalInputs'46'constructor_1935 v1 v2 v3 v4 v5 v6 v7 v8
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.LegacyExternalInputs.polarizationZ
d_polarizationZ_148 ::
  T_LegacyExternalInputs_118 ->
  Integer ->
  MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14
d_polarizationZ_148 v0
  = case coe v0 of
      C_LegacyExternalInputs'46'constructor_1935 v1 v2 v3 v4 v5 v6 v7 v8
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.LegacyExternalInputs.orthogonalityZ
d_orthogonalityZ_152 ::
  T_LegacyExternalInputs_118 ->
  Integer ->
  MAlonzo.Code.DASHI.Physics.Closure.OrthogonalityZ90ZLift.T_OrthogonalityZLift_10
d_orthogonalityZ_152 v0
  = case coe v0 of
      C_LegacyExternalInputs'46'constructor_1935 v1 v2 v3 v4 v5 v6 v7 v8
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.LegacyExternalInputs.signatureCoreProvider
d_signatureCoreProvider_154 ::
  T_LegacyExternalInputs_118 ->
  MAlonzo.Code.DASHI.Physics.Signature31Canonical.T_IntrinsicCoreProvider_14
d_signatureCoreProvider_154 v0
  = case coe v0 of
      C_LegacyExternalInputs'46'constructor_1935 v1 v2 v3 v4 v5 v6 v7 v8
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.LegacyExternalInputs.mdlLyap
d_mdlLyap_160 ::
  T_LegacyExternalInputs_118 ->
  Integer -> Integer -> MAlonzo.Code.MDL.Core.T_Lyapunov_116
d_mdlLyap_160 v0
  = case coe v0 of
      C_LegacyExternalInputs'46'constructor_1935 v1 v2 v3 v4 v5 v6 v7 v8
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.LegacyExternalInputs.mdlFejer
d_mdlFejer_162 ::
  T_LegacyExternalInputs_118 ->
  MAlonzo.Code.DASHI.Physics.Closure.MDLFejerAxiomsShift.T_MDLFejerAxiomsShift_28
d_mdlFejer_162 v0
  = case coe v0 of
      C_LegacyExternalInputs'46'constructor_1935 v1 v2 v3 v4 v5 v6 v7 v8
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.LegacyExternalInputs.dynamics
d_dynamics_164 ::
  T_LegacyExternalInputs_118 ->
  MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosure.T_DynamicalClosure_8
d_dynamics_164 v0
  = case coe v0 of
      C_LegacyExternalInputs'46'constructor_1935 v1 v2 v3 v4 v5 v6 v7 v8
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.LegacyExternalInputs.universality
d_universality_166 ::
  T_LegacyExternalInputs_118 ->
  MAlonzo.Code.DASHI.Physics.UniversalityTheorem.T_Universality_10
d_universality_166 v0
  = case coe v0 of
      C_LegacyExternalInputs'46'constructor_1935 v1 v2 v3 v4 v5 v6 v7 v8
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.PhysicsClosureFull.physicsClosureFullFromLegacyExternal
d_physicsClosureFullFromLegacyExternal_168 ::
  T_LegacyExternalInputs_118 -> T_PhysicsClosureFull_8
d_physicsClosureFullFromLegacyExternal_168 v0
  = coe
      C_PhysicsClosureFull'46'constructor_1079 (coe d_kit_144 (coe v0))
      (\ v1 v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.du_quadraticFromProjectionDefect_86
           v5)
      (coe
         (\ v1 ->
            MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.d_derivedQuadratic_52
              (coe
                 MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.d_canonicalContractionForcesQuadraticTheorem_122
                 (coe v1))))
      (coe d_polarizationZ_148 (coe v0))
      (coe d_orthogonalityZ_152 (coe v0))
      (coe d_signatureCoreProvider_154 (coe v0))
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31Canonical.du_signature31'45'theoremFromProvider_28)
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31Canonical.du_signature31FromProvider_32)
      (coe
         MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.d_CS_16)
      (coe
         MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.d_L_26)
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintClosureWitness.d_closureWitness_24
         (coe
            MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintClosureWitness.d_canonicalConstraintClosureWitness_26))
      (coe d_mdlLyap_160 (coe v0)) (coe d_mdlFejer_162 (coe v0))
      (coe d_dynamics_164 (coe v0)) (coe d_universality_166 (coe v0))
-- DASHI.Physics.Closure.PhysicsClosureFull.physicsClosureFullFromCoreWitness
d_physicsClosureFullFromCoreWitness_188 ::
  MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness.T_PhysicsClosureCoreWitness_8 ->
  T_PhysicsClosureFull_8
d_physicsClosureFullFromCoreWitness_188 v0
  = coe
      C_PhysicsClosureFull'46'constructor_1079
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness.d_kit_36
         (coe v0))
      (\ v1 v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.du_quadraticFromProjectionDefect_86
           v5)
      (coe
         (\ v1 ->
            MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.d_derivedQuadratic_52
              (coe
                 MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.d_canonicalContractionForcesQuadraticTheorem_122
                 (coe v1))))
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureWitness.d_effectiveGeometryPolarization_64
         (coe
            MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness.d_dynamicsWitness_52
            (coe v0)))
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureWitness.d_effectiveGeometryOrthogonality_60
         (coe
            MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness.d_dynamicsWitness_52
            (coe v0)))
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness.d_signatureCoreProvider_46
         (coe v0))
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31Canonical.du_signature31'45'theoremFromProvider_28)
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31Canonical.du_signature31FromProvider_32)
      (coe
         MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.d_CS_16)
      (coe
         MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.d_L_26)
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintClosureWitness.d_closureWitness_24
         (coe
            MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintClosureWitness.d_canonicalConstraintClosureWitness_26))
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureWitness.d_monotoneLyapunov_54
         (coe
            MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness.d_dynamicsWitness_52
            (coe v0)))
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureWitness.d_monotoneFejer_56
         (coe
            MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness.d_dynamicsWitness_52
            (coe v0)))
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness.d_dynamics_50
         (coe v0))
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.PhysicsClosureCoreWitness.d_universality_38
         (coe v0))

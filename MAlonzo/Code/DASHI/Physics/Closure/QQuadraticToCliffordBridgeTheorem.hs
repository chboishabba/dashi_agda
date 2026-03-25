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

module MAlonzo.Code.DASHI.Physics.Closure.QQuadraticToCliffordBridgeTheorem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.DASHI.Geometry.CliffordGate
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticPolarization
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.CanonicalCarrier
d_CanonicalCarrier_10 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
  ()
d_CanonicalCarrier_10 = erased
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.quadraticToBilinear
d_quadraticToBilinear_16 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.DASHI.Geometry.CliffordGate.T_BilinearForm_14
d_quadraticToBilinear_16 ~v0 = du_quadraticToBilinear_16
du_quadraticToBilinear_16 ::
  MAlonzo.Code.DASHI.Geometry.CliffordGate.T_BilinearForm_14
du_quadraticToBilinear_16
  = coe
      MAlonzo.Code.DASHI.Geometry.CliffordGate.C_BilinearForm'46'constructor_31
      (coe
         (\ v0 v1 ->
            coe
              MAlonzo.Code.DASHI.Geometry.QQuadraticForm.d__'43's__26
              MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_ScalarFieldℤ_154
              (coe
                 MAlonzo.Code.DASHI.Geometry.QQuadraticForm.d__'43's__26
                 MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_ScalarFieldℤ_154
                 (coe
                    MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du_Q'770'core_186
                    (coe
                       MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du__'43''7525'__118
                       v0 v1))
                 (coe
                    MAlonzo.Code.DASHI.Geometry.QQuadraticForm.d_'45's__34
                    MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_ScalarFieldℤ_154
                    (coe
                       MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du_Q'770'core_186
                       (coe v0))))
              (coe
                 MAlonzo.Code.DASHI.Geometry.QQuadraticForm.d_'45's__34
                 MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_ScalarFieldℤ_154
                 (coe
                    MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du_Q'770'core_186
                    (coe v1)))))
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.TargetAlgebra
d_TargetAlgebra_30 a0 a1 a2 = ()
newtype T_TargetAlgebra_30
  = C_TargetAlgebra'46'constructor_347 AgdaAny
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.TargetAlgebra.CarrierT
d_CarrierT_42 :: T_TargetAlgebra_30 -> ()
d_CarrierT_42 = erased
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.TargetAlgebra.unitT
d_unitT_44 :: T_TargetAlgebra_30 -> AgdaAny
d_unitT_44 v0
  = case coe v0 of
      C_TargetAlgebra'46'constructor_347 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.RelationRespectingMap
d_RelationRespectingMap_54 a0 a1 a2 a3 = ()
newtype T_RelationRespectingMap_54
  = C_RelationRespectingMap'46'constructor_869 (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
                                                AgdaAny)
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.RelationRespectingMap.onGenerators
d_onGenerators_70 ::
  T_RelationRespectingMap_54 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_onGenerators_70 v0
  = case coe v0 of
      C_RelationRespectingMap'46'constructor_869 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.RelationRespectingMap.generatorsCollapse
d_generatorsCollapse_74 ::
  T_RelationRespectingMap_54 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_generatorsCollapse_74 = erased
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.FactorizationWitness
d_FactorizationWitness_88 a0 a1 a2 a3 a4 a5 = ()
newtype T_FactorizationWitness_88
  = C_FactorizationWitness'46'constructor_2473 (AgdaAny -> AgdaAny)
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.FactorizationWitness.factor
d_factor_108 :: T_FactorizationWitness_88 -> AgdaAny -> AgdaAny
d_factor_108 v0
  = case coe v0 of
      C_FactorizationWitness'46'constructor_2473 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.FactorizationWitness.factorOnGenerators
d_factorOnGenerators_112 ::
  T_FactorizationWitness_88 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_factorOnGenerators_112 = erased
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.UniversalFactorization
d_UniversalFactorization_122 a0 a1 a2 a3 = ()
newtype T_UniversalFactorization_122
  = C_UniversalFactorization'46'constructor_3395 (T_TargetAlgebra_30 ->
                                                  T_RelationRespectingMap_54 ->
                                                  T_FactorizationWitness_88)
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.UniversalFactorization.factorize
d_factorize_152 ::
  T_UniversalFactorization_122 ->
  T_TargetAlgebra_30 ->
  T_RelationRespectingMap_54 -> T_FactorizationWitness_88
d_factorize_152 v0
  = case coe v0 of
      C_UniversalFactorization'46'constructor_3395 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.UniversalFactorization.factorUniqueSeam
d_factorUniqueSeam_162 ::
  T_UniversalFactorization_122 ->
  T_TargetAlgebra_30 ->
  T_RelationRespectingMap_54 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_factorUniqueSeam_162 = erased
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.CliffordPresentation
d_CliffordPresentation_166 a0 = ()
data T_CliffordPresentation_166
  = C_CliffordPresentation'46'constructor_5029 MAlonzo.Code.DASHI.Geometry.CliffordGate.T_RingLike_32
                                               MAlonzo.Code.DASHI.Geometry.CliffordGate.T_BilinearForm_14
                                               MAlonzo.Code.DASHI.Geometry.CliffordGate.T_CliffordAlgebra_72
                                               T_UniversalFactorization_122
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.CliffordPresentation.ringLike
d_ringLike_182 ::
  T_CliffordPresentation_166 ->
  MAlonzo.Code.DASHI.Geometry.CliffordGate.T_RingLike_32
d_ringLike_182 v0
  = case coe v0 of
      C_CliffordPresentation'46'constructor_5029 v1 v2 v3 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.CliffordPresentation.bilinear
d_bilinear_184 ::
  T_CliffordPresentation_166 ->
  MAlonzo.Code.DASHI.Geometry.CliffordGate.T_BilinearForm_14
d_bilinear_184 v0
  = case coe v0 of
      C_CliffordPresentation'46'constructor_5029 v1 v2 v3 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.CliffordPresentation.clifford
d_clifford_186 ::
  T_CliffordPresentation_166 ->
  MAlonzo.Code.DASHI.Geometry.CliffordGate.T_CliffordAlgebra_72
d_clifford_186 v0
  = case coe v0 of
      C_CliffordPresentation'46'constructor_5029 v1 v2 v3 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.CliffordPresentation.relationWitness
d_relationWitness_190 ::
  T_CliffordPresentation_166 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_relationWitness_190 = erased
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.CliffordPresentation.universalFactorization
d_universalFactorization_192 ::
  T_CliffordPresentation_166 -> T_UniversalFactorization_122
d_universalFactorization_192 v0
  = case coe v0 of
      C_CliffordPresentation'46'constructor_5029 v1 v2 v3 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.Quadratic⇒Clifford
d_Quadratic'8658'Clifford_194 = ()
newtype T_Quadratic'8658'Clifford_194
  = C_Quadratic'8658'Clifford'46'constructor_5153 (MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
                                                   T_CliffordPresentation_166)
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.Quadratic⇒Clifford.build
d_build_202 ::
  T_Quadratic'8658'Clifford_194 ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
  T_CliffordPresentation_166
d_build_202 v0
  = case coe v0 of
      C_Quadratic'8658'Clifford'46'constructor_5153 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.QuadraticToCliffordBridgeTheorem
d_QuadraticToCliffordBridgeTheorem_204 = ()
data T_QuadraticToCliffordBridgeTheorem_204
  = C_QuadraticToCliffordBridgeTheorem'46'constructor_5345 MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78
                                                           MAlonzo.Code.DASHI.Geometry.CliffordGate.T_BilinearForm_14
                                                           T_Quadratic'8658'Clifford_194
                                                           T_CliffordPresentation_166
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.QuadraticToCliffordBridgeTheorem.strengthenedContraction
d_strengthenedContraction_218 ::
  T_QuadraticToCliffordBridgeTheorem_204 ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78
d_strengthenedContraction_218 v0
  = case coe v0 of
      C_QuadraticToCliffordBridgeTheorem'46'constructor_5345 v1 v3 v4 v5
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.QuadraticToCliffordBridgeTheorem.normalizedQuadratic
d_normalizedQuadratic_222 ::
  T_QuadraticToCliffordBridgeTheorem_204 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalizedQuadratic_222 = erased
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.QuadraticToCliffordBridgeTheorem.quadraticToBilinearCanonical
d_quadraticToBilinearCanonical_224 ::
  T_QuadraticToCliffordBridgeTheorem_204 ->
  MAlonzo.Code.DASHI.Geometry.CliffordGate.T_BilinearForm_14
d_quadraticToBilinearCanonical_224 v0
  = case coe v0 of
      C_QuadraticToCliffordBridgeTheorem'46'constructor_5345 v1 v3 v4 v5
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.QuadraticToCliffordBridgeTheorem.quadraticToClifford
d_quadraticToClifford_226 ::
  T_QuadraticToCliffordBridgeTheorem_204 ->
  T_Quadratic'8658'Clifford_194
d_quadraticToClifford_226 v0
  = case coe v0 of
      C_QuadraticToCliffordBridgeTheorem'46'constructor_5345 v1 v3 v4 v5
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.QuadraticToCliffordBridgeTheorem.canonicalPresentation
d_canonicalPresentation_228 ::
  T_QuadraticToCliffordBridgeTheorem_204 ->
  T_CliffordPresentation_166
d_canonicalPresentation_228 v0
  = case coe v0 of
      C_QuadraticToCliffordBridgeTheorem'46'constructor_5345 v1 v3 v4 v5
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.canonicalQuadraticToClifford
d_canonicalQuadraticToClifford_230 :: T_Quadratic'8658'Clifford_194
d_canonicalQuadraticToClifford_230
  = coe
      C_Quadratic'8658'Clifford'46'constructor_5153
      (coe
         (\ v0 ->
            coe
              C_CliffordPresentation'46'constructor_5029
              (coe
                 MAlonzo.Code.DASHI.Geometry.CliffordGate.C_RingLike'46'constructor_163
                 (coe
                    MAlonzo.Code.DASHI.Geometry.QQuadraticForm.d__'43's__26
                    (coe
                       MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_ScalarFieldℤ_154))
                 (coe
                    MAlonzo.Code.DASHI.Geometry.QQuadraticForm.d__'42's__28
                    (coe
                       MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_ScalarFieldℤ_154))
                 (coe
                    MAlonzo.Code.DASHI.Geometry.QQuadraticForm.d_'45's__34
                    (coe
                       MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_ScalarFieldℤ_154))
                 (coe
                    MAlonzo.Code.DASHI.Geometry.QQuadraticForm.d_0s_30
                    (coe
                       MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_ScalarFieldℤ_154))
                 (coe
                    MAlonzo.Code.DASHI.Geometry.QQuadraticForm.d_1s_32
                    (coe
                       MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_ScalarFieldℤ_154)))
              (coe du_quadraticToBilinear_16)
              (coe
                 MAlonzo.Code.DASHI.Geometry.CliffordGate.C_CliffordAlgebra'46'constructor_1227
                 (\ v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                 (\ v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                 (\ v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
              (coe
                 C_UniversalFactorization'46'constructor_3395
                 (\ v1 v2 ->
                    coe
                      C_FactorizationWitness'46'constructor_2473
                      (\ v3 -> d_unitT_44 (coe v1))))))
-- DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem.canonicalQuadraticToCliffordBridgeTheorem
d_canonicalQuadraticToCliffordBridgeTheorem_266 ::
  T_QuadraticToCliffordBridgeTheorem_204
d_canonicalQuadraticToCliffordBridgeTheorem_266
  = coe
      C_QuadraticToCliffordBridgeTheorem'46'constructor_5345
      MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.d_canonicalNontrivialInvariantStrong_218
      (coe du_quadraticToBilinear_16) d_canonicalQuadraticToClifford_230
      (coe
         d_build_202 d_canonicalQuadraticToClifford_230
         MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.d_canonicalNontrivialInvariantStrong_218)

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

module MAlonzo.Code.DASHI.Geometry.CausalForcesLorentz31 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.ParallelogramLaw
import qualified MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Geometry.CausalForcesLorentz31.CausalSymmetryPackage
d_CausalSymmetryPackage_6 = ()
data T_CausalSymmetryPackage_6
  = C_CausalSymmetryPackage'46'constructor_43 MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
                                              MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
                                              MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
                                              MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
                                              MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
                                              MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
                                              MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
-- DASHI.Geometry.CausalForcesLorentz31.CausalSymmetryPackage.coneNontrivial
d_coneNontrivial_22 ::
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_coneNontrivial_22 v0
  = case coe v0 of
      C_CausalSymmetryPackage'46'constructor_43 v1 v2 v3 v4 v5 v6 v7
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CausalForcesLorentz31.CausalSymmetryPackage.arrowOrientation
d_arrowOrientation_24 ::
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_arrowOrientation_24 v0
  = case coe v0 of
      C_CausalSymmetryPackage'46'constructor_43 v1 v2 v3 v4 v5 v6 v7
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CausalForcesLorentz31.CausalSymmetryPackage.isotropyWitness
d_isotropyWitness_26 ::
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_isotropyWitness_26 v0
  = case coe v0 of
      C_CausalSymmetryPackage'46'constructor_43 v1 v2 v3 v4 v5 v6 v7
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CausalForcesLorentz31.CausalSymmetryPackage.finiteSpeedWitness
d_finiteSpeedWitness_28 ::
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_finiteSpeedWitness_28 v0
  = case coe v0 of
      C_CausalSymmetryPackage'46'constructor_43 v1 v2 v3 v4 v5 v6 v7
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CausalForcesLorentz31.CausalSymmetryPackage.involutionWitness
d_involutionWitness_30 ::
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_involutionWitness_30 v0
  = case coe v0 of
      C_CausalSymmetryPackage'46'constructor_43 v1 v2 v3 v4 v5 v6 v7
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CausalForcesLorentz31.CausalSymmetryPackage.nondegenerateQuadratic
d_nondegenerateQuadratic_32 ::
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_nondegenerateQuadratic_32 v0
  = case coe v0 of
      C_CausalSymmetryPackage'46'constructor_43 v1 v2 v3 v4 v5 v6 v7
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CausalForcesLorentz31.CausalSymmetryPackage.quotientContractionWitness
d_quotientContractionWitness_34 ::
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_quotientContractionWitness_34 v0
  = case coe v0 of
      C_CausalSymmetryPackage'46'constructor_43 v1 v2 v3 v4 v5 v6 v7
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CausalForcesLorentz31.AdmissibleSignature
d_AdmissibleSignature_36 a0 = ()
data T_AdmissibleSignature_36 = C_admissible31_38
-- DASHI.Geometry.CausalForcesLorentz31.RivalSignature
d_RivalSignature_40 = ()
data T_RivalSignature_40 = C_sig40_42 | C_sig22_44 | C_sig04_46
-- DASHI.Geometry.CausalForcesLorentz31.rivalAsSU
d_rivalAsSU_48 ::
  T_RivalSignature_40 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature_6
d_rivalAsSU_48 v0
  = coe
      seq (coe v0)
      (coe MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.C_other_12)
-- DASHI.Geometry.CausalForcesLorentz31.uniqueLorentz31
d_uniqueLorentz31_52 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature_6 ->
  T_AdmissibleSignature_36 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uniqueLorentz31_52 = erased
-- DASHI.Geometry.CausalForcesLorentz31.nonAdmissibleSig13
d_nonAdmissibleSig13_54 ::
  T_AdmissibleSignature_36 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nonAdmissibleSig13_54 = erased
-- DASHI.Geometry.CausalForcesLorentz31.nonAdmissibleOther
d_nonAdmissibleOther_56 ::
  T_AdmissibleSignature_36 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nonAdmissibleOther_56 = erased
-- DASHI.Geometry.CausalForcesLorentz31.nonAdmissibleRival
d_nonAdmissibleRival_60 ::
  T_RivalSignature_40 ->
  T_AdmissibleSignature_36 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nonAdmissibleRival_60 = erased
-- DASHI.Geometry.CausalForcesLorentz31.CausalClassification
d_CausalClassification_62 = ()
newtype T_CausalClassification_62
  = C_CausalClassification'46'constructor_605 MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
-- DASHI.Geometry.CausalForcesLorentz31.CausalClassification.law
d_law_68 ::
  T_CausalClassification_62 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
d_law_68 v0
  = case coe v0 of
      C_CausalClassification'46'constructor_605 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CausalForcesLorentz31.CausalClassification.admissibleLaw
d_admissibleLaw_70 ::
  T_CausalClassification_62 -> T_AdmissibleSignature_36
d_admissibleLaw_70 = erased
-- DASHI.Geometry.CausalForcesLorentz31.packageAdmissibleSignature
d_packageAdmissibleSignature_76 ::
  T_CausalSymmetryPackage_6 -> () -> T_AdmissibleSignature_36
d_packageAdmissibleSignature_76 = erased
-- DASHI.Geometry.CausalForcesLorentz31.LorentzSignatureLock
d_LorentzSignatureLock_90 = ()
newtype T_LorentzSignatureLock_90
  = C_LorentzSignatureLock'46'constructor_933 MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
-- DASHI.Geometry.CausalForcesLorentz31.LorentzSignatureLock.witness31
d_witness31_108 ::
  T_LorentzSignatureLock_90 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
d_witness31_108 v0
  = case coe v0 of
      C_LorentzSignatureLock'46'constructor_933 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CausalForcesLorentz31.LorentzSignatureLock.admissible31Witness
d_admissible31Witness_110 ::
  T_LorentzSignatureLock_90 -> T_AdmissibleSignature_36
d_admissible31Witness_110 = erased
-- DASHI.Geometry.CausalForcesLorentz31.LorentzSignatureLock.unique31
d_unique31_114 ::
  T_LorentzSignatureLock_90 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature_6 ->
  T_AdmissibleSignature_36 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique31_114 = erased
-- DASHI.Geometry.CausalForcesLorentz31.LorentzSignatureLock.rejectSig13
d_rejectSig13_116 ::
  T_LorentzSignatureLock_90 ->
  T_AdmissibleSignature_36 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rejectSig13_116 = erased
-- DASHI.Geometry.CausalForcesLorentz31.LorentzSignatureLock.rejectOther
d_rejectOther_118 ::
  T_LorentzSignatureLock_90 ->
  T_AdmissibleSignature_36 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rejectOther_118 = erased
-- DASHI.Geometry.CausalForcesLorentz31.LorentzSignatureLock.rejectRival
d_rejectRival_122 ::
  T_LorentzSignatureLock_90 ->
  T_RivalSignature_40 ->
  T_AdmissibleSignature_36 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rejectRival_122 = erased
-- DASHI.Geometry.CausalForcesLorentz31.normalizedQuadraticFromStrong
d_normalizedQuadraticFromStrong_128 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalizedQuadraticFromStrong_128 = erased
-- DASHI.Geometry.CausalForcesLorentz31.coneArrowEvidence
d_coneArrowEvidence_142 ::
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_coneArrowEvidence_142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_coneArrowEvidence_142
du_coneArrowEvidence_142 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_coneArrowEvidence_142
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- DASHI.Geometry.CausalForcesLorentz31.isotropyArrowEvidence
d_isotropyArrowEvidence_176 ::
  T_CausalSymmetryPackage_6 ->
  () -> () -> () -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_isotropyArrowEvidence_176 ~v0 ~v1 ~v2 ~v3
  = du_isotropyArrowEvidence_176
du_isotropyArrowEvidence_176 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_isotropyArrowEvidence_176
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- DASHI.Geometry.CausalForcesLorentz31.causalClassificationFromEvidence
d_causalClassificationFromEvidence_208 ::
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () -> T_CausalSymmetryPackage_6 -> T_CausalClassification_62
d_causalClassificationFromEvidence_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_causalClassificationFromEvidence_208
du_causalClassificationFromEvidence_208 ::
  T_CausalClassification_62
du_causalClassificationFromEvidence_208
  = coe
      C_CausalClassification'46'constructor_605
      (coe
         MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.C_SignatureLaw'46'constructor_1
         (coe MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.C_sig31_8))
-- DASHI.Geometry.CausalForcesLorentz31.eliminateEuclideanAndDegenerate
d_eliminateEuclideanAndDegenerate_236 ::
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () -> T_CausalSymmetryPackage_6 -> T_CausalClassification_62
d_eliminateEuclideanAndDegenerate_236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_eliminateEuclideanAndDegenerate_236
du_eliminateEuclideanAndDegenerate_236 :: T_CausalClassification_62
du_eliminateEuclideanAndDegenerate_236
  = coe du_causalClassificationFromEvidence_208
-- DASHI.Geometry.CausalForcesLorentz31.spatialIsotropyAndArrowForce31
d_spatialIsotropyAndArrowForce31_256 ::
  () ->
  () ->
  () ->
  T_CausalSymmetryPackage_6 ->
  T_CausalClassification_62 -> T_CausalClassification_62
d_spatialIsotropyAndArrowForce31_256 ~v0 ~v1 ~v2 ~v3 v4
  = du_spatialIsotropyAndArrowForce31_256 v4
du_spatialIsotropyAndArrowForce31_256 ::
  T_CausalClassification_62 -> T_CausalClassification_62
du_spatialIsotropyAndArrowForce31_256 v0 = coe v0
-- DASHI.Geometry.CausalForcesLorentz31.quadraticConeIsotropyClassification
d_quadraticConeIsotropyClassification_284 ::
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () ->
  () -> () -> T_CausalSymmetryPackage_6 -> T_CausalClassification_62
d_quadraticConeIsotropyClassification_284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                          ~v6 ~v7
  = du_quadraticConeIsotropyClassification_284
du_quadraticConeIsotropyClassification_284 ::
  T_CausalClassification_62
du_quadraticConeIsotropyClassification_284
  = coe du_eliminateEuclideanAndDegenerate_236
-- DASHI.Geometry.CausalForcesLorentz31.quadraticConeIsotropyForces31
d_quadraticConeIsotropyForces31_314 ::
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () ->
  () ->
  () ->
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
d_quadraticConeIsotropyForces31_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_quadraticConeIsotropyForces31_314
du_quadraticConeIsotropyForces31_314 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
du_quadraticConeIsotropyForces31_314
  = coe d_law_68 (coe du_quadraticConeIsotropyClassification_284)
-- DASHI.Geometry.CausalForcesLorentz31.normalizedCoreClassification
d_normalizedCoreClassification_346 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () -> () -> () -> T_CausalClassification_62
d_normalizedCoreClassification_346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8
  = du_normalizedCoreClassification_346
du_normalizedCoreClassification_346 :: T_CausalClassification_62
du_normalizedCoreClassification_346
  = coe du_quadraticConeIsotropyClassification_284
-- DASHI.Geometry.CausalForcesLorentz31.normalizedCoreClassifies31
d_normalizedCoreClassifies31_382 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
d_normalizedCoreClassifies31_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8
  = du_normalizedCoreClassifies31_382
du_normalizedCoreClassifies31_382 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_SignatureLaw_14
du_normalizedCoreClassifies31_382
  = coe d_law_68 (coe du_normalizedCoreClassification_346)
-- DASHI.Geometry.CausalForcesLorentz31.lorentzSignatureLockFromCausalAxioms
d_lorentzSignatureLockFromCausalAxioms_416 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.DASHI.Geometry.ParallelogramLaw.T_AdditiveSpace_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Quadratic_38 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_Cone_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeMetricCompatibility.T_ConeMetricCompat_72 ->
  () -> () -> () -> T_LorentzSignatureLock_90
d_lorentzSignatureLockFromCausalAxioms_416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6 ~v7 ~v8
  = du_lorentzSignatureLockFromCausalAxioms_416
du_lorentzSignatureLockFromCausalAxioms_416 ::
  T_LorentzSignatureLock_90
du_lorentzSignatureLockFromCausalAxioms_416
  = coe
      C_LorentzSignatureLock'46'constructor_933
      (d_law_68 (coe du_normalizedCoreClassification_346))
-- DASHI.Geometry.CausalForcesLorentz31.lorentz31-from-causal-axioms
d_lorentz31'45'from'45'causal'45'axioms_440 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
d_lorentz31'45'from'45'causal'45'axioms_440 ~v0 ~v1
  = du_lorentz31'45'from'45'causal'45'axioms_440
du_lorentz31'45'from'45'causal'45'axioms_440 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
du_lorentz31'45'from'45'causal'45'axioms_440
  = coe
      MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.C_Signature31Theorem'46'constructor_57
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 ->
            d_witness31_108 (coe du_lorentzSignatureLockFromCausalAxioms_416)))
-- DASHI.Geometry.CausalForcesLorentz31.signature31-from-causal-axioms
d_signature31'45'from'45'causal'45'axioms_462 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
  T_CausalSymmetryPackage_6 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_signature31'45'from'45'causal'45'axioms_462 ~v0 ~v1
  = du_signature31'45'from'45'causal'45'axioms_462
du_signature31'45'from'45'causal'45'axioms_462 ::
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
du_signature31'45'from'45'causal'45'axioms_462
  = coe MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_sig31_288

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

module MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.CanonicalQuadraticOutput
d_CanonicalQuadraticOutput_10 a0 = ()
newtype T_CanonicalQuadraticOutput_10
  = C_CanonicalQuadraticOutput'46'constructor_183 MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.CanonicalQuadraticOutput.quadratic
d_quadratic_20 ::
  T_CanonicalQuadraticOutput_10 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
d_quadratic_20 v0
  = case coe v0 of
      C_CanonicalQuadraticOutput'46'constructor_183 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.CanonicalQuadraticOutput.normalize
d_normalize_24 ::
  T_CanonicalQuadraticOutput_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalize_24 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.ContractionForcesQuadraticTheorem
d_ContractionForcesQuadraticTheorem_26 = ()
data T_ContractionForcesQuadraticTheorem_26
  = C_ContractionForcesQuadraticTheorem'46'constructor_711 Integer
                                                           MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_ProjectionDefect_32
                                                           MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.T_ProjectionDefectParallelogramPackage_14
                                                           MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
                                                           MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
                                                           MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.ContractionForcesQuadraticTheorem.dimension
d_dimension_46 :: T_ContractionForcesQuadraticTheorem_26 -> Integer
d_dimension_46 v0
  = case coe v0 of
      C_ContractionForcesQuadraticTheorem'46'constructor_711 v1 v2 v3 v4 v6 v7
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.ContractionForcesQuadraticTheorem.projection
d_projection_48 ::
  T_ContractionForcesQuadraticTheorem_26 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefect.T_ProjectionDefect_32
d_projection_48 v0
  = case coe v0 of
      C_ContractionForcesQuadraticTheorem'46'constructor_711 v1 v2 v3 v4 v6 v7
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.ContractionForcesQuadraticTheorem.projectionParallelogram
d_projectionParallelogram_50 ::
  T_ContractionForcesQuadraticTheorem_26 ->
  MAlonzo.Code.DASHI.Geometry.ProjectionDefectToParallelogram.T_ProjectionDefectParallelogramPackage_14
d_projectionParallelogram_50 v0
  = case coe v0 of
      C_ContractionForcesQuadraticTheorem'46'constructor_711 v1 v2 v3 v4 v6 v7
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.ContractionForcesQuadraticTheorem.derivedQuadratic
d_derivedQuadratic_52 ::
  T_ContractionForcesQuadraticTheorem_26 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
d_derivedQuadratic_52 v0
  = case coe v0 of
      C_ContractionForcesQuadraticTheorem'46'constructor_711 v1 v2 v3 v4 v6 v7
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.ContractionForcesQuadraticTheorem.normalizedQuadratic
d_normalizedQuadratic_56 ::
  T_ContractionForcesQuadraticTheorem_26 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalizedQuadratic_56 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.ContractionForcesQuadraticTheorem.signature31Theorem
d_signature31Theorem_58 ::
  T_ContractionForcesQuadraticTheorem_26 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
d_signature31Theorem_58 v0
  = case coe v0 of
      C_ContractionForcesQuadraticTheorem'46'constructor_711 v1 v2 v3 v4 v6 v7
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.ContractionForcesQuadraticTheorem.signature31Value
d_signature31Value_60 ::
  T_ContractionForcesQuadraticTheorem_26 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_signature31Value_60 v0
  = case coe v0 of
      C_ContractionForcesQuadraticTheorem'46'constructor_711 v1 v2 v3 v4 v6 v7
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.ContractionForcesQuadraticTheorem.signatureForced31
d_signatureForced31_62 ::
  T_ContractionForcesQuadraticTheorem_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_signatureForced31_62 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.ContractionForcesQuadraticTheorem.canonicalOutput
d_canonicalOutput_64 ::
  T_ContractionForcesQuadraticTheorem_26 ->
  T_CanonicalQuadraticOutput_10
d_canonicalOutput_64 v0
  = coe
      C_CanonicalQuadraticOutput'46'constructor_183
      (d_derivedQuadratic_52 (coe v0))
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.canonicalSignature31Theorem
d_canonicalSignature31Theorem_66 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
d_canonicalSignature31Theorem_66
  = coe
      MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.C_Signature31Theorem'46'constructor_57
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.C_SignatureLaw'46'constructor_1
              (coe MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.C_sig31_8)))
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.fromStrongContraction
d_fromStrongContraction_82 ::
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78 ->
  T_ContractionForcesQuadraticTheorem_26
d_fromStrongContraction_82 v0
  = coe
      C_ContractionForcesQuadraticTheorem'46'constructor_711
      (MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.d_dimension_102
         (coe v0))
      (MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.d_projection_104
         (coe v0))
      (MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.d_projectionParallelogram_106
         (coe v0))
      (MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.d_derivedQuadratic_110
         (coe v0))
      d_canonicalSignature31Theorem_66
      (coe MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_sig31_288)
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.CanonicalContractionQuadraticStability
d_CanonicalContractionQuadraticStability_86 = ()
newtype T_CanonicalContractionQuadraticStability_86
  = C_CanonicalContractionQuadraticStability'46'constructor_1289 MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.CanonicalContractionQuadraticStability.strengthenedSource
d_strengthenedSource_100 ::
  T_CanonicalContractionQuadraticStability_86 ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78
d_strengthenedSource_100 v0
  = case coe v0 of
      C_CanonicalContractionQuadraticStability'46'constructor_1289 v1
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.CanonicalContractionQuadraticStability.theoremSurface
d_theoremSurface_102 ::
  T_CanonicalContractionQuadraticStability_86 ->
  T_ContractionForcesQuadraticTheorem_26
d_theoremSurface_102 v0
  = coe
      d_fromStrongContraction_82 (coe d_strengthenedSource_100 (coe v0))
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.CanonicalContractionQuadraticStability.quadraticTransportStable
d_quadraticTransportStable_106 ::
  T_CanonicalContractionQuadraticStability_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_quadraticTransportStable_106 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.CanonicalContractionQuadraticStability.canonicalNormalizationStable
d_canonicalNormalizationStable_110 ::
  T_CanonicalContractionQuadraticStability_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_canonicalNormalizationStable_110 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.canonicalContractionQuadraticStability
d_canonicalContractionQuadraticStability_112 ::
  T_CanonicalContractionQuadraticStability_86
d_canonicalContractionQuadraticStability_112
  = coe
      C_CanonicalContractionQuadraticStability'46'constructor_1289
      MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.d_canonicalNontrivialInvariantStrong_218
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.canonicalContractionForcesQuadraticTheorem
d_canonicalContractionForcesQuadraticTheorem_122 ::
  Integer -> T_ContractionForcesQuadraticTheorem_26
d_canonicalContractionForcesQuadraticTheorem_122 v0
  = coe
      d_fromStrongContraction_82
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.d_canonicalIdentityInvariantStrong_198
         (coe v0))
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.canonicalOutputAgreement
d_canonicalOutputAgreement_136 ::
  T_ContractionForcesQuadraticTheorem_26 ->
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44 ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_UniqueUpToScaleSeam_12 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_canonicalOutputAgreement_136 = erased
-- DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.canonicalRealStackContractionForcesQuadraticTheorem
d_canonicalRealStackContractionForcesQuadraticTheorem_146 ::
  T_ContractionForcesQuadraticTheorem_26
d_canonicalRealStackContractionForcesQuadraticTheorem_146
  = coe
      d_theoremSurface_102
      (coe d_canonicalContractionQuadraticStability_112)

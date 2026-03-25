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

module MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing
import qualified MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem
import qualified MAlonzo.Code.DASHI.Physics.Signature31Canonical
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.ContractionQuadraticToSignatureBridgeTheorem
d_ContractionQuadraticToSignatureBridgeTheorem_8 = ()
data T_ContractionQuadraticToSignatureBridgeTheorem_8
  = C_ContractionQuadraticToSignatureBridgeTheorem'46'constructor_397 MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.T_ContractionForcesQuadraticTheorem_26
                                                                      MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78
                                                                      MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
                                                                      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
-- DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.ContractionQuadraticToSignatureBridgeTheorem.contractionForcesQuadraticTheorem
d_contractionForcesQuadraticTheorem_24 ::
  T_ContractionQuadraticToSignatureBridgeTheorem_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.T_ContractionForcesQuadraticTheorem_26
d_contractionForcesQuadraticTheorem_24 v0
  = case coe v0 of
      C_ContractionQuadraticToSignatureBridgeTheorem'46'constructor_397 v1 v2 v3 v4
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
d_strengthenedContraction_26 ::
  T_ContractionQuadraticToSignatureBridgeTheorem_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticStrong.T_ContractionForcesQuadraticStrong_78
d_strengthenedContraction_26 v0
  = case coe v0 of
      C_ContractionQuadraticToSignatureBridgeTheorem'46'constructor_397 v1 v2 v3 v4
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.ContractionQuadraticToSignatureBridgeTheorem.signature31Theorem
d_signature31Theorem_28 ::
  T_ContractionQuadraticToSignatureBridgeTheorem_8 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
d_signature31Theorem_28 v0
  = case coe v0 of
      C_ContractionQuadraticToSignatureBridgeTheorem'46'constructor_397 v1 v2 v3 v4
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.ContractionQuadraticToSignatureBridgeTheorem.signature31Value
d_signature31Value_30 ::
  T_ContractionQuadraticToSignatureBridgeTheorem_8 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_signature31Value_30 v0
  = case coe v0 of
      C_ContractionQuadraticToSignatureBridgeTheorem'46'constructor_397 v1 v2 v3 v4
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.ContractionQuadraticToSignatureBridgeTheorem.signatureForced31
d_signatureForced31_32 ::
  T_ContractionQuadraticToSignatureBridgeTheorem_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_signatureForced31_32 = erased
-- DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.ContractionQuadraticToSignatureBridgeTheorem.normalizedQuadratic
d_normalizedQuadratic_36 ::
  T_ContractionQuadraticToSignatureBridgeTheorem_8 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalizedQuadratic_36 = erased
-- DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.contractionQuadraticToSignatureBridgeFromIntrinsicCore
d_contractionQuadraticToSignatureBridgeFromIntrinsicCore_40 ::
  MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.T_IntrinsicSignatureCoreAxioms_6 ->
  T_ContractionQuadraticToSignatureBridgeTheorem_8
d_contractionQuadraticToSignatureBridgeFromIntrinsicCore_40 v0
  = coe
      C_ContractionQuadraticToSignatureBridgeTheorem'46'constructor_397
      (MAlonzo.Code.DASHI.Physics.Closure.ContractionForcesQuadraticTheorem.d_fromStrongContraction_82
         (coe
            MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.d_strengthenedContraction_12
            (coe v0)))
      (MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.d_strengthenedContraction_12
         (coe v0))
      (coe
         MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.du_signature31'45'theoremFromIntrinsic_42)
      (coe
         MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.du_signature31FromIntrinsic_52)
-- DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.contractionQuadraticToSignatureBridgeFromProvider
d_contractionQuadraticToSignatureBridgeFromProvider_46 ::
  MAlonzo.Code.DASHI.Physics.Signature31Canonical.T_IntrinsicCoreProvider_14 ->
  T_ContractionQuadraticToSignatureBridgeTheorem_8
d_contractionQuadraticToSignatureBridgeFromProvider_46 v0
  = coe
      d_contractionQuadraticToSignatureBridgeFromIntrinsicCore_40
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31Canonical.d_coreAxioms_26
         (coe v0))
-- DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.canonicalContractionQuadraticToSignatureBridgeTheorem
d_canonicalContractionQuadraticToSignatureBridgeTheorem_50 ::
  T_ContractionQuadraticToSignatureBridgeTheorem_8
d_canonicalContractionQuadraticToSignatureBridgeTheorem_50
  = coe
      d_contractionQuadraticToSignatureBridgeFromProvider_46
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31Canonical.d_shiftCoreProvider_36)

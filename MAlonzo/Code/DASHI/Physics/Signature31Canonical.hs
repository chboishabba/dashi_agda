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

module MAlonzo.Code.DASHI.Physics.Signature31Canonical where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing
import qualified MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31
import qualified MAlonzo.Code.DASHI.Physics.Signature31IntrinsicRootSystemB4Instance
import qualified MAlonzo.Code.DASHI.Physics.Signature31IntrinsicShiftInstance
import qualified MAlonzo.Code.DASHI.Physics.Signature31IntrinsicSyntheticInstance

-- DASHI.Physics.Signature31Canonical.IntrinsicCoreProviderSource
d_IntrinsicCoreProviderSource_6 = ()
data T_IntrinsicCoreProviderSource_6
  = C_shiftOrbitProfileSource_8 | C_syntheticOneMinusSource_10 |
    C_rootSystemB4Source_12
-- DASHI.Physics.Signature31Canonical.IntrinsicCoreProvider
d_IntrinsicCoreProvider_14 = ()
data T_IntrinsicCoreProvider_14
  = C_IntrinsicCoreProvider'46'constructor_7 T_IntrinsicCoreProviderSource_6
                                             MAlonzo.Code.Agda.Builtin.String.T_String_6
                                             MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.T_IntrinsicSignatureCoreAxioms_6
-- DASHI.Physics.Signature31Canonical.IntrinsicCoreProvider.providerSource
d_providerSource_22 ::
  T_IntrinsicCoreProvider_14 -> T_IntrinsicCoreProviderSource_6
d_providerSource_22 v0
  = case coe v0 of
      C_IntrinsicCoreProvider'46'constructor_7 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Signature31Canonical.IntrinsicCoreProvider.providerLabel
d_providerLabel_24 ::
  T_IntrinsicCoreProvider_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_providerLabel_24 v0
  = case coe v0 of
      C_IntrinsicCoreProvider'46'constructor_7 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Signature31Canonical.IntrinsicCoreProvider.coreAxioms
d_coreAxioms_26 ::
  T_IntrinsicCoreProvider_14 ->
  MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.T_IntrinsicSignatureCoreAxioms_6
d_coreAxioms_26 v0
  = case coe v0 of
      C_IntrinsicCoreProvider'46'constructor_7 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Signature31Canonical.signature31-theoremFromProvider
d_signature31'45'theoremFromProvider_28 ::
  T_IntrinsicCoreProvider_14 ->
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
d_signature31'45'theoremFromProvider_28 ~v0
  = du_signature31'45'theoremFromProvider_28
du_signature31'45'theoremFromProvider_28 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
du_signature31'45'theoremFromProvider_28
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.du_signature31'45'theoremFromIntrinsic_42
-- DASHI.Physics.Signature31Canonical.signature31FromProvider
d_signature31FromProvider_32 ::
  T_IntrinsicCoreProvider_14 ->
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_signature31FromProvider_32 ~v0 = du_signature31FromProvider_32
du_signature31FromProvider_32 ::
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
du_signature31FromProvider_32
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.du_signature31FromIntrinsic_52
-- DASHI.Physics.Signature31Canonical.shiftCoreProvider
d_shiftCoreProvider_36 :: T_IntrinsicCoreProvider_14
d_shiftCoreProvider_36
  = coe
      C_IntrinsicCoreProvider'46'constructor_7
      (coe C_shiftOrbitProfileSource_8)
      (coe ("shift-intrinsic-core" :: Data.Text.Text))
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31IntrinsicShiftInstance.d_shiftIntrinsicCoreAxioms_26)
-- DASHI.Physics.Signature31Canonical.syntheticCoreProvider
d_syntheticCoreProvider_38 :: T_IntrinsicCoreProvider_14
d_syntheticCoreProvider_38
  = coe
      C_IntrinsicCoreProvider'46'constructor_7
      (coe C_syntheticOneMinusSource_10)
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31IntrinsicSyntheticInstance.d_syntheticLabel_8)
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31IntrinsicSyntheticInstance.d_syntheticIntrinsicCoreAxioms_6)
-- DASHI.Physics.Signature31Canonical.b4CoreProvider
d_b4CoreProvider_40 :: T_IntrinsicCoreProvider_14
d_b4CoreProvider_40
  = coe
      C_IntrinsicCoreProvider'46'constructor_7
      (coe C_rootSystemB4Source_12)
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31IntrinsicRootSystemB4Instance.d_b4Label_8)
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31IntrinsicRootSystemB4Instance.d_b4IntrinsicCoreAxioms_6)
-- DASHI.Physics.Signature31Canonical.canonicalCoreAxioms
d_canonicalCoreAxioms_42 ::
  MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.T_IntrinsicSignatureCoreAxioms_6
d_canonicalCoreAxioms_42
  = coe d_coreAxioms_26 (coe d_shiftCoreProvider_36)
-- DASHI.Physics.Signature31Canonical.canonicalProfileWitness
d_canonicalProfileWitness_44 ::
  MAlonzo.Code.DASHI.Geometry.Signature31FromIntrinsicShellForcing.T_IntrinsicProfileWitness_18
d_canonicalProfileWitness_44
  = coe
      MAlonzo.Code.DASHI.Physics.Signature31IntrinsicShiftInstance.d_shiftProfileWitness_28
-- DASHI.Physics.Signature31Canonical.signature31-theorem
d_signature31'45'theorem_46 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
d_signature31'45'theorem_46
  = coe du_signature31'45'theoremFromProvider_28
-- DASHI.Physics.Signature31Canonical.signature31
d_signature31_48 ::
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_signature31_48 = coe du_signature31FromProvider_32
-- DASHI.Physics.Signature31Canonical.syntheticSignature31-theorem
d_syntheticSignature31'45'theorem_50 ::
  MAlonzo.Code.DASHI.Geometry.SignatureUniqueness31.T_Signature31Theorem_20
d_syntheticSignature31'45'theorem_50
  = coe du_signature31'45'theoremFromProvider_28
-- DASHI.Physics.Signature31Canonical.syntheticSignature31
d_syntheticSignature31_52 ::
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_syntheticSignature31_52 = coe du_signature31FromProvider_32
-- DASHI.Physics.Signature31Canonical.syntheticSignatureMatchesCanonical
d_syntheticSignatureMatchesCanonical_54 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_syntheticSignatureMatchesCanonical_54 = erased

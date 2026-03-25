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

module MAlonzo.Code.DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyOrbitProfile
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction
import qualified MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellEnumeration
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Physics.Signature31InstanceShiftZ90Z

-- DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.shiftShellAction
d_shiftShellAction_6 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.T_AbstractShellAction_16
d_shiftShellAction_6
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellAction.du_buildShellAction_72
      (coe
         MAlonzo.Code.DASHI.Physics.Signature31InstanceShiftZ90Z.d_sigAxioms_858)
-- DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.shiftEnumeration
d_shiftEnumeration_8 ::
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_ShellOrbitEnumeration_262
d_shiftEnumeration_8
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyShellEnumeration.du_buildShellOrbitEnumerationFromShellAction_498
      (coe d_shiftShellAction_6)
-- DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.shell1Derived
d_shell1Derived_10 :: [Integer]
d_shell1Derived_10
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_shell1OrbitSizes_268
      (coe d_shiftEnumeration_8)
-- DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.shell2Derived
d_shell2Derived_12 :: [Integer]
d_shell2Derived_12
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.d_shell2OrbitSizes_270
      (coe d_shiftEnumeration_8)
-- DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.shell1Derived≡computed
d_shell1Derived'8801'computed_14 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shell1Derived'8801'computed_14 = erased
-- DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.shell2Derived≡computed
d_shell2Derived'8801'computed_16 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shell2Derived'8801'computed_16 = erased
-- DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.shiftEnumeration-shell1≡computed
d_shiftEnumeration'45'shell1'8801'computed_18 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shiftEnumeration'45'shell1'8801'computed_18 = erased
-- DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.shiftEnumeration-shell2≡computed
d_shiftEnumeration'45'shell2'8801'computed_20 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shiftEnumeration'45'shell2'8801'computed_20 = erased
-- DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.orientationTagDerived
d_orientationTagDerived_22 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_orientationTagDerived_22 = erased
-- DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration.shiftOrbitProfileDerivation
d_shiftOrbitProfileDerivation_24 ::
  MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyOrbitProfile.T_OrbitProfileDerivation_24
d_shiftOrbitProfileDerivation_24
  = coe
      MAlonzo.Code.DASHI.Geometry.ConeArrowIsotropyOrbitProfile.C_OrbitProfileDerivation'46'constructor_195
      (coe (31 :: Integer)) (coe d_shiftEnumeration_8)

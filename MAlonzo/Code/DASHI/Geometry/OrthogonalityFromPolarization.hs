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

module MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.DASHI.Energy.ClosestPoint
import qualified MAlonzo.Code.DASHI.Energy.Energy
import qualified MAlonzo.Code.DASHI.Geometry.ProjectionDefect
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm

-- DASHI.Geometry.OrthogonalityFromPolarization.Polarization
d_Polarization_14 a0 a1 a2 a3 = ()
data T_Polarization_14
  = C_Polarization'46'constructor_1095 (AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny
-- DASHI.Geometry.OrthogonalityFromPolarization.Polarization.Q
d_Q_38 :: T_Polarization_14 -> AgdaAny -> AgdaAny
d_Q_38 v0
  = case coe v0 of
      C_Polarization'46'constructor_1095 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.OrthogonalityFromPolarization.Polarization.⟪_,_⟫
d_'10218'_'44'_'10219'_40 ::
  T_Polarization_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_'10218'_'44'_'10219'_40 v0
  = case coe v0 of
      C_Polarization'46'constructor_1095 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.OrthogonalityFromPolarization.Polarization.two
d_two_42 :: T_Polarization_14 -> AgdaAny
d_two_42 v0
  = case coe v0 of
      C_Polarization'46'constructor_1095 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.OrthogonalityFromPolarization.Polarization.two-def
d_two'45'def_44 ::
  T_Polarization_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_two'45'def_44 = erased
-- DASHI.Geometry.OrthogonalityFromPolarization.Polarization.polarization
d_polarization_50 ::
  T_Polarization_14 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_polarization_50 = erased
-- DASHI.Geometry.OrthogonalityFromPolarization.OrthogonalityFromPolarization
d_OrthogonalityFromPolarization_70 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
newtype T_OrthogonalityFromPolarization_70
  = C_OrthogonalityFromPolarization'46'constructor_3469 (AgdaAny ->
                                                         AgdaAny)
-- DASHI.Geometry.OrthogonalityFromPolarization.OrthogonalityFromPolarization.Orth
d_Orth_102 ::
  T_OrthogonalityFromPolarization_70 -> AgdaAny -> AgdaAny -> ()
d_Orth_102 = erased
-- DASHI.Geometry.OrthogonalityFromPolarization.OrthogonalityFromPolarization.Orth-def
d_Orth'45'def_108 ::
  T_OrthogonalityFromPolarization_70 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Orth'45'def_108 = erased
-- DASHI.Geometry.OrthogonalityFromPolarization.OrthogonalityFromPolarization.orthPD
d_orthPD_112 ::
  T_OrthogonalityFromPolarization_70 -> AgdaAny -> AgdaAny
d_orthPD_112 v0
  = case coe v0 of
      C_OrthogonalityFromPolarization'46'constructor_3469 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError

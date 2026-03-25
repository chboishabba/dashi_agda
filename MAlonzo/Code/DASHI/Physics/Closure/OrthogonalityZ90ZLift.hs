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

module MAlonzo.Code.DASHI.Physics.Closure.OrthogonalityZ90ZLift where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticPolarizationCoreInstance
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Closure.OrthogonalityZLift.OrthogonalityZLift
d_OrthogonalityZLift_10 a0 = ()
data T_OrthogonalityZLift_10
  = C_OrthogonalityZLift'46'constructor_469 MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14
                                            (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny)
-- DASHI.Physics.Closure.OrthogonalityZLift.OrthogonalityZLift.pol
d_pol_32 ::
  T_OrthogonalityZLift_10 ->
  MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14
d_pol_32 v0
  = case coe v0 of
      C_OrthogonalityZLift'46'constructor_469 v1 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.OrthogonalityZLift.OrthogonalityZLift.Orth
d_Orth_34 ::
  T_OrthogonalityZLift_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> ()
d_Orth_34 = erased
-- DASHI.Physics.Closure.OrthogonalityZLift.OrthogonalityZLift.Orth-def
d_Orth'45'def_40 ::
  T_OrthogonalityZLift_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Orth'45'def_40 = erased
-- DASHI.Physics.Closure.OrthogonalityZLift.OrthogonalityZLift.orthPD
d_orthPD_44 ::
  T_OrthogonalityZLift_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_orthPD_44 v0
  = case coe v0 of
      C_OrthogonalityZLift'46'constructor_469 v1 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.OrthogonalityZLift.Dot-zeroL
d_Dot'45'zeroL_50 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Dot'45'zeroL_50 = erased
-- DASHI.Physics.Closure.OrthogonalityZLift.orthogonalityZLift
d_orthogonalityZLift_64 :: Integer -> T_OrthogonalityZLift_10
d_orthogonalityZLift_64 ~v0 = du_orthogonalityZLift_64
du_orthogonalityZLift_64 :: T_OrthogonalityZLift_10
du_orthogonalityZLift_64
  = coe
      C_OrthogonalityZLift'46'constructor_469
      (coe
         MAlonzo.Code.DASHI.Physics.QQuadraticPolarizationCoreInstance.du_polarizationCore_150)
      erased

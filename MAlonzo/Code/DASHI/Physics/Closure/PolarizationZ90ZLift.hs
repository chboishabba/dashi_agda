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

module MAlonzo.Code.DASHI.Physics.Closure.PolarizationZ90ZLift where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticPolarization

-- DASHI.Physics.Closure.PolarizationZLift.polarizationZLift
d_polarizationZLift_10 ::
  Integer ->
  MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14
d_polarizationZLift_10 ~v0 = du_polarizationZLift_10
du_polarizationZLift_10 ::
  MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.T_Polarization_14
du_polarizationZLift_10
  = coe
      MAlonzo.Code.DASHI.Geometry.OrthogonalityFromPolarization.C_Polarization'46'constructor_1095
      (coe
         MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du_Q'770'core_186)
      (coe MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du_dotℤ_122)
      (2 :: Integer)

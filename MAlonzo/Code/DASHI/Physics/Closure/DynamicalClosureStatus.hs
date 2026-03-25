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

module MAlonzo.Code.DASHI.Physics.Closure.DynamicalClosureStatus where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- DASHI.Physics.Closure.DynamicalClosureStatus.PropagationStatus
d_PropagationStatus_8 = ()
data T_PropagationStatus_8
  = C_fiberBackedPropagation_10 | C_strongerPropagationPending_12
-- DASHI.Physics.Closure.DynamicalClosureStatus.CausalAdmissibilityStatus
d_CausalAdmissibilityStatus_14 = ()
data T_CausalAdmissibilityStatus_14
  = C_seamBackedCausalAdmissibility_16 |
    C_strongerCausalAdmissibilityPending_18
-- DASHI.Physics.Closure.DynamicalClosureStatus.MonotoneQuantityStatus
d_MonotoneQuantityStatus_20 = ()
data T_MonotoneQuantityStatus_20
  = C_mdlLyapunovAndFejer_22 | C_strongerConservedQuantityPending_24
-- DASHI.Physics.Closure.DynamicalClosureStatus.EffectiveGeometryStatus
d_EffectiveGeometryStatus_26 = ()
data T_EffectiveGeometryStatus_26
  = C_quadraticPolarizationAndOrthogonality_28 |
    C_strongerGeometryPending_30
-- DASHI.Physics.Closure.DynamicalClosureStatus.DynamicalClosureStatus
d_DynamicalClosureStatus_32 = ()
data T_DynamicalClosureStatus_32
  = C_DynamicalClosureStatus'46'constructor_13 T_PropagationStatus_8
                                               T_CausalAdmissibilityStatus_14
                                               T_MonotoneQuantityStatus_20
                                               T_EffectiveGeometryStatus_26
-- DASHI.Physics.Closure.DynamicalClosureStatus.DynamicalClosureStatus.propagation
d_propagation_42 ::
  T_DynamicalClosureStatus_32 -> T_PropagationStatus_8
d_propagation_42 v0
  = case coe v0 of
      C_DynamicalClosureStatus'46'constructor_13 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosureStatus.DynamicalClosureStatus.causalAdmissibility
d_causalAdmissibility_44 ::
  T_DynamicalClosureStatus_32 -> T_CausalAdmissibilityStatus_14
d_causalAdmissibility_44 v0
  = case coe v0 of
      C_DynamicalClosureStatus'46'constructor_13 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosureStatus.DynamicalClosureStatus.monotoneQuantity
d_monotoneQuantity_46 ::
  T_DynamicalClosureStatus_32 -> T_MonotoneQuantityStatus_20
d_monotoneQuantity_46 v0
  = case coe v0 of
      C_DynamicalClosureStatus'46'constructor_13 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.DynamicalClosureStatus.DynamicalClosureStatus.effectiveGeometry
d_effectiveGeometry_48 ::
  T_DynamicalClosureStatus_32 -> T_EffectiveGeometryStatus_26
d_effectiveGeometry_48 v0
  = case coe v0 of
      C_DynamicalClosureStatus'46'constructor_13 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError

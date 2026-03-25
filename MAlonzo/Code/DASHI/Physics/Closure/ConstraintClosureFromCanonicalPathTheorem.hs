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

module MAlonzo.Code.DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage
import qualified MAlonzo.Code.DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage
import qualified MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem
import qualified MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem
import qualified MAlonzo.Code.DASHI.Physics.Closure.QQuadraticToCliffordBridgeTheorem
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Closure

-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem.CanonicalPathWitness
d_CanonicalPathWitness_8 = ()
data T_CanonicalPathWitness_8
  = C_CanonicalPathWitness'46'constructor_3 MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.T_ContractionQuadraticToSignatureBridgeTheorem_8
                                            MAlonzo.Code.DASHI.Physics.Closure.QQuadraticToCliffordBridgeTheorem.T_QuadraticToCliffordBridgeTheorem_204
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem.CanonicalPathWitness.contractionQuadraticToSignature
d_contractionQuadraticToSignature_14 ::
  T_CanonicalPathWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.T_ContractionQuadraticToSignatureBridgeTheorem_8
d_contractionQuadraticToSignature_14 v0
  = case coe v0 of
      C_CanonicalPathWitness'46'constructor_3 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem.CanonicalPathWitness.quadraticToClifford
d_quadraticToClifford_16 ::
  T_CanonicalPathWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.QQuadraticToCliffordBridgeTheorem.T_QuadraticToCliffordBridgeTheorem_204
d_quadraticToClifford_16 v0
  = case coe v0 of
      C_CanonicalPathWitness'46'constructor_3 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem.canonicalPathWitness
d_canonicalPathWitness_18 :: T_CanonicalPathWitness_8
d_canonicalPathWitness_18
  = coe
      C_CanonicalPathWitness'46'constructor_3
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem.d_canonicalContractionQuadraticToSignatureBridgeTheorem_50)
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.QQuadraticToCliffordBridgeTheorem.d_canonicalQuadraticToCliffordBridgeTheorem_266)
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem.closureFromCanonicalQuadraticSignatureDynamics
d_closureFromCanonicalQuadraticSignatureDynamics_22 ::
  T_CanonicalPathWitness_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.T_CanonicalConstraintGaugePackage_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.T_ConstraintClosureTransport_10 ->
  MAlonzo.Code.DASHI.Physics.Constraints.Closure.T_ClosureLaw_12
d_closureFromCanonicalQuadraticSignatureDynamics_22 ~v0 v1 v2
  = du_closureFromCanonicalQuadraticSignatureDynamics_22 v1 v2
du_closureFromCanonicalQuadraticSignatureDynamics_22 ::
  MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.T_CanonicalConstraintGaugePackage_8 ->
  MAlonzo.Code.DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.T_ConstraintClosureTransport_10 ->
  MAlonzo.Code.DASHI.Physics.Constraints.Closure.T_ClosureLaw_12
du_closureFromCanonicalQuadraticSignatureDynamics_22 v0 v1
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.d_transportedClosureLaw_44
      (coe v0) (coe v1)
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem.canonicalPathInducedConstraintClosure
d_canonicalPathInducedConstraintClosure_28 ::
  MAlonzo.Code.DASHI.Physics.Constraints.Closure.T_ClosureLaw_12
d_canonicalPathInducedConstraintClosure_28
  = coe
      du_closureFromCanonicalQuadraticSignatureDynamics_22
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_canonicalConstraintGaugePackage_44)
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.d_canonicalConstraintClosureTransport_64)

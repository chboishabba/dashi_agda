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

module MAlonzo.Code.DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage
import qualified MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem
import qualified MAlonzo.Code.DASHI.Physics.Constraints.Closure
import qualified MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance

-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.ConstraintClosureTransport
d_ConstraintClosureTransport_10 a0 = ()
data T_ConstraintClosureTransport_10
  = C_ConstraintClosureTransport'46'constructor_339 (MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.T_C_8 ->
                                                     AgdaAny)
                                                    (AgdaAny ->
                                                     MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.T_C_8)
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.ConstraintClosureTransport.lift
d_lift_28 ::
  T_ConstraintClosureTransport_10 ->
  MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.T_C_8 ->
  AgdaAny
d_lift_28 v0
  = case coe v0 of
      C_ConstraintClosureTransport'46'constructor_339 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.ConstraintClosureTransport.project
d_project_30 ::
  T_ConstraintClosureTransport_10 ->
  AgdaAny ->
  MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.T_C_8
d_project_30 v0
  = case coe v0 of
      C_ConstraintClosureTransport'46'constructor_339 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.ConstraintClosureTransport.project-lift
d_project'45'lift_34 ::
  T_ConstraintClosureTransport_10 ->
  MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.T_C_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_project'45'lift_34 = erased
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.ConstraintClosureTransport.bracket-compat
d_bracket'45'compat_40 ::
  T_ConstraintClosureTransport_10 ->
  MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.T_C_8 ->
  MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.T_C_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bracket'45'compat_40 = erased
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.transportedClosureLaw
d_transportedClosureLaw_44 ::
  MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.T_CanonicalConstraintGaugePackage_8 ->
  T_ConstraintClosureTransport_10 ->
  MAlonzo.Code.DASHI.Physics.Constraints.Closure.T_ClosureLaw_12
d_transportedClosureLaw_44 v0 v1
  = coe
      MAlonzo.Code.DASHI.Physics.Constraints.Closure.C_ClosureLaw'46'constructor_269
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 d_project_30 v1
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.d_closes_46
                       v0 (coe d_lift_28 v1 v2) (coe d_lift_28 v1 v3))))
              erased))
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.canonicalConstraintClosureTransport
d_canonicalConstraintClosureTransport_64 ::
  T_ConstraintClosureTransport_10
d_canonicalConstraintClosureTransport_64
  = coe
      C_ConstraintClosureTransport'46'constructor_339 (\ v0 -> v0)
      (\ v0 -> v0)
-- DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage.canonicalPackageInducedClosure
d_canonicalPackageInducedClosure_76 ::
  MAlonzo.Code.DASHI.Physics.Constraints.Closure.T_ClosureLaw_12
d_canonicalPackageInducedClosure_76
  = coe
      d_transportedClosureLaw_44
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_canonicalConstraintGaugePackage_44)
      (coe d_canonicalConstraintClosureTransport_64)

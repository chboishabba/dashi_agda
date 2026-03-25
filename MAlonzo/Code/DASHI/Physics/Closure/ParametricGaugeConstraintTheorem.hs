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

module MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Algebra.GaugeGroupContract
import qualified MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage
import qualified MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance

-- DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.ParametricGaugeConstraintTheorem
d_ParametricGaugeConstraintTheorem_10 a0 = ()
data T_ParametricGaugeConstraintTheorem_10
  = C_ParametricGaugeConstraintTheorem'46'constructor_385 MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.T_Emergence_14
                                                          (AgdaAny -> Bool)
                                                          MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.T_UniquenessClaim_24
-- DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.ParametricGaugeConstraintTheorem.emergence
d_emergence_26 ::
  T_ParametricGaugeConstraintTheorem_10 ->
  MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.T_Emergence_14
d_emergence_26 v0
  = case coe v0 of
      C_ParametricGaugeConstraintTheorem'46'constructor_385 v1 v2 v3
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.ParametricGaugeConstraintTheorem.admissibility
d_admissibility_28 ::
  T_ParametricGaugeConstraintTheorem_10 -> AgdaAny -> Bool
d_admissibility_28 v0
  = case coe v0 of
      C_ParametricGaugeConstraintTheorem'46'constructor_385 v1 v2 v3
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.ParametricGaugeConstraintTheorem.uniqueness
d_uniqueness_30 ::
  T_ParametricGaugeConstraintTheorem_10 ->
  MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.T_UniquenessClaim_24
d_uniqueness_30 v0
  = case coe v0 of
      C_ParametricGaugeConstraintTheorem'46'constructor_385 v1 v2 v3
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.ParametricGaugeConstraintTheorem.closurePreservesAdmissibility
d_closurePreservesAdmissibility_36 ::
  T_ParametricGaugeConstraintTheorem_10 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closurePreservesAdmissibility_36 = erased
-- DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.parametricGaugeConstraintTheorem
d_parametricGaugeConstraintTheorem_40 ::
  MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.T_CanonicalConstraintGaugePackage_8 ->
  T_ParametricGaugeConstraintTheorem_10
d_parametricGaugeConstraintTheorem_40 v0
  = coe
      C_ParametricGaugeConstraintTheorem'46'constructor_385
      (coe
         MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.C_Emergence'46'constructor_5
         (coe
            MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.d_pickGauge_56
            (coe v0)))
      (MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.d_admissible_48
         (coe v0))
      (coe
         MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.C_UniquenessClaim'46'constructor_221
         (coe
            MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.C_Emergence'46'constructor_5
            (coe
               MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.d_pickGauge_56
               (coe v0)))
         (MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.d_admissible_48
            (coe v0)))
-- DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.canonicalConstraintGaugePackage
d_canonicalConstraintGaugePackage_44 ::
  MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.T_CanonicalConstraintGaugePackage_8
d_canonicalConstraintGaugePackage_44
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.C_CanonicalConstraintGaugePackage'46'constructor_829
      MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.d_bracket_32
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
           (coe
              MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.d_bracket_32
              (coe v0) (coe v1))
           erased)
      (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (\ v0 ->
         coe
           MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.C_SU3'215'SU2'215'U1_8)
-- DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.canonicalParametricGaugeConstraintTheorem
d_canonicalParametricGaugeConstraintTheorem_66 ::
  T_ParametricGaugeConstraintTheorem_10
d_canonicalParametricGaugeConstraintTheorem_66
  = coe
      d_parametricGaugeConstraintTheorem_40
      (coe d_canonicalConstraintGaugePackage_44)

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

module MAlonzo.Code.DASHI.Physics.Closure.CanonicalGaugeContractTheorem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Algebra.GaugeGroupContract
import qualified MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem
import qualified MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance

-- DASHI.Physics.Closure.CanonicalGaugeContractTheorem.canonicalGaugeConstraintTheoremBase
d_canonicalGaugeConstraintTheoremBase_8 ::
  MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.T_ParametricGaugeConstraintTheorem_10
d_canonicalGaugeConstraintTheoremBase_8
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_parametricGaugeConstraintTheorem_40
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_canonicalConstraintGaugePackage_44)
-- DASHI.Physics.Closure.CanonicalGaugeContractTheorem.canonicalGaugeEmergence
d_canonicalGaugeEmergence_10 ::
  MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.T_Emergence_14
d_canonicalGaugeEmergence_10
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_emergence_26
      (coe d_canonicalGaugeConstraintTheoremBase_8)
-- DASHI.Physics.Closure.CanonicalGaugeContractTheorem.canonicalGaugeAdmissible
d_canonicalGaugeAdmissible_12 ::
  MAlonzo.Code.DASHI.Physics.Constraints.ConcreteInstance.T_C_8 ->
  Bool
d_canonicalGaugeAdmissible_12
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_admissibility_28
      (coe d_canonicalGaugeConstraintTheoremBase_8)
-- DASHI.Physics.Closure.CanonicalGaugeContractTheorem.canonicalGaugeContractTheorem
d_canonicalGaugeContractTheorem_14 ::
  MAlonzo.Code.DASHI.Algebra.GaugeGroupContract.T_UniquenessClaim_24
d_canonicalGaugeContractTheorem_14
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_uniqueness_30
      (coe d_canonicalGaugeConstraintTheoremBase_8)

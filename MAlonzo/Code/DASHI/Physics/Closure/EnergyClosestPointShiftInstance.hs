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

module MAlonzo.Code.DASHI.Physics.Closure.EnergyClosestPointShiftInstance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.DASHI.Energy.ClosestPoint
import qualified MAlonzo.Code.DASHI.Energy.FejerToClosestPoint
import qualified MAlonzo.Code.DASHI.Metric.AgreementUltrametric
import qualified MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric
import qualified MAlonzo.Code.DASHI.Physics.Closure.ClosestPointAxiomsShift
import qualified MAlonzo.Code.DASHI.Physics.RealOperatorStackShift
import qualified MAlonzo.Code.DASHI.Physics.TailCollapseProof
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd

-- DASHI.Physics.Closure.EnergyClosestPointShiftInstance.fejerShift
d_fejerShift_12 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_FejerMonotone_52
d_fejerShift_12 v0 v1
  = coe
      MAlonzo.Code.DASHI.Energy.ClosestPoint.C_FejerMonotone'46'constructor_1661
      (coe
         (\ v2 v3 v4 ->
            MAlonzo.Code.DASHI.Physics.RealOperatorStackShift.d_nonexp_122
              (coe v0) (coe v1) (coe v2) (coe v3)))
-- DASHI.Physics.Closure.EnergyClosestPointShiftInstance.fejer⇒closestShift
d_fejer'8658'closestShift_40 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fejer'8658'closestShift_40 v0 v1 v2 v3 ~v4
  = du_fejer'8658'closestShift_40 v0 v1 v2 v3
du_fejer'8658'closestShift_40 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fejer'8658'closestShift_40 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
      (coe
         MAlonzo.Code.DASHI.Metric.AgreementUltrametric.d_ultraNat_542
         (coe addInt (coe v0) (coe v1))
         (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
         (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v3)
         (coe
            MAlonzo.Code.Data.Vec.Base.du_reverse_616
            (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_P'7523'_158
               (coe v0) (coe v1) (coe v2))))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2822))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
            (coe MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4440))
         (coe
            MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine_36
            (coe addInt (coe v0) (coe v1)) (coe v2) (coe v3))
         (coe
            MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine_36
            (coe addInt (coe v0) (coe v1)) (coe v2) (coe v3))
         (coe
            MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine_36
            (coe addInt (coe v0) (coe v1)) (coe v3)
            (coe
               MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_P'7523'_158 (coe v0)
               (coe v1) (coe v2)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
            (coe
               MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine_36
               (coe addInt (coe v0) (coe v1)) (coe v2) (coe v3)))
         (coe
            MAlonzo.Code.DASHI.Physics.RealOperatorStackShift.d_nonexp_122
            (coe v0) (coe v1) (coe v2) (coe v3)))
-- DASHI.Physics.Closure.EnergyClosestPointShiftInstance.closestAxiomsShift
d_closestAxiomsShift_66 ::
  MAlonzo.Code.DASHI.Physics.Closure.ClosestPointAxiomsShift.T_ClosestPointAxiomsShift_8
d_closestAxiomsShift_66
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.ClosestPointAxiomsShift.C_ClosestPointAxiomsShift'46'constructor_61
      (coe
         (\ v0 v1 ->
            coe
              MAlonzo.Code.DASHI.Energy.FejerToClosestPoint.C_FejerClosestAxioms'46'constructor_1185
              (coe d_fejerShift_12 (coe v0) (coe v1))
              (\ v2 v3 v4 ->
                 coe du_fejer'8658'closestShift_40 (coe v0) (coe v1) v2 v3)))
-- DASHI.Physics.Closure.EnergyClosestPointShiftInstance.closestShift
d_closestShift_76 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_ClosestPoint_126
d_closestShift_76 v0 v1
  = coe
      MAlonzo.Code.DASHI.Energy.FejerToClosestPoint.du_closestFromFejer_62
      (coe
         MAlonzo.Code.DASHI.Physics.Closure.ClosestPointAxiomsShift.d_closestAxiomShift_20
         d_closestAxiomsShift_66 v0 v1)
-- DASHI.Physics.Closure.EnergyClosestPointShiftInstance.fejerImpliesClosestShift
d_fejerImpliesClosestShift_86 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Energy.ClosestPoint.T_FejerImpliesClosest_202
d_fejerImpliesClosestShift_86 v0 v1
  = coe
      MAlonzo.Code.DASHI.Energy.ClosestPoint.C_FejerImpliesClosest'46'constructor_5269
      (coe d_closestShift_76 (coe v0) (coe v1))

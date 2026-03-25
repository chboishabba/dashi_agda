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

module MAlonzo.Code.DASHI.Physics.RealOperatorStackShift where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Geometry.FiberContraction
import qualified MAlonzo.Code.DASHI.Geometry.StrictContractionComposition
import qualified MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric
import qualified MAlonzo.Code.DASHI.Physics.CanonicalizationMinimal
import qualified MAlonzo.Code.DASHI.Physics.TailCollapseProof
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.RealOperatorStackShift.C
d_C_10 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_C_10 v0 ~v1 = du_C_10 v0
du_C_10 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_C_10 v0
  = coe
      MAlonzo.Code.DASHI.Physics.CanonicalizationMinimal.du_C'7523'_16
      (coe v0)
-- DASHI.Physics.RealOperatorStackShift.P
d_P_20 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_P_20 v0 v1
  = coe
      MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_P'7523'_158 (coe v0)
      (coe v1)
-- DASHI.Physics.RealOperatorStackShift.R
d_R_30 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_R_30 v0 v1
  = coe
      MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_R'7523'_132 (coe v0)
      (coe v1)
-- DASHI.Physics.RealOperatorStackShift.nonexpC
d_nonexpC_40 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
d_nonexpC_40 v0 v1
  = coe
      MAlonzo.Code.DASHI.Physics.CanonicalizationMinimal.d_nonexpC'7523'_64
      (coe v0) (coe v1)
-- DASHI.Physics.RealOperatorStackShift.nonexpR
d_nonexpR_50 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
d_nonexpR_50 v0 v1
  = coe
      MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.C_NonExpansive'46'constructor_355
      (coe d_nonexp_64 (coe v0) (coe v1))
-- DASHI.Physics.RealOperatorStackShift._.nonexp
d_nonexp_64 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonexp_64 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
      (coe
         MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine'45''43''43''45'shiftTail'8804'_1362
         (coe v0) (coe v1)
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_coarseOf_82
            (coe v0) (coe v2))
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_coarseOf_82
            (coe v0) (coe v3))
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
            (coe v2))
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
            (coe v3)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
         (coe
            MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine_36
            (coe addInt (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
               (coe
                  MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_coarseOf_82
                  (coe v0) (coe v2))
               (coe
                  MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
                  (coe v2)))
            (coe
               MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
               (coe
                  MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_coarseOf_82
                  (coe v0) (coe v3))
               (coe
                  MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
                  (coe v3)))))
-- DASHI.Physics.RealOperatorStackShift.nonexpP
d_nonexpP_108 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
d_nonexpP_108 v0 v1
  = coe
      MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.C_NonExpansive'46'constructor_355
      (coe d_nonexp_122 (coe v0) (coe v1))
-- DASHI.Physics.RealOperatorStackShift._.nonexp
d_nonexp_122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonexp_122 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
      (coe
         MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine'45''43''43''45'projTail'8804'_1398
         (coe v0) (coe v1)
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_coarseOf_82
            (coe v0) (coe v2))
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_coarseOf_82
            (coe v0) (coe v3))
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
            (coe v2))
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
            (coe v3)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2772
         (coe
            MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine_36
            (coe addInt (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
               (coe
                  MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_coarseOf_82
                  (coe v0) (coe v2))
               (coe
                  MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
                  (coe v2)))
            (coe
               MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
               (coe
                  MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_coarseOf_82
                  (coe v0) (coe v3))
               (coe
                  MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
                  (coe v3)))))
-- DASHI.Physics.RealOperatorStackShift.strictP-fiber
d_strictP'45'fiber_166 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Geometry.FiberContraction.T_ContractiveOnFibers_46
d_strictP'45'fiber_166 v0 v1
  = coe
      MAlonzo.Code.DASHI.Geometry.FiberContraction.C_ContractiveOnFibers'46'constructor_559
      (coe
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.du_dNatFine'45'positive_98
              (coe addInt (coe v0) (coe v1)) (coe v2) (coe v3)))
-- DASHI.Physics.RealOperatorStackShift._.d
d_d_180 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Geometry.FiberContraction.T_FiberDistinct_22 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_d_180 v0 v1 ~v2 ~v3 ~v4 = du_d_180 v0 v1
du_d_180 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_d_180 v0 v1
  = coe
      MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine_36
      (coe addInt (coe v0) (coe v1))

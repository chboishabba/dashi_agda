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

module MAlonzo.Code.DASHI.Physics.CanonicalizationMinimal where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Algebra.Trit
import qualified MAlonzo.Code.DASHI.Geometry.StrictContractionComposition
import qualified MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric
import qualified MAlonzo.Code.DASHI.Physics.TailCollapseProof
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.CanonicalizationMinimal.canonTrit
d_canonTrit_6 ::
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6
d_canonTrit_6 v0
  = case coe v0 of
      MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8
        -> coe MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12
      MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10 -> coe v0
      MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.CanonicalizationMinimal.canonVec
d_canonVec_10 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_canonVec_10 ~v0 = du_canonVec_10
du_canonVec_10 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_canonVec_10
  = coe MAlonzo.Code.Data.Vec.Base.du_map_178 (coe d_canonTrit_6)
-- DASHI.Physics.CanonicalizationMinimal.Cᵣ
d_C'7523'_16 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_C'7523'_16 v0 ~v1 v2 = du_C'7523'_16 v0 v2
du_C'7523'_16 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_C'7523'_16 v0 v1
  = let v2
          = coe
              MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_split_12 (coe v0)
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe
                MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                (coe du_canonVec_10 v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Physics.CanonicalizationMinimal.Cᵣ-++
d_C'7523''45''43''43'_46 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_C'7523''45''43''43'_46 = erased
-- DASHI.Physics.CanonicalizationMinimal.nonexpCᵣ
d_nonexpC'7523'_64 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.T_NonExpansive_26
d_nonexpC'7523'_64 v0 v1
  = coe
      MAlonzo.Code.DASHI.Geometry.StrictContractionComposition.C_NonExpansive'46'constructor_355
      (coe d_nonexp_78 (coe v0) (coe v1))
-- DASHI.Physics.CanonicalizationMinimal._.nonexp
d_nonexp_78 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonexp_78 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
      (coe
         MAlonzo.Code.DASHI.Metric.FineAgreementUltrametric.d_dNatFine'45''43''43''45'map'8804'_1266
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
            (coe v3))
         (coe d_canonTrit_6))
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

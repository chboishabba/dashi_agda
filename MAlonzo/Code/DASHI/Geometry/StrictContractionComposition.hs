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

module MAlonzo.Code.DASHI.Geometry.StrictContractionComposition where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Contraction
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Ultrametric

-- DASHI.Geometry.StrictContractionComposition._∘_
d__'8728'__12 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'8728'__12 ~v0 ~v1 ~v2 v3 v4 v5 = du__'8728'__12 v3 v4 v5
du__'8728'__12 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'8728'__12 v0 v1 v2 = coe v0 (coe v1 v2)
-- DASHI.Geometry.StrictContractionComposition.NonExpansive
d_NonExpansive_26 a0 a1 a2 = ()
newtype T_NonExpansive_26
  = C_NonExpansive'46'constructor_355 (AgdaAny ->
                                       AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- DASHI.Geometry.StrictContractionComposition._.d
d_d_36 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> Integer
d_d_36 v0 ~v1 = du_d_36 v0
du_d_36 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  AgdaAny -> AgdaAny -> Integer
du_d_36 v0 = coe MAlonzo.Code.Ultrametric.d_d_30 (coe v0)
-- DASHI.Geometry.StrictContractionComposition.NonExpansive.nonexp
d_nonexp_64 ::
  T_NonExpansive_26 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonexp_64 v0
  = case coe v0 of
      C_NonExpansive'46'constructor_355 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.StrictContractionComposition.DistinctPreserving
d_DistinctPreserving_70 a0 a1 = ()
data T_DistinctPreserving_70
  = C_DistinctPreserving'46'constructor_805
-- DASHI.Geometry.StrictContractionComposition.DistinctPreserving.preserves≢
d_preserves'8802'_86 ::
  T_DistinctPreserving_70 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_preserves'8802'_86 = erased
-- DASHI.Geometry.StrictContractionComposition.OrderLaws
d_OrderLaws_88 = ()
data T_OrderLaws_88
  = C_OrderLaws'46'constructor_983 (Integer ->
                                    Integer ->
                                    Integer ->
                                    MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
                                    MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
                                    MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                                   (Integer ->
                                    Integer ->
                                    Integer ->
                                    MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
                                    MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
                                    MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                                   (Integer ->
                                    Integer ->
                                    Integer ->
                                    MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
                                    MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
                                    MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- DASHI.Geometry.StrictContractionComposition.OrderLaws.le-trans
d_le'45'trans_120 ::
  T_OrderLaws_88 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_le'45'trans_120 v0
  = case coe v0 of
      C_OrderLaws'46'constructor_983 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.StrictContractionComposition.OrderLaws.le-<-trans
d_le'45''60''45'trans_128 ::
  T_OrderLaws_88 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_le'45''60''45'trans_128 v0
  = case coe v0 of
      C_OrderLaws'46'constructor_983 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.StrictContractionComposition.OrderLaws.<-le-trans
d_'60''45'le'45'trans_136 ::
  T_OrderLaws_88 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'le'45'trans_136 v0
  = case coe v0 of
      C_OrderLaws'46'constructor_983 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.StrictContractionComposition.composeStrict
d_composeStrict_148 ::
  () ->
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_OrderLaws_88 ->
  T_NonExpansive_26 ->
  T_NonExpansive_26 ->
  T_DistinctPreserving_70 ->
  MAlonzo.Code.Contraction.T_Contractive'8802'_62 ->
  MAlonzo.Code.Contraction.T_Contractive'8802'_62
d_composeStrict_148 ~v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_composeStrict_148 v1 v2 v3 v4 v5 v6 v7 v9
du_composeStrict_148 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_OrderLaws_88 ->
  T_NonExpansive_26 ->
  T_NonExpansive_26 ->
  MAlonzo.Code.Contraction.T_Contractive'8802'_62 ->
  MAlonzo.Code.Contraction.T_Contractive'8802'_62
du_composeStrict_148 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Contraction.C_Contractive'8802''46'constructor_849
      (coe
         (\ v8 v9 v10 ->
            coe
              d_'60''45'le'45'trans_136 v4
              (coe
                 MAlonzo.Code.Ultrametric.d_d_30 v0 (coe v1 (coe v3 (coe v2 v8)))
                 (coe v1 (coe v3 (coe v2 v9))))
              (coe MAlonzo.Code.Ultrametric.d_d_30 v0 (coe v2 v8) (coe v2 v9))
              (coe MAlonzo.Code.Ultrametric.d_d_30 v0 v8 v9)
              (coe
                 d_le'45''60''45'trans_128 v4
                 (coe
                    MAlonzo.Code.Ultrametric.d_d_30 v0 (coe v1 (coe v3 (coe v2 v8)))
                    (coe v1 (coe v3 (coe v2 v9))))
                 (coe
                    MAlonzo.Code.Ultrametric.d_d_30 v0 (coe v3 (coe v2 v8))
                    (coe v3 (coe v2 v9)))
                 (coe MAlonzo.Code.Ultrametric.d_d_30 v0 (coe v2 v8) (coe v2 v9))
                 (coe d_nonexp_64 v5 (coe v3 (coe v2 v8)) (coe v3 (coe v2 v9)))
                 (coe
                    MAlonzo.Code.Contraction.d_contraction'8802'_100 v7 (coe v2 v8)
                    (coe v2 v9) erased))
              (coe d_nonexp_64 v6 v8 v9)))
-- DASHI.Geometry.StrictContractionComposition._.<-le-trans
d_'60''45'le'45'trans_190 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_OrderLaws_88 ->
  T_NonExpansive_26 ->
  T_NonExpansive_26 ->
  T_DistinctPreserving_70 ->
  MAlonzo.Code.Contraction.T_Contractive'8802'_62 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'le'45'trans_190 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11
  = du_'60''45'le'45'trans_190 v4
du_'60''45'le'45'trans_190 ::
  T_OrderLaws_88 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'le'45'trans_190 v0
  = coe d_'60''45'le'45'trans_136 (coe v0)
-- DASHI.Geometry.StrictContractionComposition._.le-<-trans
d_le'45''60''45'trans_192 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_OrderLaws_88 ->
  T_NonExpansive_26 ->
  T_NonExpansive_26 ->
  T_DistinctPreserving_70 ->
  MAlonzo.Code.Contraction.T_Contractive'8802'_62 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_le'45''60''45'trans_192 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11
  = du_le'45''60''45'trans_192 v4
du_le'45''60''45'trans_192 ::
  T_OrderLaws_88 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_le'45''60''45'trans_192 v0
  = coe d_le'45''60''45'trans_128 (coe v0)
-- DASHI.Geometry.StrictContractionComposition._.le-trans
d_le'45'trans_194 ::
  MAlonzo.Code.Ultrametric.T_Ultrametric_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_OrderLaws_88 ->
  T_NonExpansive_26 ->
  T_NonExpansive_26 ->
  T_DistinctPreserving_70 ->
  MAlonzo.Code.Contraction.T_Contractive'8802'_62 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_le'45'trans_194 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_le'45'trans_194 v4
du_le'45'trans_194 ::
  T_OrderLaws_88 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_le'45'trans_194 v0 = coe d_le'45'trans_120 (coe v0)

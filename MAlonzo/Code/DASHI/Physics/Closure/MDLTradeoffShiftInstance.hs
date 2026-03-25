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

module MAlonzo.Code.DASHI.Physics.Closure.MDLTradeoffShiftInstance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Algebra.Trit
import qualified MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff
import qualified MAlonzo.Code.DASHI.Physics.TailCollapseProof
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.NatOrderedMonoid
d_NatOrderedMonoid_8 ::
  MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.T_OrderedMonoid_26
d_NatOrderedMonoid_8
  = coe
      MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.C_OrderedMonoid'46'constructor_761
      (coe
         MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.C_AddMonoid'46'constructor_23
         addInt (0 :: Integer))
      (\ v0 ->
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776 (coe v0))
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784)
      (\ v0 v1 v2 v3 ->
         coe
           MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3530
           (coe v3))
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.nz
d_nz_30 :: MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 -> Integer
d_nz_30 v0
  = case coe v0 of
      MAlonzo.Code.DASHI.Algebra.Trit.C_neg_8 -> coe (1 :: Integer)
      MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10 -> coe (0 :: Integer)
      MAlonzo.Code.DASHI.Algebra.Trit.C_pos_12 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.countNZ
d_countNZ_34 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_countNZ_34 ~v0 v1 = du_countNZ_34 v1
du_countNZ_34 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_countNZ_34 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe (0 :: Integer)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> coe addInt (coe du_countNZ_34 (coe v3)) (coe d_nz_30 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.countNZ-snoc
d_countNZ'45'snoc_46 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_countNZ'45'snoc_46 = erased
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.countNZ-replicate-zer
d_countNZ'45'replicate'45'zer_60 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_countNZ'45'replicate'45'zer_60 = erased
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.countNZ-init≤
d_countNZ'45'init'8804'_70 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_countNZ'45'init'8804'_70 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
               -> coe seq (coe v4) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
                         -> coe
                              MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3530
                              (coe
                                 du_countNZ_34 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8))
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                                 (coe d_nz_30 (coe v4)))
                              (coe
                                 d_countNZ'45'init'8804'_70 (coe v2)
                                 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.projTail-def
d_projTail'45'def_86 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projTail'45'def_86 = erased
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.shiftTail-def
d_shiftTail'45'def_96 ::
  Integer ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shiftTail'45'def_96 = erased
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.countNZ-projTail≤
d_countNZ'45'projTail'8804'_106 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_countNZ'45'projTail'8804'_106 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                (coe
                   du_countNZ_34
                   (coe
                      MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_projTail_116
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe d_countNZ'45'init'8804'_70 (coe v2) (coe v1))
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.countNZ-shiftTail≤
d_countNZ'45'shiftTail'8804'_128 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_countNZ'45'shiftTail'8804'_128 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                (coe
                   du_countNZ_34
                   (coe
                      MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_shiftTail_106
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))))
      _ -> case coe v1 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3494
                    (coe du_countNZ_34 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.countNZ-tailStep≤
d_countNZ'45'tailStep'8804'_152 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_countNZ'45'tailStep'8804'_152 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
      (coe
         d_countNZ'45'projTail'8804'_106 (coe v0)
         (coe
            MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_shiftTail_106
            (coe v0) (coe v1)))
      (coe d_countNZ'45'shiftTail'8804'_128 (coe v0) (coe v1))
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.tailOf-Pᵣ
d_tailOf'45'P'7523'_162 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tailOf'45'P'7523'_162 = erased
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.tailOf-Tᵣ
d_tailOf'45'T'7523'_198 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tailOf'45'T'7523'_198 = erased
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.resid-drop-lemma
d_resid'45'drop'45'lemma_212 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_resid'45'drop'45'lemma_212 v0 v1 v2
  = coe
      d_countNZ'45'tailStep'8804'_152 (coe v1)
      (coe
         MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
         (coe v2))
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.coarse-invariant-R
d_coarse'45'invariant'45'R_230 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coarse'45'invariant'45'R_230 = erased
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.coarse-invariant-P
d_coarse'45'invariant'45'P_262 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coarse'45'invariant'45'P_262 = erased
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.coarse-invariant-T
d_coarse'45'invariant'45'T_294 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coarse'45'invariant'45'T_294 = erased
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.coarseOf-PT-≡-P
d_coarseOf'45'PT'45''8801''45'P_308 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coarseOf'45'PT'45''8801''45'P_308 = erased
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.model-drop-lemma
d_model'45'drop'45'lemma_330 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_model'45'drop'45'lemma_330 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
      (coe
         du_countNZ_34
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_split_12 (coe v0)
               (coe
                  MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                     (coe
                        MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_split_12 (coe v0)
                        (coe v2)))
                  (coe
                     MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_projTail_116
                     (coe v1)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                        (coe
                           MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_split_12 (coe v0)
                           (coe v2))))))))
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.MDLPartsShift
d_MDLPartsShift_346 ::
  Integer ->
  Integer -> MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.T_MDLParts_90
d_MDLPartsShift_346 v0 v1
  = coe
      MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.C_MDLParts'46'constructor_1861
      (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_P'7523'_158
         (coe v0) (coe v1))
      (\ v2 -> v2)
      (MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_T'7523'_228
         (coe v0) (coe v1))
      (\ v2 ->
         coe
           du_countNZ_34
           (coe
              MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_coarseOf_82
              (coe v0) (coe v2)))
      (\ v2 ->
         coe
           du_countNZ_34
           (coe
              MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
              (coe v2)))
      (\ v2 ->
         addInt
           (coe
              du_countNZ_34
              (coe
                 MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_tailOf_96 (coe v0)
                 (coe v2)))
           (coe
              du_countNZ_34
              (coe
                 MAlonzo.Code.DASHI.Physics.TailCollapseProof.du_coarseOf_82
                 (coe v0)
                 (coe
                    MAlonzo.Code.DASHI.Physics.TailCollapseProof.d_P'7523'_158 (coe v0)
                    (coe v1) (coe v2)))))
-- DASHI.Physics.Closure.MDLTradeoffShiftInstance.TradeoffShift
d_TradeoffShift_366 ::
  Integer ->
  Integer ->
  MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.T_TradeoffLemma_158
d_TradeoffShift_366 v0 v1
  = coe
      MAlonzo.Code.DASHI.MDL.MDLDescentTradeoff.C_TradeoffLemma'46'constructor_4549
      (coe d_model'45'drop'45'lemma_330 (coe v0) (coe v1))
      (coe d_resid'45'drop'45'lemma_212 (coe v0) (coe v1))

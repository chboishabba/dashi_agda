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

module MAlonzo.Code.DASHI.Physics.TailCollapseProof where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.DASHI.Algebra.Trit
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.TailCollapseProof.split
d_split_12 ::
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_split_12 ~v0 v1 ~v2 v3 = du_split_12 v1 v3
du_split_12 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_split_12 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32) (coe v1)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
                  -> let v6 = coe du_split_12 (coe v2) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v7) (coe v8)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Physics.TailCollapseProof.split-++
d_split'45''43''43'_58 ::
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_split'45''43''43'_58 = erased
-- DASHI.Physics.TailCollapseProof.coarseOf
d_coarseOf_82 ::
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_coarseOf_82 ~v0 v1 ~v2 v3 = du_coarseOf_82 v1 v3
du_coarseOf_82 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_coarseOf_82 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_split_12 (coe v0) (coe v1))
-- DASHI.Physics.TailCollapseProof.tailOf
d_tailOf_96 ::
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_tailOf_96 ~v0 v1 ~v2 v3 = du_tailOf_96 v1 v3
du_tailOf_96 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_tailOf_96 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe du_split_12 (coe v0) (coe v1))
-- DASHI.Physics.TailCollapseProof.shiftTail
d_shiftTail_106 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_shiftTail_106 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1) (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
      _ -> case coe v1 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
               -> coe
                    MAlonzo.Code.Data.Vec.Base.du__'8759''691'__606 (coe v4)
                    (coe MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10)
             _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.TailCollapseProof.projTail
d_projTail_116 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_projTail_116 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1) (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Base.du__'8759''691'__606
                (coe MAlonzo.Code.Data.Vec.Base.du_init_658 (coe v2) (coe v1))
                (coe MAlonzo.Code.DASHI.Algebra.Trit.C_zer_10))
-- DASHI.Physics.TailCollapseProof.tailStep
d_tailStep_124 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_tailStep_124 v0 v1
  = coe
      d_projTail_116 (coe v0) (coe d_shiftTail_106 (coe v0) (coe v1))
-- DASHI.Physics.TailCollapseProof.Rᵣ
d_R'7523'_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_R'7523'_132 v0 v1 v2
  = let v3 = coe du_split_12 (coe v0) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe
                MAlonzo.Code.Data.Vec.Base.du__'43''43'__188 (coe v4)
                (coe d_shiftTail_106 (coe v1) (coe v5))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Physics.TailCollapseProof.Pᵣ
d_P'7523'_158 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_P'7523'_158 v0 v1 v2
  = let v3 = coe du_split_12 (coe v0) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe
                MAlonzo.Code.Data.Vec.Base.du__'43''43'__188 (coe v4)
                (coe d_projTail_116 (coe v1) (coe v5))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Physics.TailCollapseProof.Rᵣ-++
d_R'7523''45''43''43'_188 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'7523''45''43''43'_188 = erased
-- DASHI.Physics.TailCollapseProof.Pᵣ-++
d_P'7523''45''43''43'_210 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_P'7523''45''43''43'_210 = erased
-- DASHI.Physics.TailCollapseProof.Tᵣ
d_T'7523'_228 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_T'7523'_228 v0 v1 v2
  = coe
      d_P'7523'_158 (coe v0) (coe v1)
      (coe d_R'7523'_132 (coe v0) (coe v1) (coe v2))
-- DASHI.Physics.TailCollapseProof.iterate
d_iterate_238 ::
  () -> Integer -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_iterate_238 ~v0 v1 v2 v3 = du_iterate_238 v1 v2 v3
du_iterate_238 ::
  Integer -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_iterate_238 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe du_iterate_238 (coe v3) (coe v1) (coe v1 v2))
-- DASHI.Physics.TailCollapseProof.init-replicate
d_init'45'replicate_252 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_init'45'replicate_252 = erased
-- DASHI.Physics.TailCollapseProof.snoc-replicate
d_snoc'45'replicate_260 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snoc'45'replicate_260 = erased
-- DASHI.Physics.TailCollapseProof.tailStep-forgets-last
d_tailStep'45'forgets'45'last_270 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tailStep'45'forgets'45'last_270 = erased
-- DASHI.Physics.TailCollapseProof.projTail-replicate
d_projTail'45'replicate_278 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projTail'45'replicate_278 = erased
-- DASHI.Physics.TailCollapseProof.shiftTail-replicate
d_shiftTail'45'replicate_286 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shiftTail'45'replicate_286 = erased
-- DASHI.Physics.TailCollapseProof.tailStep-replicate
d_tailStep'45'replicate_292 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tailStep'45'replicate_292 = erased
-- DASHI.Physics.TailCollapseProof.pair-η
d_pair'45'η_302 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'η_302 = erased
-- DASHI.Physics.TailCollapseProof.init-∷ʳ
d_init'45''8759''691'_316 ::
  () ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_init'45''8759''691'_316 = erased
-- DASHI.Physics.TailCollapseProof.projTail-idem
d_projTail'45'idem_336 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projTail'45'idem_336 = erased
-- DASHI.Physics.TailCollapseProof.Pᵣ-idem
d_P'7523''45'idem_350 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_P'7523''45'idem_350 = erased
-- DASHI.Physics.TailCollapseProof.tailStep≡shiftTail
d_tailStep'8801'shiftTail_388 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tailStep'8801'shiftTail_388 = erased
-- DASHI.Physics.TailCollapseProof.shiftTail-∷ʳ-zer
d_shiftTail'45''8759''691''45'zer_404 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shiftTail'45''8759''691''45'zer_404 = erased
-- DASHI.Physics.TailCollapseProof.iterate-shiftTail-∷ʳ-zer
d_iterate'45'shiftTail'45''8759''691''45'zer_418 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iterate'45'shiftTail'45''8759''691''45'zer_418 = erased
-- DASHI.Physics.TailCollapseProof.iterate-pointwise
d_iterate'45'pointwise_446 ::
  () ->
  Integer ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iterate'45'pointwise_446 = erased
-- DASHI.Physics.TailCollapseProof.tailCollapse-shiftTail
d_tailCollapse'45'shiftTail_474 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tailCollapse'45'shiftTail_474 = erased
-- DASHI.Physics.TailCollapseProof.tailCollapse
d_tailCollapse_488 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tailCollapse_488 = erased
-- DASHI.Physics.TailCollapseProof.merge-split
d_merge'45'split_504 ::
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_merge'45'split_504 = erased
-- DASHI.Physics.TailCollapseProof.Tᵣ-++
d_T'7523''45''43''43'_534 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'7523''45''43''43'_534 = erased
-- DASHI.Physics.TailCollapseProof.split-Tᵣ
d_split'45'T'7523'_558 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_split'45'T'7523'_558 = erased
-- DASHI.Physics.TailCollapseProof.split-iterate-Tᵣ
d_split'45'iterate'45'T'7523'_600 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_split'45'iterate'45'T'7523'_600 = erased
-- DASHI.Physics.TailCollapseProof.tailOf-after-Tk
d_tailOf'45'after'45'Tk_630 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tailOf'45'after'45'Tk_630 = erased

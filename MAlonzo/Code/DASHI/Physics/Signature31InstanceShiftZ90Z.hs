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

module MAlonzo.Code.DASHI.Physics.Signature31InstanceShiftZ90Z where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.DASHI.Algebra.Trit
import qualified MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy
import qualified MAlonzo.Code.DASHI.Geometry.QQuadraticForm
import qualified MAlonzo.Code.DASHI.Geometry.Signature.HyperbolicFormZ90Z
import qualified MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy
import qualified MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance
import qualified MAlonzo.Code.DASHI.Physics.QQuadraticPolarization
import qualified MAlonzo.Code.DASHI.Physics.Signature31OrbitActionAgreement
import qualified MAlonzo.Code.DASHI.Physics.SignedPerm4
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Signature31InstanceShiftZ.m
d_m_6 :: Integer
d_m_6 = coe (4 :: Integer)
-- DASHI.Physics.Signature31InstanceShiftZ.QFΣ
d_QFΣ_10 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_QFΣ_10
  = coe
      MAlonzo.Code.DASHI.Physics.QQuadraticEmergenceShiftInstance.d_quadraticShiftΣ_364
      (coe d_m_6)
-- DASHI.Physics.Signature31InstanceShiftZ.QF
d_QF_12 ::
  MAlonzo.Code.DASHI.Geometry.QQuadraticForm.T_QuadraticForm_44
d_QF_12
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_QFΣ_10)
-- DASHI.Physics.Signature31InstanceShiftZ.toCounts'
d_toCounts''_14 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Geometry.Signature.HyperbolicFormZ90Z.T_CausalCountsZ_10
d_toCounts''_14 v0 v1
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature.HyperbolicFormZ90Z.C_CausalCountsZ'46'constructor_23
      (coe v0) (coe v1)
-- DASHI.Physics.Signature31InstanceShiftZ.toCounts
d_toCounts_20 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.DASHI.Geometry.Signature.HyperbolicFormZ90Z.T_CausalCountsZ_10
d_toCounts_20 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> coe d_toCounts''_14 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Signature31InstanceShiftZ.zero4
d_zero4_26 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_zero4_26
  = coe
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 (0 :: Integer)
      (coe
         MAlonzo.Code.Data.Vec.Base.C__'8759'__38 (0 :: Integer)
         (coe
            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 (0 :: Integer)
            (coe
               MAlonzo.Code.Data.Vec.Base.C__'8759'__38 (0 :: Integer)
               (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))))
-- DASHI.Physics.Signature31InstanceShiftZ.coneNontrivialWitness
d_coneNontrivialWitness_28 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_coneNontrivialWitness_28
  = coe
      MAlonzo.Code.Data.Integer.Properties.d_'8804''45'refl_2728
      (coe
         MAlonzo.Code.DASHI.Geometry.Signature.HyperbolicFormZ90Z.du_sumSq_24
         (coe
            MAlonzo.Code.DASHI.Geometry.Signature.HyperbolicFormZ90Z.d_sigma_20
            (coe d_toCounts_20 (coe d_zero4_26))))
-- DASHI.Physics.Signature31InstanceShiftZ.tau-toCounts
d_tau'45'toCounts_34 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tau'45'toCounts_34 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.tau-toCounts'
d_tau'45'toCounts''_44 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tau'45'toCounts''_44 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.sigma-toCounts'
d_sigma'45'toCounts''_54 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigma'45'toCounts''_54 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.flipVal
d_flipVal_60 :: Bool -> Integer -> Integer
d_flipVal_60 v0 v1
  = if coe v0
      then coe v1
      else coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)
-- DASHI.Physics.Signature31InstanceShiftZ.flipBy
d_flipBy_66 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_flipBy_66 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> coe
                           seq (coe v10)
                           (case coe v1 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
                                -> case coe v13 of
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v18 v19
                                              -> coe
                                                   seq (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                      (d_flipVal_60 (coe v3) (coe v12))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         (d_flipVal_60 (coe v6) (coe v15))
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            (d_flipVal_60 (coe v9) (coe v18))
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Signature31InstanceShiftZ.SignedPerm3
d_SignedPerm3_80 = ()
data T_SignedPerm3_80
  = C_SignedPerm3'46'constructor_4931 MAlonzo.Code.DASHI.Physics.SignedPerm4.T_Perm3_6
                                      MAlonzo.Code.Data.Vec.Base.T_Vec_28
-- DASHI.Physics.Signature31InstanceShiftZ.SignedPerm3.perm
d_perm_86 ::
  T_SignedPerm3_80 ->
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_Perm3_6
d_perm_86 v0
  = case coe v0 of
      C_SignedPerm3'46'constructor_4931 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Signature31InstanceShiftZ.SignedPerm3.flip
d_flip_88 ::
  T_SignedPerm3_80 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_flip_88 v0
  = case coe v0 of
      C_SignedPerm3'46'constructor_4931 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Signature31InstanceShiftZ.applySigned
d_applySigned_90 ::
  T_SignedPerm3_80 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_applySigned_90 v0 v1
  = coe
      d_flipBy_66 (coe d_flip_88 (coe v0))
      (coe
         MAlonzo.Code.DASHI.Physics.SignedPerm4.du_permute3_22
         (coe d_perm_86 (coe v0)) (coe v1))
-- DASHI.Physics.Signature31InstanceShiftZ.actIso
d_actIso_96 ::
  T_SignedPerm3_80 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_actIso_96 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
                             -> coe
                                  seq (coe v13)
                                  (coe
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3
                                     (d_flipBy_66
                                        (coe d_flip_88 (coe v0))
                                        (coe
                                           MAlonzo.Code.DASHI.Physics.SignedPerm4.du_permute3_22
                                           (coe d_perm_86 (coe v0))
                                           (coe
                                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                              (coe
                                                 MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                                 (coe
                                                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12
                                                    (coe
                                                       MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Signature31InstanceShiftZ.flipTritℤ
d_flipTritℤ_108 :: Bool -> Integer -> Integer
d_flipTritℤ_108 v0 v1
  = if coe v0
      then coe v1
      else coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)
-- DASHI.Physics.Signature31InstanceShiftZ.actIso4
d_actIso4_114 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_actIso4_114 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
                             -> coe
                                  seq (coe v13)
                                  (coe
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                     (d_flipTritℤ_108
                                        (coe
                                           MAlonzo.Code.DASHI.Physics.SignedPerm4.d_flipT_96
                                           (coe v0))
                                        (coe v3))
                                     (d_flipBy_66
                                        (coe
                                           MAlonzo.Code.DASHI.Physics.SignedPerm4.d_flipS_98
                                           (coe v0))
                                        (coe
                                           MAlonzo.Code.DASHI.Physics.SignedPerm4.du_permute3_22
                                           (coe
                                              MAlonzo.Code.DASHI.Physics.SignedPerm4.d_perm_94
                                              (coe v0))
                                           (coe
                                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                              (coe
                                                 MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                                 (coe
                                                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12
                                                    (coe
                                                       MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Signature31InstanceShiftZ.intOfTrit-flipTrit
d_intOfTrit'45'flipTrit_130 ::
  Bool ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_intOfTrit'45'flipTrit_130 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.intOfTrit-flipTritT
d_intOfTrit'45'flipTritT_138 ::
  Bool ->
  MAlonzo.Code.DASHI.Algebra.Trit.T_Trit_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_intOfTrit'45'flipTritT_138 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.vecℤ-flipBy3
d_vecℤ'45'flipBy3_146 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vecℤ'45'flipBy3_146 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.vecℤ-permute3
d_vecℤ'45'permute3_164 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_Perm3_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vecℤ'45'permute3_164 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.tau-actIso
d_tau'45'actIso_236 ::
  T_SignedPerm3_80 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tau'45'actIso_236 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.sq-neg
d_sq'45'neg_356 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sq'45'neg_356 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.sq-flipVal
d_sq'45'flipVal_366 ::
  Bool -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sq'45'flipVal_366 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.sq-flipTritℤ
d_sq'45'flipTritℤ_376 ::
  Bool -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sq'45'flipTritℤ_376 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.sumSq-flipBy
d_sumSq'45'flipBy_386 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sumSq'45'flipBy_386 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.sumSq-perm
d_sumSq'45'perm_404 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_Perm3_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sumSq'45'perm_404 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.sumSq3'
d_sumSq3''_412 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sumSq3''_412 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.sumSq3
d_sumSq3_426 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sumSq3_426 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.swap-left
d_swap'45'left_442 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_swap'45'left_442 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.swap-inner
d_swap'45'inner_458 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_swap'45'inner_458 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.qcore-pres
d_qcore'45'pres_532 ::
  T_SignedPerm3_80 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_qcore'45'pres_532 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.qcore-sumSq
d_qcore'45'sumSq_538 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_qcore'45'sumSq_538 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.sumSq-actIso4
d_sumSq'45'actIso4_566 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sumSq'45'actIso4_566 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.qcore-pres4
d_qcore'45'pres4_582 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_qcore'45'pres4_582 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.actFiniteCompat
d_actFiniteCompat_592 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_actFiniteCompat_592 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.shell1-pres
d_shell1'45'pres_612 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shell1'45'pres_612 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.shell2-pres
d_shell2'45'pres_624 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shell2'45'pres_624 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.cone-pres-go
d_cone'45'pres'45'go_648 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_Perm3_6 ->
  Bool ->
  Bool ->
  Bool ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_cone'45'pres'45'go_648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_cone'45'pres'45'go_648 v8
du_cone'45'pres'45'go_648 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_cone'45'pres'45'go_648 v0 = coe v0
-- DASHI.Physics.Signature31InstanceShiftZ.cone-pres
d_cone'45'pres_688 ::
  T_SignedPerm3_80 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_cone'45'pres_688 v0 v1 v2
  = case coe v0 of
      C_SignedPerm3'46'constructor_4931 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
                             -> coe
                                  seq (coe v13)
                                  (case coe v1 of
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v18 v19
                                              -> case coe v19 of
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v21 v22
                                                     -> case coe v22 of
                                                          MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v24 v25
                                                            -> coe
                                                                 seq (coe v25)
                                                                 (coe seq (coe v3) (coe v2))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.Signature31InstanceShiftZ.cone-pres4
d_cone'45'pres4_828 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_cone'45'pres4_828 v0 v1 v2
  = coe
      seq (coe v0)
      (case coe v1 of
         MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
           -> case coe v5 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
                  -> case coe v8 of
                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
                         -> case coe v11 of
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v13 v14
                                -> coe seq (coe v14) (coe v2)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- DASHI.Physics.Signature31InstanceShiftZ.sigAxioms
d_sigAxioms_858 ::
  MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.T_SignatureAxioms_16
d_sigAxioms_858
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.C_SignatureAxioms'46'constructor_1573
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_ConeStructure'46'constructor_13
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_TimeArrow'46'constructor_115
         (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (\ v0 v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_IsotropyAction'46'constructor_293
         d_actIso4_114
         (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_ShellIsotropyAction'46'constructor_765
         (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_FiniteShellRealization'46'constructor_1089
         (coe
            MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm.du_decEqVec_52)
         (MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm.d_allVecTrit_114
            (coe (4 :: Integer)))
         (coe MAlonzo.Code.DASHI.Physics.QQuadraticPolarization.du_vecℤ_114)
         (MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm.d_isShell_126
            (coe (1 :: Integer)))
         (MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm.d_isShell_126
            (coe (2 :: Integer))))
      (coe
         MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_FiniteIsotropyRealization'46'constructor_1717
         MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm.d_allSignedPerm4_206
         MAlonzo.Code.DASHI.Physics.Signature31OrbitActionAgreement.d_actIso4Trit_6
         (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- DASHI.Physics.Signature31InstanceShiftZ.sig31Axioms
d_sig31Axioms_916 ::
  MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.T_Signature31FromConeArrowIsotropyAxioms_146
d_sig31Axioms_916
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.C_Signature31FromConeArrowIsotropyAxioms'46'constructor_3413
      (coe
         (\ v0 ->
            coe MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.C_sig31_288))
-- DASHI.Physics.Signature31InstanceShiftZ.signature31
d_signature31_920 ::
  MAlonzo.Code.DASHI.Geometry.ConeTimeIsotropy.T_Signature_286
d_signature31_920
  = coe
      MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.d_Signature31Theorem_164
      d_sig31Axioms_916 d_sigAxioms_858
-- DASHI.Physics.Signature31InstanceShiftZ.orientationTagFromArrow
d_orientationTagFromArrow_922 ::
  MAlonzo.Code.DASHI.Geometry.Signature31FromConeArrowIsotropy.T_SignatureAxioms_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_orientationTagFromArrow_922 = erased
-- DASHI.Physics.Signature31InstanceShiftZ.measuredFromConeArrowShift
d_measuredFromConeArrowShift_924 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_measuredFromConeArrowShift_924 = erased

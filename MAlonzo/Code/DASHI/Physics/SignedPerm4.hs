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

module MAlonzo.Code.DASHI.Physics.SignedPerm4 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.SignedPerm4.Perm3
d_Perm3_6 = ()
data T_Perm3_6
  = C_p012_8 | C_p021_10 | C_p102_12 | C_p120_14 | C_p201_16 |
    C_p210_18
-- DASHI.Physics.SignedPerm4.permute3
d_permute3_22 ::
  () ->
  T_Perm3_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_permute3_22 ~v0 v1 v2 = du_permute3_22 v1 v2
du_permute3_22 ::
  T_Perm3_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_permute3_22 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> coe
                           seq (coe v10)
                           (case coe v0 of
                              C_p012_8
                                -> coe
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3
                                     (coe
                                        MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                        (coe
                                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                           (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                              C_p021_10
                                -> coe
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3
                                     (coe
                                        MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                        (coe
                                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                           (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                              C_p102_12
                                -> coe
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                     (coe
                                        MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3
                                        (coe
                                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                           (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                              C_p120_14
                                -> coe
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                     (coe
                                        MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                        (coe
                                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3
                                           (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                              C_p201_16
                                -> coe
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                     (coe
                                        MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3
                                        (coe
                                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                           (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                              C_p210_18
                                -> coe
                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                     (coe
                                        MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                        (coe
                                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3
                                           (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.SignedPerm4.allPerm3
d_allPerm3_84 :: [T_Perm3_6]
d_allPerm3_84
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_p012_8)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_p021_10)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_p102_12)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_p120_14)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_p201_16)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_p210_18)
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- DASHI.Physics.SignedPerm4.SignedPerm4
d_SignedPerm4_86 = ()
data T_SignedPerm4_86
  = C_SignedPerm4'46'constructor_4457 T_Perm3_6 Bool
                                      MAlonzo.Code.Data.Vec.Base.T_Vec_28
-- DASHI.Physics.SignedPerm4.SignedPerm4.perm
d_perm_94 :: T_SignedPerm4_86 -> T_Perm3_6
d_perm_94 v0
  = case coe v0 of
      C_SignedPerm4'46'constructor_4457 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.SignedPerm4.SignedPerm4.flipT
d_flipT_96 :: T_SignedPerm4_86 -> Bool
d_flipT_96 v0
  = case coe v0 of
      C_SignedPerm4'46'constructor_4457 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.SignedPerm4.SignedPerm4.flipS
d_flipS_98 ::
  T_SignedPerm4_86 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_flipS_98 v0
  = case coe v0 of
      C_SignedPerm4'46'constructor_4457 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError

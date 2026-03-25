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

module MAlonzo.Code.MDL.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Nat.Base

-- MDL.Core.CodeLength
d_CodeLength_4 :: ()
d_CodeLength_4 = erased
-- MDL.Core.Dataset
d_Dataset_6 = ()
newtype T_Dataset_6 = C_Dataset'46'constructor_5 AgdaAny
-- MDL.Core.Dataset.Data
d_Data_12 :: T_Dataset_6 -> ()
d_Data_12 = erased
-- MDL.Core.Dataset.sample
d_sample_14 :: T_Dataset_6 -> AgdaAny
d_sample_14 v0
  = case coe v0 of
      C_Dataset'46'constructor_5 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- MDL.Core.Model
d_Model_18 a0 = ()
data T_Model_18
  = C_Model'46'constructor_71 AgdaAny (AgdaAny -> Integer)
                              (AgdaAny -> AgdaAny -> Integer)
-- MDL.Core.Model.Param
d_Param_30 :: T_Model_18 -> ()
d_Param_30 = erased
-- MDL.Core.Model.param
d_param_32 :: T_Model_18 -> AgdaAny
d_param_32 v0
  = case coe v0 of
      C_Model'46'constructor_71 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- MDL.Core.Model.encodeM
d_encodeM_34 :: T_Model_18 -> AgdaAny -> Integer
d_encodeM_34 v0
  = case coe v0 of
      C_Model'46'constructor_71 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- MDL.Core.Model.encodeData
d_encodeData_36 :: T_Model_18 -> AgdaAny -> AgdaAny -> Integer
d_encodeData_36 v0
  = case coe v0 of
      C_Model'46'constructor_71 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- MDL.Core.modelTotalLength
d_modelTotalLength_40 :: T_Dataset_6 -> T_Model_18 -> Integer
d_modelTotalLength_40 v0 v1
  = coe
      addInt
      (coe
         d_encodeData_36 v1 (d_param_32 (coe v1)) (d_sample_14 (coe v0)))
      (coe d_encodeM_34 v1 (d_param_32 (coe v1)))
-- MDL.Core.better
d_better_48 :: T_Dataset_6 -> T_Model_18 -> T_Model_18 -> ()
d_better_48 = erased
-- MDL.Core.Subset
d_Subset_56 :: Integer -> ()
d_Subset_56 = erased
-- MDL.Core.subsetCost
d_subsetCost_62 :: Integer -> Integer -> Integer
d_subsetCost_62 v0 ~v1 = du_subsetCost_62 v0
du_subsetCost_62 :: Integer -> Integer
du_subsetCost_62 v0 = coe v0
-- MDL.Core.BoundedModel
d_BoundedModel_70 a0 a1 = ()
data T_BoundedModel_70
  = C_BoundedModel'46'constructor_507 T_Model_18
                                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- MDL.Core.BoundedModel.inner
d_inner_80 :: T_BoundedModel_70 -> T_Model_18
d_inner_80 v0
  = case coe v0 of
      C_BoundedModel'46'constructor_507 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- MDL.Core.BoundedModel.boundProof
d_boundProof_82 ::
  T_BoundedModel_70 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_boundProof_82 v0
  = case coe v0 of
      C_BoundedModel'46'constructor_507 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- MDL.Core.limit71
d_limit71_84 :: Integer
d_limit71_84 = coe (71 :: Integer)
-- MDL.Core.Model71
d_Model71_88 a0 = ()
data T_Model71_88
  = C_Model71'46'constructor_593 T_Model_18
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- MDL.Core.Model71.base
d_base_96 :: T_Model71_88 -> T_Model_18
d_base_96 v0
  = case coe v0 of
      C_Model71'46'constructor_593 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- MDL.Core.Model71.bounded
d_bounded_98 ::
  T_Model71_88 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bounded_98 v0
  = case coe v0 of
      C_Model71'46'constructor_593 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- MDL.Core.restrictSafe
d_restrictSafe_106 ::
  T_Model_18 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_restrictSafe_106 ~v0 v1 = du_restrictSafe_106 v1
du_restrictSafe_106 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_restrictSafe_106 v0 = coe v0
-- MDL.Core.Lyapunov
d_Lyapunov_116 a0 a1 = ()
data T_Lyapunov_116
  = C_Lyapunov'46'constructor_817 (AgdaAny -> Integer)
                                  (AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- MDL.Core.Lyapunov.L
d_L_128 :: T_Lyapunov_116 -> AgdaAny -> Integer
d_L_128 v0
  = case coe v0 of
      C_Lyapunov'46'constructor_817 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- MDL.Core.Lyapunov.descent
d_descent_132 ::
  T_Lyapunov_116 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_descent_132 v0
  = case coe v0 of
      C_Lyapunov'46'constructor_817 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError

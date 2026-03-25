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

module MAlonzo.Code.DASHI.Combinatorics.Entropy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Nat.Base

-- DASHI.Combinatorics.Entropy.Entropy
d_Entropy_8 a0 = ()
newtype T_Entropy_8
  = C_Entropy'46'constructor_5 (AgdaAny -> Integer)
-- DASHI.Combinatorics.Entropy.Entropy.H
d_H_14 :: T_Entropy_8 -> AgdaAny -> Integer
d_H_14 v0
  = case coe v0 of
      C_Entropy'46'constructor_5 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Combinatorics.Entropy.zero≤
d_zero'8804'_18 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_zero'8804'_18 ~v0 = du_zero'8804'_18
du_zero'8804'_18 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_zero'8804'_18 = coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
-- DASHI.Combinatorics.Entropy.entropy-nonneg
d_entropy'45'nonneg_26 ::
  T_Entropy_8 -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entropy'45'nonneg_26 ~v0 ~v1 = du_entropy'45'nonneg_26
du_entropy'45'nonneg_26 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_entropy'45'nonneg_26 = coe du_zero'8804'_18
-- DASHI.Combinatorics.Entropy.Involution
d_Involution_34 a0 = ()
newtype T_Involution_34
  = C_Involution'46'constructor_279 (AgdaAny -> AgdaAny)
-- DASHI.Combinatorics.Entropy.Involution.ι
d_ι_44 :: T_Involution_34 -> AgdaAny -> AgdaAny
d_ι_44 v0
  = case coe v0 of
      C_Involution'46'constructor_279 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Combinatorics.Entropy.Involution.invol
d_invol_48 ::
  T_Involution_34 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_invol_48 = erased
-- DASHI.Combinatorics.Entropy.EntropyInvariant
d_EntropyInvariant_56 a0 a1 a2 = ()
data T_EntropyInvariant_56 = C_EntropyInvariant'46'constructor_507
-- DASHI.Combinatorics.Entropy.EntropyInvariant.invH
d_invH_70 ::
  T_EntropyInvariant_56 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_invH_70 = erased

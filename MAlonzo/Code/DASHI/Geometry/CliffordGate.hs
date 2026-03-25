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

module MAlonzo.Code.DASHI.Geometry.CliffordGate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

-- DASHI.Geometry.CliffordGate.BilinearForm
d_BilinearForm_14 a0 a1 a2 a3 = ()
newtype T_BilinearForm_14
  = C_BilinearForm'46'constructor_31 (AgdaAny -> AgdaAny -> AgdaAny)
-- DASHI.Geometry.CliffordGate.BilinearForm.⟪_,_⟫
d_'10218'_'44'_'10219'_26 ::
  T_BilinearForm_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_'10218'_'44'_'10219'_26 v0
  = case coe v0 of
      C_BilinearForm'46'constructor_31 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CliffordGate.RingLike
d_RingLike_32 a0 a1 = ()
data T_RingLike_32
  = C_RingLike'46'constructor_163 (AgdaAny -> AgdaAny -> AgdaAny)
                                  (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) AgdaAny
                                  AgdaAny
-- DASHI.Geometry.CliffordGate.RingLike._+_
d__'43'__48 :: T_RingLike_32 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__48 v0
  = case coe v0 of
      C_RingLike'46'constructor_163 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CliffordGate.RingLike._*_
d__'42'__50 :: T_RingLike_32 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__50 v0
  = case coe v0 of
      C_RingLike'46'constructor_163 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CliffordGate.RingLike.-_
d_'45'__52 :: T_RingLike_32 -> AgdaAny -> AgdaAny
d_'45'__52 v0
  = case coe v0 of
      C_RingLike'46'constructor_163 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CliffordGate.RingLike.0#
d_0'35'_54 :: T_RingLike_32 -> AgdaAny
d_0'35'_54 v0
  = case coe v0 of
      C_RingLike'46'constructor_163 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CliffordGate.RingLike.1#
d_1'35'_56 :: T_RingLike_32 -> AgdaAny
d_1'35'_56 v0
  = case coe v0 of
      C_RingLike'46'constructor_163 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CliffordGate.CliffordAlgebra
d_CliffordAlgebra_72 a0 a1 a2 a3 a4 a5 a6 = ()
data T_CliffordAlgebra_72
  = C_CliffordAlgebra'46'constructor_1227 (AgdaAny ->
                                           AgdaAny -> AgdaAny)
                                          AgdaAny (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- DASHI.Geometry.CliffordGate.CliffordAlgebra.Carrier
d_Carrier_102 :: T_CliffordAlgebra_72 -> ()
d_Carrier_102 = erased
-- DASHI.Geometry.CliffordGate.CliffordAlgebra._·_
d__'183'__104 ::
  T_CliffordAlgebra_72 -> AgdaAny -> AgdaAny -> AgdaAny
d__'183'__104 v0
  = case coe v0 of
      C_CliffordAlgebra'46'constructor_1227 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CliffordGate.CliffordAlgebra.1A
d_1A_106 :: T_CliffordAlgebra_72 -> AgdaAny
d_1A_106 v0
  = case coe v0 of
      C_CliffordAlgebra'46'constructor_1227 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CliffordGate.CliffordAlgebra.scalar
d_scalar_108 :: T_CliffordAlgebra_72 -> AgdaAny -> AgdaAny
d_scalar_108 v0
  = case coe v0 of
      C_CliffordAlgebra'46'constructor_1227 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CliffordGate.CliffordAlgebra.embed
d_embed_110 :: T_CliffordAlgebra_72 -> AgdaAny -> AgdaAny
d_embed_110 v0
  = case coe v0 of
      C_CliffordAlgebra'46'constructor_1227 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.CliffordGate.CliffordAlgebra.clifford
d_clifford_114 ::
  T_CliffordAlgebra_72 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clifford_114 = erased
-- DASHI.Geometry.CliffordGate.DiracOperator
d_DiracOperator_136 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
newtype T_DiracOperator_136
  = C_DiracOperator'46'constructor_2005 (AgdaAny -> AgdaAny)
-- DASHI.Geometry.CliffordGate.DiracOperator.D
d_D_160 :: T_DiracOperator_136 -> AgdaAny -> AgdaAny
d_D_160 v0
  = case coe v0 of
      C_DiracOperator'46'constructor_2005 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError

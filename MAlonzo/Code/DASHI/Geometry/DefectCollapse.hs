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

module MAlonzo.Code.DASHI.Geometry.DefectCollapse where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- DASHI.Geometry.DefectCollapse.DefectCollapse
d_DefectCollapse_14 a0 a1 a2 a3 = ()
data T_DefectCollapse_14
  = C_DefectCollapse'46'constructor_209 (AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny)
-- DASHI.Geometry.DefectCollapse.DefectCollapse.D
d_D_36 :: T_DefectCollapse_14 -> AgdaAny -> AgdaAny
d_D_36 v0
  = case coe v0 of
      C_DefectCollapse'46'constructor_209 v1 v2 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.DefectCollapse.DefectCollapse.T
d_T_38 :: T_DefectCollapse_14 -> AgdaAny -> AgdaAny
d_T_38 v0
  = case coe v0 of
      C_DefectCollapse'46'constructor_209 v1 v2 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.DefectCollapse.DefectCollapse._≤_
d__'8804'__40 :: T_DefectCollapse_14 -> AgdaAny -> AgdaAny -> ()
d__'8804'__40 = erased
-- DASHI.Geometry.DefectCollapse.DefectCollapse.energy
d_energy_42 :: T_DefectCollapse_14 -> AgdaAny -> AgdaAny
d_energy_42 v0
  = case coe v0 of
      C_DefectCollapse'46'constructor_209 v1 v2 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.DefectCollapse.DefectCollapse.collapse
d_collapse_46 :: T_DefectCollapse_14 -> AgdaAny -> AgdaAny
d_collapse_46 v0
  = case coe v0 of
      C_DefectCollapse'46'constructor_209 v1 v2 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError

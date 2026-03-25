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

module MAlonzo.Code.DASHI.Geometry.RealIsotropy.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Geometry.Isotropy
import qualified MAlonzo.Code.Ultrametric

-- DASHI.Geometry.RealIsotropy.Core.RealIsotropy
d_RealIsotropy_14 a0 a1 a2 = ()
newtype T_RealIsotropy_14
  = C_RealIsotropy'46'constructor_41 MAlonzo.Code.DASHI.Geometry.Isotropy.T_Isotropy_62
-- DASHI.Geometry.RealIsotropy.Core.RealIsotropy.iso
d_iso_26 ::
  T_RealIsotropy_14 ->
  MAlonzo.Code.DASHI.Geometry.Isotropy.T_Isotropy_62
d_iso_26 v0
  = case coe v0 of
      C_RealIsotropy'46'constructor_41 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.RealIsotropy.Core.RealIsotropy.coneInvariant
d_coneInvariant_28 :: T_RealIsotropy_14 -> ()
d_coneInvariant_28 = erased

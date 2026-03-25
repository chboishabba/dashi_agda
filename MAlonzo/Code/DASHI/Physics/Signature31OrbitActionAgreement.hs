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

module MAlonzo.Code.DASHI.Physics.Signature31OrbitActionAgreement where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm
import qualified MAlonzo.Code.DASHI.Physics.SignedPerm4
import qualified MAlonzo.Code.Data.Vec.Base

-- DASHI.Physics.Signature31OrbitActionAgreement.actIso4Trit
d_actIso4Trit_6 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_actIso4Trit_6 v0 v1
  = coe
      MAlonzo.Code.DASHI.Physics.OrbitProfileComputedSignedPerm.d_actSigned4_180
      (coe v0) (coe v1)
-- DASHI.Physics.Signature31OrbitActionAgreement.actSigned4≡actIso4Trit
d_actSigned4'8801'actIso4Trit_16 ::
  MAlonzo.Code.DASHI.Physics.SignedPerm4.T_SignedPerm4_86 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_actSigned4'8801'actIso4Trit_16 = erased

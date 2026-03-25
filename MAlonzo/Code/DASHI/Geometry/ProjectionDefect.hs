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

module MAlonzo.Code.DASHI.Geometry.ProjectionDefect where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

-- DASHI.Geometry.ProjectionDefect.Additive
d_Additive_8 a0 = ()
data T_Additive_8
  = C_Additive'46'constructor_39 (AgdaAny -> AgdaAny -> AgdaAny)
                                 AgdaAny (AgdaAny -> AgdaAny)
-- DASHI.Geometry.ProjectionDefect.Additive.Carrier
d_Carrier_20 :: T_Additive_8 -> ()
d_Carrier_20 = erased
-- DASHI.Geometry.ProjectionDefect.Additive._+_
d__'43'__22 :: T_Additive_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__22 v0
  = case coe v0 of
      C_Additive'46'constructor_39 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ProjectionDefect.Additive.0#
d_0'35'_24 :: T_Additive_8 -> AgdaAny
d_0'35'_24 v0
  = case coe v0 of
      C_Additive'46'constructor_39 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ProjectionDefect.Additive.-_
d_'45'__26 :: T_Additive_8 -> AgdaAny -> AgdaAny
d_'45'__26 v0
  = case coe v0 of
      C_Additive'46'constructor_39 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect
d_ProjectionDefect_32 a0 a1 = ()
data T_ProjectionDefect_32
  = C_ProjectionDefect'46'constructor_761 (AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- DASHI.Geometry.ProjectionDefect._._+_
d__'43'__40 :: T_Additive_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__40 v0 = coe d__'43'__22 (coe v0)
-- DASHI.Geometry.ProjectionDefect._.-_
d_'45'__42 :: T_Additive_8 -> AgdaAny -> AgdaAny
d_'45'__42 v0 = coe d_'45'__26 (coe v0)
-- DASHI.Geometry.ProjectionDefect._.0#
d_0'35'_44 :: T_Additive_8 -> AgdaAny
d_0'35'_44 v0 = coe d_0'35'_24 (coe v0)
-- DASHI.Geometry.ProjectionDefect._.Carrier
d_Carrier_46 :: T_Additive_8 -> ()
d_Carrier_46 = erased
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect._._+_
d__'43'__68 ::
  T_Additive_8 ->
  T_ProjectionDefect_32 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__68 v0 ~v1 = du__'43'__68 v0
du__'43'__68 :: T_Additive_8 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__68 v0 = coe d__'43'__22 (coe v0)
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect._.-_
d_'45'__70 ::
  T_Additive_8 -> T_ProjectionDefect_32 -> AgdaAny -> AgdaAny
d_'45'__70 v0 ~v1 = du_'45'__70 v0
du_'45'__70 :: T_Additive_8 -> AgdaAny -> AgdaAny
du_'45'__70 v0 = coe d_'45'__26 (coe v0)
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect._.0#
d_0'35'_72 :: T_Additive_8 -> T_ProjectionDefect_32 -> AgdaAny
d_0'35'_72 v0 ~v1 = du_0'35'_72 v0
du_0'35'_72 :: T_Additive_8 -> AgdaAny
du_0'35'_72 v0 = coe d_0'35'_24 (coe v0)
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect._.Carrier
d_Carrier_74 :: T_Additive_8 -> T_ProjectionDefect_32 -> ()
d_Carrier_74 = erased
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect.P
d_P_76 :: T_ProjectionDefect_32 -> AgdaAny -> AgdaAny
d_P_76 v0
  = case coe v0 of
      C_ProjectionDefect'46'constructor_761 v1 v2 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect.D
d_D_78 :: T_ProjectionDefect_32 -> AgdaAny -> AgdaAny
d_D_78 v0
  = case coe v0 of
      C_ProjectionDefect'46'constructor_761 v1 v2 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect.D-def
d_D'45'def_82 ::
  T_ProjectionDefect_32 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_D'45'def_82 = erased
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect.P-idem
d_P'45'idem_86 ::
  T_ProjectionDefect_32 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_P'45'idem_86 = erased
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect.Orth
d_Orth_88 :: T_ProjectionDefect_32 -> AgdaAny -> AgdaAny -> ()
d_Orth_88 = erased
-- DASHI.Geometry.ProjectionDefect.ProjectionDefect.Orth-PD
d_Orth'45'PD_92 :: T_ProjectionDefect_32 -> AgdaAny -> AgdaAny
d_Orth'45'PD_92 v0
  = case coe v0 of
      C_ProjectionDefect'46'constructor_761 v1 v2 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError

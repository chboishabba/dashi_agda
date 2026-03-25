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

module MAlonzo.Code.DASHI.Physics.Closure.MinimalAlgebraicClosureTheorem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage
import qualified MAlonzo.Code.DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem
import qualified MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem

-- DASHI.Physics.Closure.MinimalAlgebraicClosureTheorem.minimalConstraintGaugePackage
d_minimalConstraintGaugePackage_8 ::
  MAlonzo.Code.DASHI.Physics.Closure.CanonicalConstraintGaugePackage.T_CanonicalConstraintGaugePackage_8
d_minimalConstraintGaugePackage_8
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.ParametricGaugeConstraintTheorem.d_canonicalConstraintGaugePackage_44
-- DASHI.Physics.Closure.MinimalAlgebraicClosureTheorem.minimalAlgebraicClosureTheorem
d_minimalAlgebraicClosureTheorem_10 ::
  MAlonzo.Code.DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem.T_ParametricAlgebraicClosureTheorem_10
d_minimalAlgebraicClosureTheorem_10
  = coe
      MAlonzo.Code.DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem.d_parametricAlgebraicClosureTheorem_60
      (coe d_minimalConstraintGaugePackage_8)

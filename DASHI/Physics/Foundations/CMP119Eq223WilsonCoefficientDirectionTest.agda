{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119Eq223WilsonCoefficientDirectionTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119Eq223WilsonCoefficientDirectionExact as W

coefficientDirectionExact : W.eq223WilsonCoefficientDirectionIsExact ≡ true
coefficientDirectionExact = refl

nonWilsonFrozen : W.eq223CoefficientDirectionAddsNoERBVVariation ≡ true
nonWilsonFrozen = refl

finiteInsertionFixed : W.finiteWilsonInsertionNoLongerSemanticDebt ≡ true
finiteInsertionFixed = refl

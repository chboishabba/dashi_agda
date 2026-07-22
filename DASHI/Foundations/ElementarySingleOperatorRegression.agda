module DASHI.Foundations.ElementarySingleOperatorRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Base369 using (tri-low; tri-mid; tri-high)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.TernaryElementaryOperatorCandidate

------------------------------------------------------------------------
-- Focused definitional witnesses.  The semantic compiler theorem lives in
-- ElementarySingleOperator; this module ensures the intended concrete trees
-- remain wired and the ternary slot/address bridge stays canonical.

expTreeShape :
  compileEML (expE (varE zero))
  ≡ emlM (varM zero) oneM
expTreeShape = refl

logTreeShape :
  compileEML (logE (varE zero))
  ≡ emlM oneM
      (emlM
        (emlM oneM (varM zero))
        oneM)
logTreeShape = refl

subTreeShape :
  compileEML (subE (varE zero) oneE)
  ≡ emlM
      (emlM oneM
        (emlM
          (emlM oneM (varM zero))
          oneM))
      (emlM oneM oneM)
subTreeShape = refl

generatedUnitShape :
  generatedUnit zero
  ≡ nodeT (varT zero) (varT zero) (varT zero)
generatedUnitShape = refl

leftSlotCanonical : leftSlot ≡ tri-low
leftSlotCanonical = refl

middleSlotCanonical : middleSlot ≡ tri-mid
middleSlotCanonical = refl

rightSlotCanonical : rightSlot ≡ tri-high
rightSlotCanonical = refl

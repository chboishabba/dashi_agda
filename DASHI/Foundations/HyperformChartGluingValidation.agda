module DASHI.Foundations.HyperformChartGluingValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.HyperformChartGluingExact as Glue

identityNatGluing :
  Glue.SameObjectChartGluing Nat Nat _≡_
identityNatGluing = record
  { Glue.chartA = λ n → n
  ; Glue.chartB = λ n → n
  ; Glue.glueOnOverlap = λ n → refl
  }

identityNatObserver :
  Glue.ObserverWithFibre Nat Nat
identityNatObserver = record
  { Glue.observe = λ n → n
  }

identityNatLiesInOwnFibre :
  (n : Nat) →
  Glue.ObserverFibre identityNatObserver n n
identityNatLiesInOwnFibre n = refl

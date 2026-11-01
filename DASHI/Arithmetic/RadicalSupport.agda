module DASHI.Arithmetic.RadicalSupport where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int )
open import DASHI.Arithmetic.ArithmeticPrimeProfileBridge using
  ( bridgePrimeProfile )
open import DASHI.Arithmetic.GlobalPressure using
  ( totalPressure )
open import DASHI.Statistics.PrimeProfileStats using
  ( PrimeProfileStats
  ; primeProfileMask
  ; primeProfileScore
  ; supportMaskWeights
  )
open import DASHI.Arithmetic.PrimeIndexedPressure using
  ( sum15 )
open import Ontology.Hecke.FactorVecInstances using
  ( SupportMask )

------------------------------------------------------------------------
-- Radical-style support over the tracked 15-prime carrier.
--
-- This is intentionally conservative: it uses the boolean support mask of
-- the repo-native prime-profile carrier, so multiplicity is forgotten here.
-- The exact arithmetic comparison to totalPressure remains the open gap.

radicalSupportMask : PrimeProfileStats → SupportMask
radicalSupportMask = primeProfileMask

radicalSupportScore : PrimeProfileStats → Nat
radicalSupportScore s = sum15 (supportMaskWeights (radicalSupportMask s))

radicalSupportScore≡primeProfileScore :
  ∀ s →
  radicalSupportScore s ≡ primeProfileScore s
radicalSupportScore≡primeProfileScore s =
  sym (cong sum15 (PrimeProfileStats.carrierWeightsMatches s))

radicalSupportOfPair : Int → Int → Nat
radicalSupportOfPair x y = radicalSupportScore (bridgePrimeProfile x y)

------------------------------------------------------------------------
-- Exact obstruction surface.
--
-- This is the theorem shape we want, but it is not proved by the current
-- arithmetic surfaces because the repo still lacks a multiplicity-to-presence
-- bridge from valuation depth to a boolean radical mask.

RadicalSupportComparison : Set
RadicalSupportComparison =
  ∀ x y →
  totalPressure x y ≤ radicalSupportOfPair x y

record RadicalSupportSurface : Set₁ where
  field
    statsSupport : PrimeProfileStats → Nat
    statsSupportMask :
      PrimeProfileStats → SupportMask
    statsSupportMaskScore :
      ∀ s →
      statsSupport s ≡ sum15 (supportMaskWeights (statsSupportMask s))
    statsSupportMatchesProfileScore :
      ∀ s →
      statsSupport s ≡ primeProfileScore s
    pairSupport : Int → Int → Nat
    comparisonSurface : Set

open RadicalSupportSurface public

radicalSupportSurface : RadicalSupportSurface
radicalSupportSurface = record
  { statsSupport = radicalSupportScore
  ; statsSupportMask = radicalSupportMask
  ; statsSupportMaskScore = λ _ → refl
  ; statsSupportMatchesProfileScore = radicalSupportScore≡primeProfileScore
  ; pairSupport = radicalSupportOfPair
  ; comparisonSurface = RadicalSupportComparison
  }

module DASHI.Biology.BalancedTernaryHarmonicCarrierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Ingrid Daubechies,
-- "Ten Lectures on Wavelets", SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
--
-- Volodymyr Nekrashevych,
-- "Self-Similar Groups", American Mathematical Society, 2005.
-- DOI: 10.1090/surv/117.
--
-- DASHI CONTRIBUTION
-- Replace an unexplained tenfold multiplicity by T^2 disjoint-union {j}.
-- Every coarse channel has a 3^9 fine-frequency coordinate.  The elementary
-- channel product is kept distinct from the full function-space assignment.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat using (_+_; _*_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)

data BalancedTrit : Set where
  negativeTrit : BalancedTrit
  zeroTrit : BalancedTrit
  positiveTrit : BalancedTrit

record BalancedPair : Set where
  constructor balancedPair
  field
    firstTrit : BalancedTrit
    secondTrit : BalancedTrit

open BalancedPair public

data CoarseChannel : Set where
  ordinaryChannel : BalancedPair → CoarseChannel
  completionJ : CoarseChannel

canonicalCoarseChannels : List CoarseChannel
canonicalCoarseChannels =
  ordinaryChannel (balancedPair negativeTrit negativeTrit)
  ∷ ordinaryChannel (balancedPair negativeTrit zeroTrit)
  ∷ ordinaryChannel (balancedPair negativeTrit positiveTrit)
  ∷ ordinaryChannel (balancedPair zeroTrit negativeTrit)
  ∷ ordinaryChannel (balancedPair zeroTrit zeroTrit)
  ∷ ordinaryChannel (balancedPair zeroTrit positiveTrit)
  ∷ ordinaryChannel (balancedPair positiveTrit negativeTrit)
  ∷ ordinaryChannel (balancedPair positiveTrit zeroTrit)
  ∷ ordinaryChannel (balancedPair positiveTrit positiveTrit)
  ∷ completionJ
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ rest) = 1 + listCount rest

coarseChannelCountIsTen : listCount canonicalCoarseChannels ≡ 10
coarseChannelCountIsTen = refl

FineFrequency : Set
FineFrequency = Fin 19683

ElementaryHarmonicChannel : Set
ElementaryHarmonicChannel = CoarseChannel × FineFrequency

FullFineAssignment : Set
FullFineAssignment = CoarseChannel → FineFrequency

jFine : FullFineAssignment → FineFrequency
jFine assignment = assignment completionJ

fineAt : CoarseChannel → FullFineAssignment → FineFrequency
fineAt channel assignment = assignment channel

ordinaryCoarseDimension : Nat
ordinaryCoarseDimension = 9

completionCoarseDimension : Nat
completionCoarseDimension = 1

fineFrequencyDimension : Nat
fineFrequencyDimension = 19683

ordinaryHarmonicDimension : Nat
ordinaryHarmonicDimension = ordinaryCoarseDimension * fineFrequencyDimension

completionHarmonicDimension : Nat
completionHarmonicDimension =
  completionCoarseDimension * fineFrequencyDimension

elementaryHarmonicDimension : Nat
elementaryHarmonicDimension =
  ordinaryHarmonicDimension + completionHarmonicDimension

ordinaryHarmonicDimensionIsThreePowerEleven :
  ordinaryHarmonicDimension ≡ 177147
ordinaryHarmonicDimensionIsThreePowerEleven = refl

completionHarmonicDimensionIsThreePowerNine :
  completionHarmonicDimension ≡ 19683
completionHarmonicDimensionIsThreePowerNine = refl

elementaryHarmonicDimensionIs196830 :
  elementaryHarmonicDimension ≡ 196830
elementaryHarmonicDimensionIs196830 = refl

-- This boundary quantifies over proposition carriers (`Set`), so the record
-- itself necessarily lives one universe higher.  The previous `: Set`
-- annotation was a universe inconsistency; changing only the record sort to
-- `Set₁` preserves every field and every boundary statement.
record HarmonicCarrierBoundary : Set₁ where
  constructor harmonicCarrierBoundary
  field
    completionJIsOrdinaryBalancedPair : Set
    completionJIsNotOrdinaryBalancedPair :
      completionJIsOrdinaryBalancedPair → Set
    elementaryChannelCarrierEqualsFullAssignmentSpace : Set
    elementaryChannelCarrierDoesNotEqualFullAssignmentSpace :
      elementaryChannelCarrierEqualsFullAssignmentSpace → Set
    harmonicCarrierConstructsMonsterAction : Set
    harmonicCarrierDoesNotConstructMonsterAction :
      harmonicCarrierConstructsMonsterAction → Set

canonicalHarmonicCarrierBoundary : HarmonicCarrierBoundary
canonicalHarmonicCarrierBoundary =
  harmonicCarrierBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)

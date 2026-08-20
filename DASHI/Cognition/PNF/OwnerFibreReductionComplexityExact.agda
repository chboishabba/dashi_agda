module DASHI.Cognition.PNF.OwnerFibreReductionComplexityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Cognition.PNF.ComplexityArithmetic
  using (_+ᶜ_; _≤ᶜ_)

------------------------------------------------------------------------
-- Physical witness for repeated full-fibre reduction.
--
-- If one new proposal arrives in each wave and the implementation reduces the
-- whole accumulated owner fibre after every wave, its proposal-scan exposure is
-- 1 + 2 + ... + k.  This is an execution-cost witness only; it does not license
-- incremental semantic reduction.
------------------------------------------------------------------------

repeatedUnitWaveExposure : Nat → Nat
repeatedUnitWaveExposure zero = zero
repeatedUnitWaveExposure (suc k) = suc k +ᶜ repeatedUnitWaveExposure k

appendOnlyUnitWaveExposure : Nat → Nat
appendOnlyUnitWaveExposure k = k

eightWaveFullRescanExposure : repeatedUnitWaveExposure 8 ≡ 36
eightWaveFullRescanExposure = refl

eightWaveAppendOnlyExposure : appendOnlyUnitWaveExposure 8 ≡ 8
eightWaveAppendOnlyExposure = refl

------------------------------------------------------------------------
-- The semantic proof obligation required before replacing full-fibre reduction
-- by prefix-summary + delta-summary composition.
------------------------------------------------------------------------

_++ᶠ_ : ∀ {A : Set} → List A → List A → List A
[] ++ᶠ ys = ys
(x ∷ xs) ++ᶠ ys = x ∷ (xs ++ᶠ ys)

record IncrementalReductionSufficiency
  (Proposal Summary : Set)
  : Set where
  field
    summarize : List Proposal → Summary
    combine : Summary → Summary → Summary
    emptyIdentity : ∀ xs → combine (summarize []) (summarize xs) ≡ summarize xs
    appendHomomorphism : ∀ prefix delta →
      combine (summarize prefix) (summarize delta)
      ≡ summarize (prefix ++ᶠ delta)

open IncrementalReductionSufficiency public

incrementalSummaryEqualsFullReduction :
  ∀ {Proposal Summary : Set}
    (law : IncrementalReductionSufficiency Proposal Summary)
    (prefix delta : List Proposal) →
  combine law (summarize law prefix) (summarize law delta)
  ≡ summarize law (prefix ++ᶠ delta)
incrementalSummaryEqualsFullReduction law prefix delta =
  appendHomomorphism law prefix delta

------------------------------------------------------------------------
-- Independent owner fibres have a weaker requirement: their reductions may be
-- scheduled/reordered when their state actions commute.  Same-owner incremental
-- reduction needs the stronger homomorphism above and must not be inferred from
-- this commutation law.
------------------------------------------------------------------------

record IndependentOwnerReduction
  (Owner Delta State : Set)
  : Set where
  field
    ownerOf : Delta → Owner
    apply : Delta → State → State
    Independent : Delta → Delta → Set
    commute : ∀ {left right state} →
      Independent left right →
      apply left (apply right state) ≡ apply right (apply left state)

open IndependentOwnerReduction public

record OneWaveOwnerScanBound : Set where
  constructor oneWaveOwnerScanBound
  field
    activeOwnerProposals : Nat
    scannedProposalUnits : Nat
    boundedByActiveFibre : scannedProposalUnits ≤ᶜ activeOwnerProposals

open OneWaveOwnerScanBound public

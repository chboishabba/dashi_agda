module DASHI.Governance.DevelopmentalTriadicFiniteQuotientWeldExact where

-- Exact adapter from an existing DASHI finite developmental candidate leaf
-- to the canonical balanced-ternary Z/3^nZ quotient tower.
-- This is an encoding of FOUR FINITE SYNTHETIC histories, not a validated
-- mapping of actual ACE scores, biological sensitive periods or people.
-- Background: DASHI.Foundations.TriadicFiniteQuotient (original owner).
-- All finite quotient identities are inherited, not recreated.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; neg; zer; pos; TritPrefix; []; _∷_)
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Governance.SituatedDevelopmentalUltrametricExact as Dev

childhoodDigit : Dev.ChildhoodBranch → Trit
childhoodDigit Dev.sharedBranch = zer
childhoodDigit Dev.otherBranch = pos

laterDigit : Dev.AdultBranch → Trit
laterDigit Dev.localA = zer
laterDigit Dev.localB = pos

-- First retained digit is the selected early branch; second is the
-- selected later branch. Canonical 3-adic residue, NOT a clinical score.
encodeHistory : Dev.DevelopmentalLeaf → Q.Residue3Pow 2
encodeHistory (Dev.developmental-leaf childhood adulthood) =
  childhoodDigit childhood ∷ laterDigit adulthood ∷ []

earlyProjection : Dev.DevelopmentalLeaf → Q.Residue3Pow 1
earlyProjection leaf = childhoodDigit (Dev.childhood leaf) ∷ []

canonicalReductionMatchesEarlyHistory :
  (leaf : Dev.DevelopmentalLeaf) →
  Q.reduce (encodeHistory leaf) ≡ earlyProjection leaf
canonicalReductionMatchesEarlyHistory (Dev.developmental-leaf _ _) = refl

-- An explicit canonical zero section is exact, but not a recovery of
-- unknown later developmental observations.
canonicalZeroLiftIsRightSection :
  (prefix : Q.Residue3Pow 1) →
  Q.reduce (Q.zeroLift prefix) ≡ prefix
canonicalZeroLiftIsRightSection = Q.reduce-zeroLift

sameEarlyBranchDifferentLaterInformation :
  Q.reduce (encodeHistory Dev.leafA) ≡
  Q.reduce (encodeHistory Dev.leafB)
sameEarlyBranchDifferentLaterInformation = refl

laterHistoryReallyLost :
  encodeHistory Dev.leafA ≡ encodeHistory Dev.leafB → ⊥
laterHistoryReallyLost ()

differentEarlyBranchDistinctAtDepthOne :
  Q.reduce (encodeHistory Dev.leafA) ≡
  Q.reduce (encodeHistory Dev.leafC) → ⊥
differentEarlyBranchDistinctAtDepthOne ()

-- Encodings may feed already proved compatible finite kernels, but such
-- kernels do NOT by themselves predict an individual's endocrine biology.
record ValidatedDevelopmentalProjection (PersonHistory : Set) : Set₁ where
  field
    mapOriginalHistory : PersonHistory → Q.Residue3Pow 2
    originalChronologyAuthenticated : PersonHistory → Set
    developmentalWindowCalibration : PersonHistory → Set
    biologicalResponseValidated : PersonHistory → Set

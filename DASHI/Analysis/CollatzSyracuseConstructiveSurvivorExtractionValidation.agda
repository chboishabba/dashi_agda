module DASHI.Analysis.CollatzSyracuseConstructiveSurvivorExtractionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseConstructiveSurvivorExtractionExact as Extract

finiteBarrierExtractionPaid :
  Extract.ConstructiveSurvivorExtractionBoundary.finiteBarrierExtractionPaid
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 1
finiteBarrierExtractionPaid = refl

strictDescentBuildsFiniteBarrierPaid :
  Extract.ConstructiveSurvivorExtractionBoundary.strictDescentBuildsFiniteBarrierPaid
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 1
strictDescentBuildsFiniteBarrierPaid = refl

finiteBarrierStrictDescentEquivalencePaid :
  Extract.ConstructiveSurvivorExtractionBoundary.finiteBarrierStrictDescentEquivalencePaid
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 1
finiteBarrierStrictDescentEquivalencePaid = refl

noInfiniteGivesDoubleNegatedDescentPaid :
  Extract.ConstructiveSurvivorExtractionBoundary.noInfiniteGivesDoubleNegatedDescentPaid
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 1
noInfiniteGivesDoubleNegatedDescentPaid = refl

noInversePointGivesDoubleNegatedDescentPaid :
  Extract.ConstructiveSurvivorExtractionBoundary.noInversePointGivesDoubleNegatedDescentPaid
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 1
noInversePointGivesDoubleNegatedDescentPaid = refl

markovNotSilentlyOwned :
  Extract.ConstructiveSurvivorExtractionBoundary.natSearchMarkovOwnedUnconditionally
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 0
markovNotSilentlyOwned = refl

mereNoInfiniteDoesNotConstructDescent :
  Extract.ConstructiveSurvivorExtractionBoundary.noInfiniteAutomaticallyConstructsDescent
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 0
mereNoInfiniteDoesNotConstructDescent = refl

{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.ConjunctiveExposureLocalityRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤)
open import Data.Nat.Properties as NatP

open import DASHI.Cognition.PNF.ConjunctiveExposureLocalityExact

Legacy Optimized : ⊤ → Set
Legacy _ = ⊤
Optimized _ = ⊤

exactParity : ExtensionalParity
exactParity = record
  { FineRow = ⊤
  ; legacyRelation = Legacy
  ; optimizedRelation = Optimized
  ; relationExact = λ _ → refl
  }

-- Exact relation equality does not determine physical exposure.  Four and
-- forty are deliberately incompatible while the semantic relation is identical.
parityExposureCounterexample : ExtensionalParityExposureCounterexample
parityExposureCounterexample = record
  { parityWitness = exactParity
  ; firstExposure = 4
  ; secondExposure = 40
  ; exposureDiffers = λ ()
  }

-- A concrete bounded observation.  The three bounds normalize to reflexive
-- inequalities, keeping the regression independent of implementation-specific
-- arithmetic lemmas.
observation : PhysicalWorkObservation
observation = physicalWorkObservation 5 2 7 7 3 3 0

bounded : BoundedPhysicalWork observation
bounded = boundedPhysicalWork
  1
  1
  1
  NatP.≤-refl
  NatP.≤-refl
  NatP.≤-refl

sparseExactTransition : PhysicallySparseExactTransition
sparseExactTransition = record
  { parity = exactParity
  ; observation = observation
  ; boundedWork = bounded
  }

candidateMaskCountIsSixteen : candidateMaskCardinality ≡ 16
candidateMaskCountIsSixteen = refl

retentionMaskCountIsEight : retentionMaskCardinality ≡ 8
retentionMaskCountIsEight = refl

module DASHI.Physics.Closure.NSTriadKNDongLiFrequencyLocalizedCoercivityAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Dong Li.
-- Author: Dong Li.
-- Title: "On a Frequency Localized Bernstein Inequality and Some Generalized
-- Poincare-Type Inequalities".
-- Venue/year: arXiv:1212.0183v1, 2012.
-- DOI: 10.48550/arXiv.1212.0183.
-- Uses: Theorem 1.1, Corollary 1.6, Theorem 1.10, and Corollary 1.13: improved
-- frequency-localized fractional heat-flow decay and the resulting coercive
-- lower bounds for fractional Laplacians on Euclidean and periodic domains.
-- Relationship: records a dissipative coercivity lane.  It is not the finite
-- support counting Bernstein inequality, does not reverse a low-pass
-- derivative estimate into decay, and does not directly discharge the
-- nonlinear output-relocation Schur conditions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNBernsteinDirectionAudit as Direction
import DASHI.Physics.Closure.NSTriadKNRationalFiniteBernstein as Finite

record DongLiFrequencyLocalizedCoercivitySurface : Set where
  constructor surface
  field
    euclideanAnnularSupport : Bool
    fractionalRangeZeroBelowAlphaAtMostTwo : Bool
    lebesgueRangeOneBelowQBelowInfinity : Bool
    improvedHeatFlowDecayRecorded : Bool
    coerciveBernsteinLowerBoundRecorded : Bool
    periodicMeanZeroVersionRecorded : Bool
    generalizedPoincareVersionRecorded : Bool
    sharpConstantOneHeatFlowMechanismRecorded : Bool

open DongLiFrequencyLocalizedCoercivitySurface public

dongLiCoercivitySurface : DongLiFrequencyLocalizedCoercivitySurface
dongLiCoercivitySurface = surface
  true true true true true true true true

record DongLiRepositoryRelationshipReceipt : Set where
  constructor receipt
  field
    finiteCountingBernsteinAlreadyClosed :
      Finite.finiteBernsteinCountingClosed ≡ true
    directionAuditAlreadySeparatesLowPassCost :
      Direction.bernsteinAloneSuppliesLowFrequencyDecay ≡ false
    highHighToLowStillNeedsCancellationOrSobolevInput :
      Direction.highHighToLowNeedsCancellationOrSobolevInput ≡ true
    coercivityIsNotCountingUpperBound : Bool
    coercivityDoesNotDirectlyCloseSchurCheckA : Bool
    coercivityCanFeedDissipativeAbsorption : Bool

open DongLiRepositoryRelationshipReceipt public

dongLiRepositoryRelationshipReceipt : DongLiRepositoryRelationshipReceipt
dongLiRepositoryRelationshipReceipt = receipt
  Finite.finiteBernsteinCountingClosedIsTrue
  Direction.bernsteinAloneSuppliesLowFrequencyDecayIsFalse
  Direction.highHighToLowNeedsCancellationOrSobolevInputIsTrue
  true false true

dongLiFrequencyLocalizedCoercivityRecorded : Bool
dongLiFrequencyLocalizedCoercivityRecorded = true

dongLiDirectlyClosesOutputRelocationCheckA : Bool
dongLiDirectlyClosesOutputRelocationCheckA = false

dongLiSuppliesFiniteCountingBernstein : Bool
dongLiSuppliesFiniteCountingBernstein = false

dongLiRelevantToDissipativeAbsorption : Bool
dongLiRelevantToDissipativeAbsorption = true

dongLiFrequencyLocalizedCoercivityRecordedIsTrue :
  dongLiFrequencyLocalizedCoercivityRecorded ≡ true
dongLiFrequencyLocalizedCoercivityRecordedIsTrue = refl

dongLiDirectlyClosesOutputRelocationCheckAIsFalse :
  dongLiDirectlyClosesOutputRelocationCheckA ≡ false
dongLiDirectlyClosesOutputRelocationCheckAIsFalse = refl

dongLiSuppliesFiniteCountingBernsteinIsFalse :
  dongLiSuppliesFiniteCountingBernstein ≡ false
dongLiSuppliesFiniteCountingBernsteinIsFalse = refl

dongLiRelevantToDissipativeAbsorptionIsTrue :
  dongLiRelevantToDissipativeAbsorption ≡ true
dongLiRelevantToDissipativeAbsorptionIsTrue = refl

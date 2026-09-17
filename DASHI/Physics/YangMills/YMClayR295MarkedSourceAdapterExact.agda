{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR295MarkedSourceAdapterExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell

------------------------------------------------------------------------
-- R295 -> generic marked-source adapter.
--
-- R295 already owns, on the exact finite T5 measure family:
--
--   * the expectation/product algebra;
--   * literal source directions for every selected T5 observable;
--   * mixed log-J response = exact connected covariance;
--   * a magnitude bound by the selected rooted shell at every cutoff.
--
-- The dense-marked F1 producer introduced on PR #996 consumes the generic
-- `MarkedTwoSourceResponse` / `SeparationDecayProducer` interface.  Those are
-- not new physical inputs: they can be built definitionally from R295.
--
-- This module is therefore a pure carrier/interface compiler.  It does NOT
-- prove the remaining dense-L2 carrier or envelope-to-c_k||psi||^2 weld.
------------------------------------------------------------------------

record ObservablePair (Observable : Set) : Set where
  constructor pair
  field
    left : Observable
    right : Observable

open ObservablePair public

r295MarkedResponse :
  ∀ {Measure TestObservable}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (presentation : R295.DirectT5StateFamilyJPresentation dataSet extension) →
  Marked.MarkedTwoSourceResponse TestObservable (Nat → ℚ)
r295MarkedResponse dataSet extension presentation =
  let
    algebra = R295.t5FiniteExpectationAlgebra dataSet extension
    meaning = R295.meaning presentation
  in
  record
    { Marked.MarkedTwoSourceResponse.multiply =
        Cumulant.multiply algebra
    ; Marked.MarkedTwoSourceResponse.subtract =
        Cumulant.subtract algebra
    ; Marked.MarkedTwoSourceResponse.expectation =
        Cumulant.expectation algebra
    ; Marked.MarkedTwoSourceResponse.productExpectation =
        λ first second →
          Cumulant.expectation algebra
            (Cumulant.productObservable algebra first second)
    ; Marked.MarkedTwoSourceResponse.mixedLogPartitionDerivative =
        λ first second →
          Cumulant.literalMixedSecondLogDerivative meaning
            (Cumulant.sourceDirectionOf meaning first)
            (Cumulant.sourceDirectionOf meaning second)
    ; Marked.MarkedTwoSourceResponse.mixedDerivativeMeaning =
        Cumulant.literalMixedLogDerivativeIsConnectedCovariance meaning
    }

r295MarkedSeparationDecayProducer :
  ∀ {Measure TestObservable}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (presentation : R295.DirectT5StateFamilyJPresentation dataSet extension) →
  Marked.SeparationDecayProducer
    (r295MarkedResponse dataSet extension presentation)
r295MarkedSeparationDecayProducer dataSet extension presentation = record
  { Marked.SeparationDecayProducer.absoluteValue =
      λ sequence cutoff → R278.magnitude extension (sequence cutoff)
  ; Marked.SeparationDecayProducer.LessEqual =
      λ lower upper → ∀ cutoff → lower cutoff ≤ upper cutoff
  ; Marked.SeparationDecayProducer.distance = pair
  ; Marked.SeparationDecayProducer.decayEnvelope =
      λ observablePair cutoff →
        Shell.rootedShell
          (R295.shellData presentation)
          (R295.scaleOf presentation cutoff)
          (R295.volumeOf presentation cutoff)
          (R295.connectingRoot presentation cutoff
            (left observablePair) (right observablePair))
          (R295.physicalDistance presentation
            (left observablePair) (right observablePair))
  ; Marked.SeparationDecayProducer.mixedDerivativeDecay =
      λ first second cutoff →
        R295.differentiatedSourceMagnitudeBoundOnSelectedDirections
          presentation cutoff first second
  }

------------------------------------------------------------------------
-- Direct compiler consequence: every R295 presentation is already a valid
-- generic marked-source decay producer.  Consumers should not request another
-- theorem saying merely that "selected marked decay exists".
------------------------------------------------------------------------

r295ConnectedCorrelationDecay :
  ∀ {Measure TestObservable}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (presentation : R295.DirectT5StateFamilyJPresentation dataSet extension)
    (first second : TestObservable) →
  let
    response = r295MarkedResponse dataSet extension presentation
    producer = r295MarkedSeparationDecayProducer dataSet extension presentation
  in
  Marked.LessEqual producer
    (Marked.absoluteValue producer
      (Marked.connectedCorrelation response first second))
    (Marked.decayEnvelope producer
      (Marked.distance producer first second))
r295ConnectedCorrelationDecay dataSet extension presentation first second =
  Marked.connectedCorrelationDecayFromMarkedSource
    (r295MarkedSeparationDecayProducer dataSet extension presentation)
    first second

------------------------------------------------------------------------
-- Bookkeeping.
------------------------------------------------------------------------

r295BuildsGenericMarkedResponse : Bool
r295BuildsGenericMarkedResponse = true

r295BuildsGenericMarkedResponseIsTrue :
  r295BuildsGenericMarkedResponse ≡ true
r295BuildsGenericMarkedResponseIsTrue = refl

r295BuildsGenericSeparationDecayProducer : Bool
r295BuildsGenericSeparationDecayProducer = true

r295BuildsGenericSeparationDecayProducerIsTrue :
  r295BuildsGenericSeparationDecayProducer ≡ true
r295BuildsGenericSeparationDecayProducerIsTrue = refl

selectedMarkedDecayRequiresIndependentF1Payment : Bool
selectedMarkedDecayRequiresIndependentF1Payment = false

selectedMarkedDecayRequiresIndependentF1PaymentIsFalse :
  selectedMarkedDecayRequiresIndependentF1Payment ≡ false
selectedMarkedDecayRequiresIndependentF1PaymentIsFalse = refl

-- Source-written explicit Agda term in this tranche.  Keep the metadata
-- fail-closed until an exact-head Agda kernel run is observed.
r295MarkedSourceAdapterLevel : ProofLevel
r295MarkedSourceAdapterLevel = conditional

-- The underlying physical selected-J localization remains exactly the R295
-- source-facing level; the adapter does not alter its proof status.
r295LiteralSelectedJLocalizationLevel : ProofLevel
r295LiteralSelectedJLocalizationLevel =
  R295.round295LiteralT5JDirectionLocalizationLevel

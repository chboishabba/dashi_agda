module DASHI.Wikimedia.ShemCandidateGateBidiExact where

-- H25 candidate realization, NOT a source-attested CLARA recurrence.
-- Retain zero as a field point. Missing occupancy is outside this carrier.
-- The F return in the source graph has an earlier J index; interpreting it
-- as a next-column inversion is only the candidate audited here.
open import DASHI.Core.Prelude
import DASHI.Wikimedia.KeyShoeCLARAOperatorBoundaryExact as CLARA
open import DASHI.Wikimedia.KeyShoeNativeFieldIncidenceExact
  using (Point; add; sub; inverse; inverseInvolutive)
open import DASHI.Wikimedia.KeyShoeFieldLawMovingFrameExact
  using (addSub; subAdd)

gateStep : CLARA.Gate → Point → Point → Point
gateStep CLARA.mContinue delta r = add delta r
gateStep CLARA.fReturn delta r = inverse (add delta r)

gateBack : CLARA.Gate → Point → Point → Point
gateBack CLARA.mContinue delta s = sub s delta
gateBack CLARA.fReturn delta s = sub (inverse s) delta

gateBackStep : (g : CLARA.Gate) (delta r : Point) →
  gateBack g delta (gateStep g delta r) ≡ r
gateBackStep CLARA.mContinue delta r = subAdd delta r
gateBackStep CLARA.fReturn delta r
  rewrite inverseInvolutive (add delta r) = subAdd delta r

gateStepBack : (g : CLARA.Gate) (delta s : Point) →
  gateStep g delta (gateBack g delta s) ≡ s
gateStepBack CLARA.mContinue delta s = addSub delta s
gateStepBack CLARA.fReturn delta s
  rewrite addSub delta (inverse s) = inverseInvolutive s

-- Bidirectional local membership: this is a proof about a chosen gate;
-- neither existence nor selection of the actual source gate is supplied.
edgeForwardToBackward : (g : CLARA.Gate) (delta r s : Point) →
  gateStep g delta r ≡ s → gateBack g delta s ≡ r
edgeForwardToBackward g delta r s e =
  trans (cong (gateBack g delta) (sym e)) (gateBackStep g delta r)

edgeBackwardToForward : (g : CLARA.Gate) (delta r s : Point) →
  gateBack g delta s ≡ r → gateStep g delta r ≡ s
edgeBackwardToForward g delta r s e =
  trans (cong (gateStep g delta) (sym e)) (gateStepBack g delta s)

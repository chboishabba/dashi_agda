module DASHI.Physics.Closure.NSTriadKNLiteralSpectatorSameOutputRepairRound588Exact where

------------------------------------------------------------------------
-- ROUND588 / SAME-OUTPUT REPAIR FOR THE LITERAL SPECTATOR-RESOLVENT CARRIER
--
-- R587 specializes the unrestricted nested overlap to the actual R541
-- spectator resolvent W_beta(alpha).  Its first pair wrapper, however, only
-- required the two row cells to have the same final output; it did not require
-- the fixed spectator beta itself to lie in that same output fibre.
--
-- The live R566/R568 forcing square enumerates alpha and beta from one and the
-- same `physicalOutputFiber`.  Therefore the canonical local overlap object is
-- a triple
--
--   beta, alpha_L, alpha_R
--
-- with all three final outputs identical.  This file installs exactly that
-- same-object carrier before any shell or resolvent estimate is attempted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralSpectatorResolventOverlapRound587Exact as R587

record SameOutputSpectatorTriple588 : Set where
  constructor same-output-spectator-triple588
  field
    spectator588 : Physical.PhysicalTriadIncidence
    left588 right588 : Physical.PhysicalTriadIncidence
    leftOutputIsSpectator588 :
      Physical.k left588 ≡ Physical.k spectator588
    rightOutputIsSpectator588 :
      Physical.k right588 ≡ Physical.k spectator588

open SameOutputSpectatorTriple588 public

leftAndRightSameOutput588 :
  (P : SameOutputSpectatorTriple588) →
  Physical.k (left588 P) ≡ Physical.k (right588 P)
leftAndRightSameOutput588 P =
  trans
    (leftOutputIsSpectator588 P)
    (sym (rightOutputIsSpectator588 P))

swapRows588 :
  SameOutputSpectatorTriple588 → SameOutputSpectatorTriple588
swapRows588 P =
  same-output-spectator-triple588
    (spectator588 P)
    (right588 P)
    (left588 P)
    (rightOutputIsSpectator588 P)
    (leftOutputIsSpectator588 P)

------------------------------------------------------------------------
-- Proof-search correction.
------------------------------------------------------------------------

data SpectatorSameOutputResidual588 : Set where
  missingPhysicalRadiusShellFloor588 : SpectatorSameOutputResidual588
  missingLiteralResolventShellEnvelope588 : SpectatorSameOutputResidual588
  missingCutoffUniformSameOutputEnvelopeMass588 : SpectatorSameOutputResidual588
  missingSpacetimeTransport588 : SpectatorSameOutputResidual588

currentResidual588 : SpectatorSameOutputResidual588
currentResidual588 = missingPhysicalRadiusShellFloor588

round588R587SpectatorSameOutputExplicit : Bool
round588R587SpectatorSameOutputExplicit = false

round588CanonicalSpectatorTripleSameOutputExplicit : Bool
round588CanonicalSpectatorTripleSameOutputExplicit = true

round588LeftRightSameOutputCompilerClosed : Bool
round588LeftRightSameOutputCompilerClosed = true

round588ArbitrarySwapInvariantWeightMandatory : Bool
round588ArbitrarySwapInvariantWeightMandatory =
  R587.round587ArbitrarySwapInvariantWeightMandatory

round588PhysicalRadiusShellFloorClosed : Bool
round588PhysicalRadiusShellFloorClosed = false

round588LiteralResolventShellEnvelopeClosed : Bool
round588LiteralResolventShellEnvelopeClosed = false

round588CutoffUniformSameOutputEnvelopeMassClosed : Bool
round588CutoffUniformSameOutputEnvelopeMassClosed = false

round588LeafAClosed : Bool
round588LeafAClosed = false

round588ClayPromotion : Bool
round588ClayPromotion = false

round588CanonicalSpectatorTripleSameOutputExplicitIsTrue :
  round588CanonicalSpectatorTripleSameOutputExplicit ≡ true
round588CanonicalSpectatorTripleSameOutputExplicitIsTrue = refl

round588LeftRightSameOutputCompilerClosedIsTrue :
  round588LeftRightSameOutputCompilerClosed ≡ true
round588LeftRightSameOutputCompilerClosedIsTrue = refl

round588ArbitrarySwapInvariantWeightMandatoryIsFalse :
  round588ArbitrarySwapInvariantWeightMandatory ≡ false
round588ArbitrarySwapInvariantWeightMandatoryIsFalse =
  R587.round587ArbitrarySwapInvariantWeightMandatoryIsFalse

round588ClayPromotionIsFalse : round588ClayPromotion ≡ false
round588ClayPromotionIsFalse = refl

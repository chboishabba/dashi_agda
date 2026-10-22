{-# OPTIONS --safe #-}
module DASHI.WorldModel.VERIDNSCanonicalEvidenceFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.CanonicalClayFrontierExact as Clay
import DASHI.Physics.Closure.NSCanonicalClayResidualExact as NS
import DASHI.Core.BidiResidualApproximationExact as Bidi

-- A complete finite comparison is still evidence about the finite model.
-- The following type is intentionally NOT a constructor for the canonical
-- A1/A2/A3/B4/B123/B7/B-continuation/C-D physical payments.
data NumericalEvidenceStatus : Set where
  finiteComparison : NumericalEvidenceStatus
  heldoutFalsification : NumericalEvidenceStatus
  approximationRefined : NumericalEvidenceStatus

data CanonicalNSLeaf : Set where
  A1 A2 A3 B4 B123 B7 BCont CD : CanonicalNSLeaf

canonical : CanonicalNSLeaf → Clay.CanonicalClayLiveObligation
canonical A1 = Clay.a1PhysicalPopulation
canonical A2 = Clay.a2MajorantDomination
canonical A3 = Clay.a3Continuation
canonical B4 = Clay.b4PhysicalR440Payment
canonical B123 = Clay.b123PhysicalProducers
canonical B7 = Clay.b7IntegratedControl
canonical BCont = Clay.bContinuationInputs
canonical CD = Clay.cdReleasedReconstruction

-- The finite hypotheses to be falsified are different propositions from
-- the physical obligations. In particular, a numerical negative example
-- to an attempted B7 proof currency is not a refutation of B7.
data EvidenceConsequence : Set where
  refineFiniteFibre : EvidenceConsequence
  rejectProposedCurrency : EvidenceConsequence
  revisitSelectedLeaf : EvidenceConsequence

record TypedNSObservation : Set where
  constructor typedNSObservation
  field
    source : NumericalEvidenceStatus
    targets : CanonicalNSLeaf
    consequence : EvidenceConsequence

-- The blocked transition is definitional: numerical evidence carries no
-- evidence for the canonical NS promotion flag.
clayGateStillClosed :
  (receipt : TypedNSObservation) →
  NS.clayNavierStokesPromoted ≡ false
clayGateStillClosed _ = NS.clayNavierStokesPromotedIsFalse

globalGateStillClosed :
  (receipt : TypedNSObservation) →
  Clay.clayNavierStokesPromoted ≡ false
globalGateStillClosed _ = Clay.clayNavierStokesPromotedIsFalse

-- Genuine theorem: same-observer ambiguity can be reduced through a
-- measurement without claiming exact identification of physical dynamics.
measurementFibreRefines :
  {Hidden Measurement : Set}
  (prior : Bidi.ResidualFibre Hidden)
  (measure : Hidden → Measurement)
  (observed : Measurement) →
  Bidi.FibreRefines (Bidi.MeasuredFibre prior measure observed) prior
measurementFibreRefines =
  Bidi.measurementAlwaysRefinesPrior

finiteRefinementNotExactIdentification :
  Bidi.approximatelyConstrainedGrade ≡ Bidi.exactlyIdentifiedGrade → ⊥
finiteRefinementNotExactIdentification =
  Bidi.approximateNotExact

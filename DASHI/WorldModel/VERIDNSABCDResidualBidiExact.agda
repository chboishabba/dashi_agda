{-# OPTIONS --safe #-}
module DASHI.WorldModel.VERIDNSABCDResidualBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.CanonicalClayFrontierExact as Clay
import DASHI.Physics.Closure.NSCanonicalClayResidualExact as NS
import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.ResidualConditionedExperimentPortfolioExact as Portfolio

------------------------------------------------------------------------
-- Explicitly align numerical experimentation with canonical NS A/B/C/D
-- leaves. No experiment is an inhabitant of an analytic proof obligation.
------------------------------------------------------------------------

data NSExperimentalLane : Set where
  APhysicalPopulation APhysicalMajorant AContinuation : NSExperimentalLane
  BPhysicalR440 BPhysicalProducers BIntegratedControl BContinuation : NSExperimentalLane
  CDReleasedReconstruction : NSExperimentalLane

canonicalLeaf : NSExperimentalLane → Clay.CanonicalClayLiveObligation
canonicalLeaf APhysicalPopulation = Clay.a1PhysicalPopulation
canonicalLeaf APhysicalMajorant = Clay.a2MajorantDomination
canonicalLeaf AContinuation = Clay.a3Continuation
canonicalLeaf BPhysicalR440 = Clay.b4PhysicalR440Payment
canonicalLeaf BPhysicalProducers = Clay.b123PhysicalProducers
canonicalLeaf BIntegratedControl = Clay.b7IntegratedControl
canonicalLeaf BContinuation = Clay.bContinuationInputs
canonicalLeaf CDReleasedReconstruction = Clay.cdReleasedReconstruction

record NSExperimentalReceipt : Set where
  constructor nsExperimentalReceipt
  field
    lane : NSExperimentalLane
    sourceObject : String
    exactObservable : String
    hypothesis : String
    observedResult : String
    rejectedOrRetained : String
    stillUnpaid : String

open NSExperimentalReceipt public

-- Historical matched N32/N48/N64 coherence experiment: local self-advection
-- depletion fails held-out; this is a *falsifier*, not a proof of B7.
historicalNonvacuousFalsifier : NSExperimentalReceipt
historicalNonvacuousFalsifier = nsExperimentalReceipt
  BIntegratedControl
  "docs/ns_exact_galerkin_coherence_baseline_results.md"
  "held-out N64 nonvacuous depletion margin at declared kappa"
  "local depletion is negative self-advective smooth alignment derivative"
  "reported held-out margins -0.01,-0.05,-0.10,-0.25"
  "reject this local depletion currency for the tested triad and parameters"
  "actual physical integrated Q4/E or signed Q5 route plus cutoff-uniform estimates"

-- Bidi already proves measured-fibre refinement; it never manufactures
-- an exact identification from one approximate numerical contact.
numericalEvidenceRefines :
  {Hidden Measurement : Set}
  (prior : Bidi.ResidualFibre Hidden)
  (measurement : Hidden → Measurement)
  (observed : Measurement) →
  Bidi.FibreRefines (Bidi.MeasuredFibre prior measurement observed) prior
numericalEvidenceRefines = Bidi.measurementAlwaysRefinesPrior

approximateCannotBecomeExact :
  Bidi.approximatelyConstrainedGrade ≡ Bidi.exactlyIdentifiedGrade → ⊥
approximateCannotBecomeExact = Bidi.approximateNotExact

existingSelectionCanChange :
  Portfolio.selected Portfolio.initialSelection ≡
  Portfolio.selected Portfolio.laterSelection → ⊥
existingSelectionCanChange = Portfolio.selectionChangesAfterResidualUpdate

-- The canonical residual explicitly keeps all historical unresolved
-- packages and Clay promotion blocked after any such numerical experiment.
canonicalUnresolved : NS.unresolvedPackagesDischarged ≡ false
canonicalUnresolved = NS.unresolvedPackagesDischargedIsFalse

canonicalNoClayPromotion : NS.clayNavierStokesPromoted ≡ false
canonicalNoClayPromotion = NS.clayNavierStokesPromotedIsFalse

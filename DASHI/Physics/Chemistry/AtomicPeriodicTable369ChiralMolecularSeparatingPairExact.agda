module DASHI.Physics.Chemistry.AtomicPeriodicTable369ChiralMolecularSeparatingPairExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)

------------------------------------------------------------------------
-- FINITE CHIRAL SEPARATING-PAIR FIXTURE
--
-- Same coarse molecular chart, distinct retained chirality residual, distinct
-- chirality-sensitive readout.  This is a proof-shape fixture for the molecular
-- bridge; it is not a claim about a particular experimental molecule.
------------------------------------------------------------------------

data CoarseMolecularChart : Set where
  sameCompositionConnectivityCharge : CoarseMolecularChart

data ChiralRichState : Set where
  leftHandedState : ChiralRichState
  rightHandedState : ChiralRichState

data ChiralityResidual : Set where
  leftResidual : ChiralityResidual
  rightResidual : ChiralityResidual

data ChiralReadout : Set where
  leftReadout : ChiralReadout
  rightReadout : ChiralReadout

coarseChart : ChiralRichState → CoarseMolecularChart
coarseChart leftHandedState = sameCompositionConnectivityCharge
coarseChart rightHandedState = sameCompositionConnectivityCharge

chiralityResidual : ChiralRichState → ChiralityResidual
chiralityResidual leftHandedState = leftResidual
chiralityResidual rightHandedState = rightResidual

chiralitySensitiveObservable : ChiralRichState → ChiralReadout
chiralitySensitiveObservable leftHandedState = leftReadout
chiralitySensitiveObservable rightHandedState = rightReadout

sameCoarsePair :
  coarseChart leftHandedState ≡ coarseChart rightHandedState
sameCoarsePair = refl

residualsDiffer :
  chiralityResidual leftHandedState ≡ chiralityResidual rightHandedState → ⊥
residualsDiffer ()

readoutsDiffer :
  chiralitySensitiveObservable leftHandedState
  ≡ chiralitySensitiveObservable rightHandedState → ⊥
readoutsDiffer ()

record FactorsThroughCoarse : Set where
  constructor factorsThroughCoarse
  field
    factor : CoarseMolecularChart → ChiralReadout
    factorLaw :
      (x : ChiralRichState) →
      chiralitySensitiveObservable x ≡ factor (coarseChart x)

open FactorsThroughCoarse public

chiralityObservableDoesNotFactorThroughCoarse :
  FactorsThroughCoarse → ⊥
chiralityObservableDoesNotFactorThroughCoarse F =
  readoutsDiffer
    (trans
      (factorLaw F leftHandedState)
      (sym (factorLaw F rightHandedState)))

record ChiralSeparatingPairBoundary : Set where
  constructor chiralSeparatingPairBoundary
  field
    sameCoarseChart : Bool
    sameCoarseChartIsTrue : sameCoarseChart ≡ true

    chiralityResidualSeparates : Bool
    chiralityResidualSeparatesIsTrue : chiralityResidualSeparates ≡ true

    chiralitySensitiveObservableFactorsThroughCoarseChart : Bool
    chiralitySensitiveObservableFactorsThroughCoarseChartIsFalse :
      chiralitySensitiveObservableFactorsThroughCoarseChart ≡ false

    finiteFixtureProvesUniversalStereochemicalPhysics : Bool
    finiteFixtureProvesUniversalStereochemicalPhysicsIsFalse :
      finiteFixtureProvesUniversalStereochemicalPhysics ≡ false

canonicalChiralSeparatingPairBoundary : ChiralSeparatingPairBoundary
canonicalChiralSeparatingPairBoundary =
  chiralSeparatingPairBoundary
    true refl
    true refl
    false refl
    false refl

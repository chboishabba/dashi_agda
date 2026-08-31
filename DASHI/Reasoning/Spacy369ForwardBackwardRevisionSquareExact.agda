module DASHI.Reasoning.Spacy369ForwardBackwardRevisionSquareExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Reasoning.Spacy369TwoDirectionArchitectureBidiExact as Architecture

------------------------------------------------------------------------
-- FORWARD/BACKWARD REVISION SQUARE WITH RETAINED ORDER RESIDUE.
--
-- This is an architecture fixture, not a claim that the materialised SensibLaw
-- parser evidence actually changed.  A schematic forward-version correction and
-- a backward consumer-demand revision can reach the same coarse joint endpoint
-- in either order while retaining different histories.
------------------------------------------------------------------------

data ForwardVersion : Set where
  originalForward revisedForward : ForwardVersion

data BackwardDemand : Set where
  operationalDemand enlargedDemand : BackwardDemand

record RevisionCorner : Set where
  constructor revisionCorner
  field
    forwardVersion : ForwardVersion
    backwardDemand : BackwardDemand

open RevisionCorner public

q00 q10 q01 q11 : RevisionCorner
q00 = revisionCorner originalForward operationalDemand
q10 = revisionCorner revisedForward operationalDemand
q01 = revisionCorner originalForward enlargedDemand
q11 = revisionCorner revisedForward enlargedDemand

data SquareStep : RevisionCorner → RevisionCorner → Set where
  forwardAtOperational : SquareStep q00 q10
  backwardAfterForward : SquareStep q10 q11
  backwardAtOriginal : SquareStep q00 q01
  forwardAfterBackward : SquareStep q01 q11

data SquarePath : RevisionCorner → RevisionCorner → Set where
  pathRefl : (corner : RevisionCorner) → SquarePath corner corner
  pathStep :
    ∀ {a b c} →
    SquareStep a b →
    SquarePath b c →
    SquarePath a c

forwardThenBackward : SquarePath q00 q11
forwardThenBackward =
  pathStep forwardAtOperational
    (pathStep backwardAfterForward (pathRefl q11))

backwardThenForward : SquarePath q00 q11
backwardThenForward =
  pathStep backwardAtOriginal
    (pathStep forwardAfterBackward (pathRefl q11))

------------------------------------------------------------------------
-- Coarse endpoint commutation and fine history non-descent.
------------------------------------------------------------------------

data RevisionHistory : Set where
  historyForwardThenBackward historyBackwardThenForward : RevisionHistory

data RevisionOrderResidue : Set where
  forwardThenBackwardResidue backwardThenForwardResidue : RevisionOrderResidue

terminalObserver : RevisionHistory → RevisionCorner
terminalObserver historyForwardThenBackward = q11
terminalObserver historyBackwardThenForward = q11

orderResidue : RevisionHistory → RevisionOrderResidue
orderResidue historyForwardThenBackward = forwardThenBackwardResidue
orderResidue historyBackwardThenForward = backwardThenForwardResidue

sameTerminalEndpoint :
  terminalObserver historyForwardThenBackward
  ≡ terminalObserver historyBackwardThenForward
sameTerminalEndpoint = refl

orderResiduesDiffer :
  orderResidue historyForwardThenBackward
  ≡ orderResidue historyBackwardThenForward → ⊥
orderResiduesDiffer ()

terminalEndpointCannotRecoverRevisionOrder :
  INF.FactorsThrough terminalObserver orderResidue → ⊥
terminalEndpointCannotRecoverRevisionOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      historyForwardThenBackward
      historyBackwardThenForward
      sameTerminalEndpoint
      orderResiduesDiffer)

------------------------------------------------------------------------
-- The prior two-direction owner remains the authority for one-sided revision
-- discipline.  This square only adds the order-sensitive composition fixture.
------------------------------------------------------------------------

architectureBoundary : Architecture.Spacy369TwoDirectionArchitectureBidiBoundary
architectureBoundary = Architecture.canonicalSpacy369TwoDirectionArchitectureBidiBoundary

record Spacy369ForwardBackwardRevisionSquareBoundary : Set where
  constructor spacy369ForwardBackwardRevisionSquareBoundary
  field
    forwardAndBackwardUpdatesMayShareFinalJointEndpoint : Bool
    forwardAndBackwardUpdatesMayShareFinalJointEndpointIsTrue :
      forwardAndBackwardUpdatesMayShareFinalJointEndpoint ≡ true
    finalJointEndpointDeterminesRevisionOrder : Bool
    finalJointEndpointDeterminesRevisionOrderIsFalse :
      finalJointEndpointDeterminesRevisionOrder ≡ false
    forwardRevisionEqualsBackwardConsumerRevision : Bool
    forwardRevisionEqualsBackwardConsumerRevisionIsFalse :
      forwardRevisionEqualsBackwardConsumerRevision ≡ false
    revisionOrderResidueIsGaugeCurvature : Bool
    revisionOrderResidueIsGaugeCurvatureIsFalse :
      revisionOrderResidueIsGaugeCurvature ≡ false
    schematicForwardVersionMeansMaterialisedParserActuallyChanged : Bool
    schematicForwardVersionMeansMaterialisedParserActuallyChangedIsFalse :
      schematicForwardVersionMeansMaterialisedParserActuallyChanged ≡ false
    sameEndpointMeansSameSelectiveReopeningHistory : Bool
    sameEndpointMeansSameSelectiveReopeningHistoryIsFalse :
      sameEndpointMeansSameSelectiveReopeningHistory ≡ false

canonicalSpacy369ForwardBackwardRevisionSquareBoundary :
  Spacy369ForwardBackwardRevisionSquareBoundary
canonicalSpacy369ForwardBackwardRevisionSquareBoundary =
  spacy369ForwardBackwardRevisionSquareBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

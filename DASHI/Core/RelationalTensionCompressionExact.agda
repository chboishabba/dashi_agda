module DASHI.Core.RelationalTensionCompressionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- RELATIONAL TENSION / COARSE PROJECTION
--
-- This owner makes one narrow mathematical point: a cheap binary consumer may
-- identify rich states that differ on an unresolved/action-relevant residual.
-- Carrying that residual is represented as a larger finite information carrier.
-- No claim is made here about human metabolic energy, autism, or any universal
-- cognitive mechanism; empirical consumers must supply those bridges.
------------------------------------------------------------------------

data RichEpistemicState : Set where
  establishedTrue : RichEpistemicState
  establishedFalse : RichEpistemicState
  unresolvedWithResidual : RichEpistemicState

coarseBinary : RichEpistemicState → Bool
coarseBinary establishedTrue = true
coarseBinary establishedFalse = false
coarseBinary unresolvedWithResidual = false

data ResolutionPolicy : Set where
  actAsTrue actAsFalse holdAndInvestigate : ResolutionPolicy

resolutionPolicy : RichEpistemicState → ResolutionPolicy
resolutionPolicy establishedTrue = actAsTrue
resolutionPolicy establishedFalse = actAsFalse
resolutionPolicy unresolvedWithResidual = holdAndInvestigate

falseAndUnresolvedShareBinaryProjection :
  coarseBinary establishedFalse ≡ coarseBinary unresolvedWithResidual
falseAndUnresolvedShareBinaryProjection = refl

falseAndUnresolvedRequireDifferentPolicy :
  resolutionPolicy establishedFalse ≡
  resolutionPolicy unresolvedWithResidual → ⊥
falseAndUnresolvedRequireDifferentPolicy ()

binaryProjectionCannotRecoverResolutionPolicy :
  NonFactor.FactorsThrough coarseBinary resolutionPolicy → ⊥
binaryProjectionCannotRecoverResolutionPolicy =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      establishedFalse
      unresolvedWithResidual
      falseAndUnresolvedShareBinaryProjection
      falseAndUnresolvedRequireDifferentPolicy)

------------------------------------------------------------------------
-- Context-local false is not global false.
------------------------------------------------------------------------

data Context : Set where
  contextHere contextElsewhere : Context

data PropositionSubject : Set where
  oneSubject : PropositionSubject

contextualTruth : Context → PropositionSubject → Bool
contextualTruth contextHere oneSubject = false
contextualTruth contextElsewhere oneSubject = true

falseHere : contextualTruth contextHere oneSubject ≡ false
falseHere = refl

trueElsewhere : contextualTruth contextElsewhere oneSubject ≡ true
trueElsewhere = refl

data FalseEverywhereWitness : Set where
  falseEverywhere :
    ((context : Context) → contextualTruth context oneSubject ≡ false) →
    FalseEverywhereWitness

falseHereDoesNotEstablishFalseEverywhere : FalseEverywhereWitness → ⊥
falseHereDoesNotEstablishFalseEverywhere (falseEverywhere proof) with proof contextElsewhere
... | ()

------------------------------------------------------------------------
-- Finite representational-burden proxy.
--
-- `retainedCoordinates` is a structural bookkeeping count only.  It can be
-- consumed by later complexity/resource models, but it is not itself a neural
-- energy quantity or empirical effect size.
------------------------------------------------------------------------

data RepresentationMode : Set where
  binaryCompressed relationalResidualPreserving : RepresentationMode

retainedCoordinates : RepresentationMode → Nat
retainedCoordinates binaryCompressed = 1
retainedCoordinates relationalResidualPreserving = 3

data CommitmentMode : Set where
  earlyBinaryCommit carryUnresolvedRelation : CommitmentMode

commitmentFor : RepresentationMode → CommitmentMode
commitmentFor binaryCompressed = earlyBinaryCommit
commitmentFor relationalResidualPreserving = carryUnresolvedRelation

record RelationalTensionCompressionBoundary : Set where
  constructor relationalTensionCompressionBoundary
  field
    unresolvedIsEstablishedFalse : Bool
    unresolvedIsEstablishedFalseIsFalse :
      unresolvedIsEstablishedFalse ≡ false

    localFalseIsGlobalFalse : Bool
    localFalseIsGlobalFalseIsFalse :
      localFalseIsGlobalFalse ≡ false

    binaryProjectionPreservesEveryActionRelevantResidual : Bool
    binaryProjectionPreservesEveryActionRelevantResidualIsFalse :
      binaryProjectionPreservesEveryActionRelevantResidual ≡ false

    retainedCoordinateCountIsMetabolicEnergy : Bool
    retainedCoordinateCountIsMetabolicEnergyIsFalse :
      retainedCoordinateCountIsMetabolicEnergy ≡ false

    higherRepresentationalBurdenProvesAutismMechanism : Bool
    higherRepresentationalBurdenProvesAutismMechanismIsFalse :
      higherRepresentationalBurdenProvesAutismMechanism ≡ false

    tensionReading : String

canonicalRelationalTensionCompressionBoundary :
  RelationalTensionCompressionBoundary
canonicalRelationalTensionCompressionBoundary =
  relationalTensionCompressionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    "Holding tension is represented only as retaining an unresolved relational residual instead of prematurely collapsing it into a binary consumer; the resulting bookkeeping burden is structural, not an empirical neural-energy theorem."

module DASHI.Cognition.PNF.SemanticSamplingLookupGeometry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)

import DASHI.Foundations.StratifiedResolutionTowerExact as Resolution
import DASHI.Cognition.PNF.DirectDemandLookup as Direct
import DASHI.Cognition.PNF.BoundedExecutionCarrier as Bounded
open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- Exact semantic-sampling seam.
--
-- Nyquist/Shannon motivates the question "is this resolution sufficient?",
-- but the theorem formalised here is only an exact commuting-query condition:
-- a fine query is answer-equivalent to a coarse query after projection.  No
-- classical bandlimit, Fourier spectrum or sampling theorem is silently
-- imported into semantic data.
------------------------------------------------------------------------

record QuerySufficiency
    (tower : Resolution.ResolutionTower)
    (r : Nat)
    (Answer : Set) : Set₁ where
  constructor querySufficiency
  field
    fineQuery : Resolution.Carrier tower (suc r) → Answer
    coarseQuery : Resolution.Carrier tower r → Answer
    answerCommutesWithProjection :
      (fine : Resolution.Carrier tower (suc r)) →
      fineQuery fine ≡ coarseQuery (Resolution.project tower fine)

open QuerySufficiency public

record AliasingWitness
    (tower : Resolution.ResolutionTower)
    (r : Nat) : Set where
  constructor aliasingWitness
  field
    leftFine rightFine : Resolution.Carrier tower (suc r)
    sameCoarseShadow :
      Resolution.project tower leftFine ≡ Resolution.project tower rightFine
    fineStatesDistinct : leftFine ≡ rightFine → ⊥

open AliasingWitness public

------------------------------------------------------------------------
-- Exact and geometric addresses are separate coordinates.  The exact key is
-- suitable for equality lookup; the structured address supplies a neighbourhood
-- geometry such as a prefix/stratum tower.  Equality of one coordinate does not
-- automatically identify the other.
------------------------------------------------------------------------

record DualLookupAddress (GeometricAddress : Set) : Set where
  constructor dualLookupAddress
  field
    exactKey : NumericLookupKey
    geometricAddress : GeometricAddress

open DualLookupAddress public

data ProbeGeometry : Set where
  storageProbe : Direct.ProbeStrategy → ProbeGeometry
  neighbourhoodProposal : ProbeGeometry

-- Reuse DirectDemandLookup's contracts literally.
ExpectedConstantEqualityProbeContract : Set
ExpectedConstantEqualityProbeContract = Direct.ExpectedConstantProbeContract

OrderedTreeProbeContract : Set
OrderedTreeProbeContract = Direct.ProbeContract

PrefixProbeContract : Set
PrefixProbeContract = Direct.PrefixProbeContract

------------------------------------------------------------------------
-- Approximate/continuous neighbourhood geometry is proposal-only.
------------------------------------------------------------------------

record NeighbourhoodProposalReceipt (Candidate : Set) : Set where
  constructor neighbourhoodProposalReceipt
  field
    proposalFrontier : Bounded.BoundedExecutionCarrier Candidate
    approximateEvaluationUsed : Bool
    proposalRequiresExactDownstreamCheck : Bool
    proposalRequiresExactDownstreamCheckIsTrue :
      proposalRequiresExactDownstreamCheck ≡ true

open NeighbourhoodProposalReceipt public

data NeighbourhoodProposalIdentityPermission : Set where

neighbourhoodProposalCannotAdmitIdentity :
  NeighbourhoodProposalIdentityPermission → ⊥
neighbourhoodProposalCannotAdmitIdentity ()

------------------------------------------------------------------------
-- Claim boundaries: query sufficiency, compression optimality, prefix geometry
-- and p-adic algebra are separate obligations.
------------------------------------------------------------------------

record SemanticSamplingLookupBoundary : Set where
  constructor semanticSamplingLookupBoundary
  field
    queryCommutationIsClassicalNyquistTheorem : Bool
    queryCommutationIsClassicalNyquistTheoremIsFalse :
      queryCommutationIsClassicalNyquistTheorem ≡ false
    sufficientResolutionAutomaticallyMinimisesDescriptionLength : Bool
    sufficientResolutionAutomaticallyMinimisesDescriptionLengthIsFalse :
      sufficientResolutionAutomaticallyMinimisesDescriptionLength ≡ false
    prefixTowerAutomaticallyHasPAdicRingStructure : Bool
    prefixTowerAutomaticallyHasPAdicRingStructureIsFalse :
      prefixTowerAutomaticallyHasPAdicRingStructure ≡ false
    approximateNeighbourhoodMayPromoteIdentity : Bool
    approximateNeighbourhoodMayPromoteIdentityIsFalse :
      approximateNeighbourhoodMayPromoteIdentity ≡ false
    exactAndGeometricAddressesAreDistinctCoordinates : Bool
    exactAndGeometricAddressesAreDistinctCoordinatesIsTrue :
      exactAndGeometricAddressesAreDistinctCoordinates ≡ true

open SemanticSamplingLookupBoundary public

canonicalSemanticSamplingLookupBoundary : SemanticSamplingLookupBoundary
canonicalSemanticSamplingLookupBoundary =
  semanticSamplingLookupBoundary
    false refl
    false refl
    false refl
    false refl
    true refl

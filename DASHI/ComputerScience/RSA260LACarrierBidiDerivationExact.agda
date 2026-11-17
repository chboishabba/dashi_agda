module DASHI.ComputerScience.RSA260LACarrierBidiDerivationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.BidirectionalRelationRepresentationBridgeExact as Bidi
import DASHI.ComputerScience.RSA260PublicLAExecutionEnvelopeReconstructionExact as Envelope
import DASHI.ComputerScience.RSA260GNFSRunParameterArtifactSnowballExact as Params
import DASHI.ComputerScience.RSA260ProductionArtifactSubstituteAdmissionExact as Substitute

------------------------------------------------------------------------
-- RSA-260 LINEAR-ALGEBRA CARRIER: BIDIRECTIONAL DERIVATION CUT
--
-- Forward direction:
--   primary run report -> matrix/execution envelope -> expected LA artefacts.
--
-- Backward direction:
--   published Block-Wiedemann / lingen / mksol / gather outcomes -> minimum
--   constraints any candidate production LA carrier must satisfy.
--
-- Their intersection derives a CONSTRAINT FIBRE of admissible sparse GF(2)
-- carriers.  It does not derive a unique same-object matrix or its bytes.
------------------------------------------------------------------------

data LAScalarField : Set where
  gf2 : LAScalarField

data NullspaceOrientation : Set where
  leftNullspace : NullspaceOrientation

record ForwardCarrierEnvelope : Set where
  constructor forward-carrier-envelope
  field
    field : LAScalarField
    rows : Nat
    columns : Nat
    nonzeros : Nat
    rowExcess : Nat
    densityFloor : Nat
    densityRemainder : Nat
    densityDenominator : Nat
open ForwardCarrierEnvelope public

currentForwardCarrierEnvelope : ForwardCarrierEnvelope
currentForwardCarrierEnvelope = forward-carrier-envelope
  gf2
  656182601
  656182189
  98431741898
  412
  150
  4351748
  656182601

record BackwardLAConsumerRequirements : Set where
  constructor backward-la-consumer-requirements
  field
    nullspaceOrientation : NullspaceOrientation
    blockM : Nat
    blockN : Nat
    krylovSequenceCount : Nat
    sequenceWidth : Nat
    simdWidth : Nat
    finalIteration : Nat
    checkpointStride : Nat
    retainedCheckpointStride : Nat
    generatorLength : Nat
    mksolPartialSolutionFiles : Nat
    gatheredKernelVectors : Nat
    nonzeroDependencies : Nat
    firstFactorDependency : Nat
open BackwardLAConsumerRequirements public

currentBackwardLAConsumerRequirements : BackwardLAConsumerRequirements
currentBackwardLAConsumerRequirements = backward-la-consumer-requirements
  leftNullspace
  512 512
  2 256 256
  2564096
  8192 32768
  1281607
  40 64 26 12

------------------------------------------------------------------------
-- The derived carrier is a fibre/schema, not a unique matrix.
------------------------------------------------------------------------

record BidiDerivedLACarrierFibre : Set where
  constructor bidi-derived-la-carrier-fibre
  field
    forwardEnvelope : ForwardCarrierEnvelope
    backwardRequirements : BackwardLAConsumerRequirements

    checkpointIntervalsPerSequence : Nat
    completeRetainedStrideMultiples : Nat
    retainedTerminalRemainder : Nat

    exactNonzeroPositionsDerived : Bool
    exactRowOrderingDerived : Bool
    exactColumnOrderingDerived : Bool
    exactPreparedBWCEncodingDerived : Bool
    exactProjectionVectorsOrSeedDerived : Bool
    exactCheckpointContentsDerived : Bool
    exactMatrixBytesDerived : Bool
    exactMatrixDigestDerived : Bool
    uniqueMatrixDerived : Bool

    constraintFibreDerived : Bool
    sameObjectP0Paid : Bool
open BidiDerivedLACarrierFibre public

currentBidiDerivedLACarrierFibre : BidiDerivedLACarrierFibre
currentBidiDerivedLACarrierFibre = bidi-derived-la-carrier-fibre
  currentForwardCarrierEnvelope
  currentBackwardLAConsumerRequirements
  313
  78
  8192
  false false false false false false false false false
  true false

------------------------------------------------------------------------
-- Existing owners remain the authoritative source coordinates.
------------------------------------------------------------------------

publicEnvelope : Envelope.PublicLAExecutionEnvelope
publicEnvelope = Envelope.currentPublicLAExecutionEnvelope

runParameters : Params.RunParameterReceipt
runParameters = Params.rsa260LinearAlgebraParameters

substituteBoundary : Substitute.SubstituteAdmissionBoundary
substituteBoundary = Substitute.currentSubstituteAdmissionBoundary

bidiRepresentationBoundary : Bidi.BidirectionalRelationBridgeBoundary
bidiRepresentationBoundary = Bidi.canonicalBidirectionalRelationBridgeBoundary

------------------------------------------------------------------------
-- Executed arithmetic/constraint oracle.
------------------------------------------------------------------------

record BidiCarrierRuntimeSource : Set where
  constructor bidi-carrier-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    compiler : String
    exactGitBlobExecuted : Bool
open BidiCarrierRuntimeSource public

currentBidiCarrierRuntimeSource : BidiCarrierRuntimeSource
currentBidiCarrierRuntimeSource = bidi-carrier-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_la_carrier_constraint_oracle.c"
  "bfb8a3026739229ffe6bca390c1e893ce916e921"
  "cfc78a1ba98a434166430ec040d5c3b1a4138ad8"
  "gcc -std=c11 -O2 -Wall -Wextra -pedantic"
  true

record BidiCarrierDerivationBoundary : Set where
  constructor bidi-carrier-derivation-boundary
  field
    forwardPrimaryEnvelopeConstrainsCarrier : Bool
    backwardDownstreamConsumerConstrainsCarrier : Bool
    bothDirectionsUseSameRunIdentity : Bool
    intersectionDerivesConstraintFibre : Bool
    constraintFibreIsSingleton : Bool
    bidiDerivationImpliesCarrierIsomorphism : Bool
    gatheredVectorCountImpliesKernelNullity64 : Bool
    dependencyCountImpliesKernelDimension26 : Bool
    exactBytesStillRequiredForSameObjectP0 : Bool
open BidiCarrierDerivationBoundary public

canonicalBidiCarrierDerivationBoundary : BidiCarrierDerivationBoundary
canonicalBidiCarrierDerivationBoundary = bidi-carrier-derivation-boundary
  true true true true false false false false true

------------------------------------------------------------------------
-- What the bidi cut buys us operationally.
------------------------------------------------------------------------

record BidiP0AdmissionReading : Set where
  constructor bidi-p0-admission-reading
  field
    candidateMatrixMustMatchGF2Carrier : Bool
    candidateMatrixMustMatchShapeAndNNZ : Bool
    candidateRunMustMatchLeftNullspaceGeometry : Bool
    candidateRunMustMatch512By512BlockGeometry : Bool
    candidateRunMustMatchTwoWidth256Sequences : Bool
    candidateRunMustMatchCheckpointLattice : Bool
    candidateDownstreamArtifactsMustMatchPublishedCounts : Bool
    satisfyingAllPublicConstraintsAloneProvesSameObject : Bool
open BidiP0AdmissionReading public

canonicalBidiP0AdmissionReading : BidiP0AdmissionReading
canonicalBidiP0AdmissionReading = bidi-p0-admission-reading
  true true true true true true true false

------------------------------------------------------------------------
-- Residuals: these are exactly the fibres that prevent the public envelope
-- from collapsing to a unique production matrix.
------------------------------------------------------------------------

data BidiLACarrierResidual : Set where
  acquireExactFilteredOrPreparedMatrixBytes : BidiLACarrierResidual
  bindExactMatrixDigest : BidiLACarrierResidual
  recoverExactNonzeroPlacement : BidiLACarrierResidual
  recoverExactRowColumnOrdering : BidiLACarrierResidual
  recoverPreparedBWCEncodingAndPadding : BidiLACarrierResidual
  recoverProjectionVectorsInitialStateOrSeed : BidiLACarrierResidual
  acquireCheckpointContents : BidiLACarrierResidual
  closeSameObjectRunIdentity : BidiLACarrierResidual

firstConclusionPayingBidiCarrierResidual : BidiLACarrierResidual
firstConclusionPayingBidiCarrierResidual = acquireExactFilteredOrPreparedMatrixBytes

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data EnvelopeDeterminesUniqueMatrix : Set where
data OutputCountsDetermineMatrixBytes : Set where
data Gather64ImpliesNullity64 : Set where
data Dependencies26ImpliesNullity26 : Set where
data BidiConstraintFibreImpliesSameObjectP0 : Set where

envelopeDoesNotDetermineUniqueMatrix : EnvelopeDeterminesUniqueMatrix → ⊥
envelopeDoesNotDetermineUniqueMatrix ()

outputCountsDoNotDetermineMatrixBytes : OutputCountsDetermineMatrixBytes → ⊥
outputCountsDoNotDetermineMatrixBytes ()

gatherCountDoesNotDetermineNullity : Gather64ImpliesNullity64 → ⊥
gatherCountDoesNotDetermineNullity ()

dependencyCountDoesNotDetermineNullity : Dependencies26ImpliesNullity26 → ⊥
dependencyCountDoesNotDetermineNullity ()

bidiFibreDoesNotPaySameObjectBytes : BidiConstraintFibreImpliesSameObjectP0 → ⊥
bidiFibreDoesNotPaySameObjectBytes ()

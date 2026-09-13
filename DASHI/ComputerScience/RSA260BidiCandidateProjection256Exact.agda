module DASHI.ComputerScience.RSA260BidiCandidateProjection256Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiCandidateBWCShadowExact as Shadow
import DASHI.ComputerScience.RSA260BidiCandidateGeneratorKernelExact as CandidateFullLA
import DASHI.ComputerScience.RSA260GNFSRunParameterArtifactSnowballExact as RunArtifact

------------------------------------------------------------------------
-- WIDTH-256 TRANSPORT/PROJECTION EXPERIMENT ON THE SAME BIDI CANDIDATE
--
-- Two independent width-256 block sequences are transported through the
-- candidate-derived B = A A^T operator.  This matches the published total
-- two-by-256 block-column geometry while remaining an experiment on the
-- candidate shadow, not the historical production projection state.
------------------------------------------------------------------------

shadowBoundary : Shadow.PreparedShadowConsumerBoundary
shadowBoundary = Shadow.canonicalPreparedShadowConsumerBoundary

candidateFullLABoundary : CandidateFullLA.CandidateFullLAConsumerBoundary
candidateFullLABoundary = CandidateFullLA.canonicalCandidateFullLAConsumerBoundary

runArtifactBoundary : RunArtifact.RSA260RunParameterArtifactBoundary
runArtifactBoundary = RunArtifact.canonicalRSA260RunParameterArtifactBoundary

record Projection256RuntimeSource : Set where
  constructor projection256-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    compiler : String
    exactGitBlobExecuted : Bool
open Projection256RuntimeSource public

currentProjection256RuntimeSource : Projection256RuntimeSource
currentProjection256RuntimeSource = projection256-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_candidate_projection256_oracle.c"
  "0ed6c1aca645b64bac78c6ace5e4fffc7b425197"
  "2cf7f922202925df3f52a23ddd6fd51808a823f2"
  "gcc -std=c11 -O2 -Wall -Wextra -pedantic"
  true

record Projection256ExecutionReceipt : Set where
  constructor projection256-execution-receipt
  field
    sequenceCount : Nat
    widthPerSequence : Nat
    totalBlockColumns : Nat
    termsPerSequence : Nat
    vectorUpdatesChecked : Nat
    explicitAndFactorizedTransportAgree : Bool
    firstSequenceDigest : String
    secondSequenceDigest : String
    historicalProjectionStateIdentityPaid : Bool
    productionCheckpointCadenceReplayed : Bool
open Projection256ExecutionReceipt public

currentProjection256ExecutionReceipt : Projection256ExecutionReceipt
currentProjection256ExecutionReceipt = projection256-execution-receipt
  2 256 512 16 8192
  true
  "b5c4de3409d03b2c"
  "e9641c49f65689a4"
  false false

record Projection256ConsumerBoundary : Set where
  constructor projection256-consumer-boundary
  field
    candidateTwoSequenceGeometryPaid : Bool
    candidateWidth256TransportPaid : Bool
    candidateTotal512BlockColumnsPaid : Bool
    candidateExplicitFactorizedParityPaid : Bool
    candidateProjectionDigestsPaid : Bool
    candidateGeneratorAtWidth256Paid : Bool
    candidateKernelRecoveryAtWidth256Paid : Bool
    productionProjectionStatePaid : Bool
open Projection256ConsumerBoundary public

canonicalProjection256ConsumerBoundary : Projection256ConsumerBoundary
canonicalProjection256ConsumerBoundary = projection256-consumer-boundary
  true true true true true
  false false false

------------------------------------------------------------------------
-- Next experiment escalation.
------------------------------------------------------------------------

data Projection256Residual : Set where
  compareIndependentWidth256Seeds : Projection256Residual
  scaleGeneratorConsumerBeyondWidth8 : Projection256Residual
  compareAlternativePreparedAdaptersAtWidth256 : Projection256Residual
  validateWidth256CandidateAgainstProductionArtifact : Projection256Residual

firstProjection256Residual : Projection256Residual
firstProjection256Residual = compareIndependentWidth256Seeds

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data Width256ImpliesProductionProjection : Set where
data TwoBy256ImpliesProductionMNGeometry : Set where
data ProjectionParityImpliesProductionGenerator : Set where

width256DoesNotCreateProductionProjection : Width256ImpliesProductionProjection → ⊥
width256DoesNotCreateProductionProjection ()

twoBy256DoesNotCreateProductionMNGeometry : TwoBy256ImpliesProductionMNGeometry → ⊥
twoBy256DoesNotCreateProductionMNGeometry ()

projectionParityDoesNotCreateProductionGenerator : ProjectionParityImpliesProductionGenerator → ⊥
projectionParityDoesNotCreateProductionGenerator ()

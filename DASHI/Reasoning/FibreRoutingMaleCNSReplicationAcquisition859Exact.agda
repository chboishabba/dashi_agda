module DASHI.Reasoning.FibreRoutingMaleCNSReplicationAcquisition859Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.FibreRoutingMaleCNSMagnitudeAssignmentReplicationFrontierExact as Base

record ReplicationAcquisition859Receipt : Set where
  constructor replication-acquisition-859-receipt
  field
    repository : String
    branch : String
    accumulationArtifactPath : String
    accumulatedIdentityCsv : String
    depositedSelectedCount : Nat
    resolvedSelectedCount : Nat
    unresolvedSelectedCount : Nat
    searchedTrialCount : Nat
    a2r5ResolvedCount : Nat
    a1r9ResolvedCount : Nat
    a1r2ResolvedCount : Nat
    a2r1ResolvedCount : Nat
    allResolvedSelectedRowIdsUnique : Bool
    a2r5TrialIdentity : String
    a1r9TrialIdentity : String
    a1r2TrialIdentity : String
    a2r1TrialIdentity : String
    a1r2SourceRepository : String
    a1r2SourceRepositoryDOI : String
    a2r1SearchedZero : Bool
    a1r1ZenodoSourceGap : Bool
    a1r1PrincetonFallbackStillCandidate : Bool
    exactTraceIdentitySemantics : String
    interpretation : String

open ReplicationAcquisition859Receipt public

currentReplicationAcquisition859Receipt : ReplicationAcquisition859Receipt
currentReplicationAcquisition859Receipt = replication-acquisition-859-receipt
  "github.com/chboishabba/dashiBRAIN"
  "agent/malecns-real-benchmark-tranche"
  "data/gauthey_lbm/reconstruction_all_available/gauthey_lbm_identity_accumulation.json"
  "data/gauthey_lbm/reconstruction_all_available/gauthey_lbm_selected_identities_accumulated.csv"
  1620
  859
  761
  4
  374
  185
  300
  0
  true
  "04032024_6f_a2_r5"
  "04192024_6f_a1_r9"
  "04192024_6f_a1_r2"
  "04032024_6f_a2_r1"
  "Princeton Data Commons official Gauthey mirror"
  "10.34770/s5hx-1x75"
  true
  true
  true
  "exact trace equality to deposited selected row; not neuron identity and not atlas identity"
  "Four trials have now been searched for exact selected-row source identity. a2_r5 pays 374, a1_r9 pays 185, a1_r2 pays 300 from the Princeton Data Commons mirror, and a2_r1 is a searched-zero trial. The accumulated carrier therefore pays 859/1620 exact identities with 761 unresolved rows. This is acquisition progress only; no independent trial has yet been promoted merely from identity recovery."

currentResolvedSelectedCount859 : Nat
currentResolvedSelectedCount859 = 859

currentUnresolvedSelectedCount761 : Nat
currentUnresolvedSelectedCount761 = 761

currentSearchedTrialCount4 : Nat
currentSearchedTrialCount4 = 4

record ReplicationAcquisition859Boundary : Set where
  constructor replication-acquisition-859-boundary
  field
    historical559ReceiptRemainsValid : Bool
    accumulated859ReceiptPaid : Bool
    a2r1SearchedZeroRetained : Bool
    searchedZeroMeansNoBiologicalContribution : Bool
    a1r2PDCExactIdentityReceiptPaid : Bool
    pdcRepositoryUseImpliesJRC2018Ready : Bool
    exactIdentityRecoveryImpliesIndependentTrialReplication : Bool
    exactIdentityRecoveryImpliesCrossAnimalReplication : Bool
    unresolvedRowsRemainExplicit : Bool
    independentTrialReplicationStillUnpaid : Bool

open ReplicationAcquisition859Boundary public

canonicalReplicationAcquisition859Boundary : ReplicationAcquisition859Boundary
canonicalReplicationAcquisition859Boundary = replication-acquisition-859-boundary
  true
  true
  true
  false
  true
  false
  false
  false
  true
  true

baseReplicationAcquisitionBoundary : Base.ReplicationAcquisitionBoundary
baseReplicationAcquisitionBoundary = Base.canonicalReplicationAcquisitionBoundary

baseIndependentTrialReplicationStillUnpaid :
  Base.paid Base.independentTrialReplication ≡ false
baseIndependentTrialReplicationStillUnpaid = refl

pdcMirrorDOIMatchesBase : String
pdcMirrorDOIMatchesBase = Base.princetonAlternateRepositoryDOI

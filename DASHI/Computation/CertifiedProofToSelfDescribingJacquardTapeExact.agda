module DASHI.Computation.CertifiedProofToSelfDescribingJacquardTapeExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as RuleProof
import DASHI.Combinatorics.ProofCarryingTextileHyperfabricExact as Fabric
import DASHI.Computation.ProofCarryingJacquardMotifExact as Motif
import DASHI.Computation.SelfDescribingProofJacquardTapeExact as Tape

------------------------------------------------------------------------
-- The current structural motif backend is exactly two payload warp ends by
-- two picks.  These rows are the same visible rows already proved by
-- ProofCarryingJacquardMotifExact; the theorem below pins that identity.
------------------------------------------------------------------------

payload0 : Fabric.ProofMotif → Tape.BitVector 2
payload0 Fabric.premiseMotif = false Tape.b∷ false Tape.b∷ Tape.b[]
payload0 Fabric.branchMotif = false Tape.b∷ false Tape.b∷ Tape.b[]
payload0 Fabric.dischargeMotif = false Tape.b∷ true Tape.b∷ Tape.b[]
payload0 Fabric.rewriteMotif = false Tape.b∷ true Tape.b∷ Tape.b[]
payload0 Fabric.lemmaReferenceMotif = true Tape.b∷ false Tape.b∷ Tape.b[]
payload0 Fabric.conclusionMotif = true Tape.b∷ false Tape.b∷ Tape.b[]

payload1 : Fabric.ProofMotif → Tape.BitVector 2
payload1 Fabric.premiseMotif = false Tape.b∷ false Tape.b∷ Tape.b[]
payload1 Fabric.branchMotif = true Tape.b∷ true Tape.b∷ Tape.b[]
payload1 Fabric.dischargeMotif = false Tape.b∷ true Tape.b∷ Tape.b[]
payload1 Fabric.rewriteMotif = true Tape.b∷ false Tape.b∷ Tape.b[]
payload1 Fabric.lemmaReferenceMotif = false Tape.b∷ true Tape.b∷ Tape.b[]
payload1 Fabric.conclusionMotif = true Tape.b∷ false Tape.b∷ Tape.b[]

bits2Pair : Tape.BitVector 2 → Bool × Bool
bits2Pair (a Tape.b∷ b Tape.b∷ Tape.b[]) = a , b

payloadRowsAreExistingVisibleMotif :
  (motif : Fabric.ProofMotif) →
  Motif.motifVisiblePattern motif
  ≡ bits2Pair (payload0 motif) ∷ bits2Pair (payload1 motif) ∷ []
payloadRowsAreExistingVisibleMotif Fabric.premiseMotif = refl
payloadRowsAreExistingVisibleMotif Fabric.branchMotif = refl
payloadRowsAreExistingVisibleMotif Fabric.dischargeMotif = refl
payloadRowsAreExistingVisibleMotif Fabric.rewriteMotif = refl
payloadRowsAreExistingVisibleMotif Fabric.lemmaReferenceMotif = refl
payloadRowsAreExistingVisibleMotif Fabric.conclusionMotif = refl

zeroPayload : Tape.BitVector 2
zeroPayload = false Tape.b∷ false Tape.b∷ Tape.b[]

------------------------------------------------------------------------
-- Provenance coding remains source-controlled.  The textile compiler does not
-- hash or reinterpret dependency receipts itself; a caller supplies a stable
-- finite code for each exact rule occurrence.
------------------------------------------------------------------------

ProvenanceCode :
  {State Rule : Set} →
  (system : RuleProof.RuleApplicationSystem State Rule) → Set
ProvenanceCode system = Fabric.RuleOccurrence system → Nat

beginRow : Nat → Fabric.ProofMotif → Nat → Tape.ProofTapeRow 2
beginRow step motif provenance =
  Tape.canonicalRow
    Tape.motifBeginFrame step 0 false motif provenance zeroPayload

provenanceRow : Nat → Fabric.ProofMotif → Nat → Tape.ProofTapeRow 2
provenanceRow step motif provenance =
  Tape.canonicalRow
    Tape.provenanceFrame step 0 false motif provenance zeroPayload

continuation0Row : Nat → Fabric.ProofMotif → Nat → Tape.ProofTapeRow 2
continuation0Row step motif provenance =
  Tape.canonicalRow
    Tape.continuationFrame step 0 true motif provenance (payload0 motif)

continuation1Row : Nat → Fabric.ProofMotif → Nat → Tape.ProofTapeRow 2
continuation1Row step motif provenance =
  Tape.canonicalRow
    Tape.continuationFrame step 1 false motif provenance (payload1 motif)

endRow : Nat → Fabric.ProofMotif → Nat → Tape.ProofTapeRow 2
endRow step motif provenance =
  Tape.canonicalRow
    Tape.motifEndFrame step 0 false motif provenance zeroPayload

startRow : Tape.ProofTapeRow 2
startRow =
  Tape.canonicalRow
    Tape.startFrame 0 0 false Fabric.premiseMotif 0 zeroPayload

stopRow : Nat → Tape.ProofTapeRow 2
stopRow step =
  Tape.canonicalRow
    Tape.stopFrame step 0 false Fabric.conclusionMotif 0 zeroPayload

compileBodyFrom :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule}
  {assignment : Fabric.MotifAssignment Rule}
  (provenanceCode : ProvenanceCode system) →
  (step : Nat) →
  {state : State}
  {trace : RuleProof.CertifiedRuleTrace system state} →
  Fabric.CertifiedFabricTrace assignment trace →
  Tape.ProofTape 2
compileBodyFrom provenanceCode step Fabric.fabricDone =
  stopRow step ∷ []
compileBodyFrom {system = system} provenanceCode step
  (Fabric.fabricChoose {state = state} selected patch rest) =
  let
    occurrence = state , selected
    motif = Fabric.physicalMotif patch
    provenance = provenanceCode occurrence
  in
    beginRow step motif provenance
    ∷ provenanceRow step motif provenance
    ∷ continuation0Row step motif provenance
    ∷ continuation1Row step motif provenance
    ∷ endRow step motif provenance
    ∷ compileBodyFrom provenanceCode (suc step) rest

compileCertifiedFabricToProofTape :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule}
  {assignment : Fabric.MotifAssignment Rule}
  (provenanceCode : ProvenanceCode system) →
  {state : State}
  {trace : RuleProof.CertifiedRuleTrace system state} →
  Fabric.CertifiedFabricTrace assignment trace →
  Tape.ProofTape 2
compileCertifiedFabricToProofTape provenanceCode fabric =
  startRow ∷ compileBodyFrom provenanceCode 0 fabric

------------------------------------------------------------------------
-- Every row generated by this compiler is locally parity-valid by
-- construction.  The structural validator then checks ordering/IDs before a
-- machine backend is allowed to lower the tape to a loom-width raster.
------------------------------------------------------------------------

compiledStartRowValid : Tape.rowLocallyValid startRow ≡ true
compiledStartRowValid = refl

compiledContinuation0Valid :
  ∀ step motif provenance →
  Tape.rowLocallyValid (continuation0Row step motif provenance) ≡ true
compiledContinuation0Valid step motif provenance = refl

compiledContinuation1Valid :
  ∀ step motif provenance →
  Tape.rowLocallyValid (continuation1Row step motif provenance) ≡ true
compiledContinuation1Valid step motif provenance = refl

record CertifiedProofTapeCompilerBoundary : Set where
  constructor certified-proof-tape-compiler-boundary
  field
    sourceIsActualCertifiedFabricTrace : Bool
    exactRuleOccurrenceGetsProvenanceCode : Bool
    eachProofStepHasTypedFrameBoundary : Bool
    eachProofStepUsesTwoExistingMotifPicks : Bool
    generatedRowsCarryComputedParity : Bool
    outputFeedsPreWeaveTapeValidator : Bool
    visibleMotifRowsAreSameExistingRows : Bool

canonicalCertifiedProofTapeCompilerBoundary : CertifiedProofTapeCompilerBoundary
canonicalCertifiedProofTapeCompilerBoundary =
  certified-proof-tape-compiler-boundary
    true true true true true true true

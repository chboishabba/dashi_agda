module DASHI.Computation.SelfDescribingProofJacquardTapeExact where

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard
import DASHI.Combinatorics.ProofCarryingTextileHyperfabricExact as Fabric

------------------------------------------------------------------------
-- Literal fixed-width bits.  Unlike a LiftMask function, this carrier can be
-- scanned and parity-checked locally as physical/digital tape data.
------------------------------------------------------------------------

data BitVector : Nat → Set where
  [] : BitVector 0
  _∷_ : ∀ {n} → Bool → BitVector n → BitVector (suc n)

infixr 5 _∷_

lookupBit : ∀ {n} → BitVector n → Fin n → Bool
lookupBit (bit ∷ bits) zero = bit
lookupBit (bit ∷ bits) (suc i) = lookupBit bits i

bitsToLiftMask : ∀ {n} → BitVector n → Jacquard.LiftMask n
bitsToLiftMask bits i = lookupBit bits i

maskToBits : ∀ {n} → Jacquard.LiftMask n → BitVector n
maskToBits {0} mask = []
maskToBits {suc n} mask =
  mask zero ∷ maskToBits (λ i → mask (suc i))

xor : Bool → Bool → Bool
xor false b = b
xor true false = true
xor true true = false

boolEq : Bool → Bool → Bool
boolEq false false = true
boolEq true true = true
boolEq _ _ = false

parityBits : ∀ {n} → BitVector n → Bool
parityBits [] = false
parityBits (bit ∷ bits) = xor bit (parityBits bits)

------------------------------------------------------------------------
-- Self-describing proof tape rows.
--
-- Every row is still a literal lift vector and may therefore be lowered to a
-- real loom row.  Structural metadata is represented in reserved proof lanes,
-- not merely in an out-of-band comment.  The exact lane packing is delegated
-- to a machine/layout profile; this owner establishes the typed frame grammar
-- and local checkability before physical lowering.
------------------------------------------------------------------------

data FrameKind : Set where
  startFrame : FrameKind
  motifBeginFrame : FrameKind
  continuationFrame : FrameKind
  provenanceFrame : FrameKind
  motifEndFrame : FrameKind
  stopFrame : FrameKind

kindParity : FrameKind → Bool
kindParity startFrame = true
kindParity motifBeginFrame = false
kindParity continuationFrame = true
kindParity provenanceFrame = true
kindParity motifEndFrame = false
kindParity stopFrame = false

natParity : Nat → Bool
natParity 0 = false
natParity (suc n) = xor true (natParity n)

motifParity : Fabric.ProofMotif → Bool
motifParity Fabric.premiseMotif = false
motifParity Fabric.branchMotif = true
motifParity Fabric.dischargeMotif = true
motifParity Fabric.rewriteMotif = false
motifParity Fabric.lemmaReferenceMotif = true
motifParity Fabric.conclusionMotif = false

record ProofTapeRow (payloadWidth : Nat) : Set where
  constructor proof-tape-row
  field
    frameKind : FrameKind
    proofStepId : Nat
    continuationId : Nat
    motif : Fabric.ProofMotif
    provenanceId : Nat
    payload : BitVector payloadWidth
    parityBit : Bool

open ProofTapeRow public

computedParity : ∀ {n} → ProofTapeRow n → Bool
computedParity row =
  xor (kindParity (frameKind row))
    (xor (natParity (proofStepId row))
      (xor (natParity (continuationId row))
        (xor (motifParity (motif row))
          (xor (natParity (provenanceId row))
            (parityBits (payload row))))))

rowLocallyValid : ∀ {n} → ProofTapeRow n → Bool
rowLocallyValid row = boolEq (parityBit row) (computedParity row)

canonicalRow :
  ∀ {n} →
  FrameKind → Nat → Nat → Fabric.ProofMotif → Nat → BitVector n →
  ProofTapeRow n
canonicalRow kind step cont motif provenance payload =
  proof-tape-row
    kind step cont motif provenance payload
    (xor (kindParity kind)
      (xor (natParity step)
        (xor (natParity cont)
          (xor (motifParity motif)
            (xor (natParity provenance) (parityBits payload))))))

canonicalRowValid :
  ∀ {n} kind step cont motif provenance (payload : BitVector n) →
  rowLocallyValid (canonicalRow kind step cont motif provenance payload) ≡ true
canonicalRowValid kind step cont motif provenance payload = refl

ProofTape : Nat → Set
ProofTape n = List (ProofTapeRow n)

allRowsValid : ∀ {n} → ProofTape n → Bool
allRowsValid [] = true
allRowsValid (row ∷ rows) with rowLocallyValid row
... | false = false
... | true = allRowsValid rows

------------------------------------------------------------------------
-- Structural grammar: start -> motifs -> stop.
-- A motif carries begin, provenance, one or more continuation rows, and end.
------------------------------------------------------------------------

data TapePhase : Set where
  expectStart : TapePhase
  betweenMotifs : TapePhase
  expectProvenance : Nat → TapePhase
  expectContinuation : Nat → Nat → TapePhase
  expectMotifEnd : Nat → TapePhase
  finished : TapePhase

natEq : Nat → Nat → Bool
natEq 0 0 = true
natEq 0 (suc n) = false
natEq (suc n) 0 = false
natEq (suc n) (suc m) = natEq n m

data PhaseResult : Set where
  rejected : PhaseResult
  accepted : TapePhase → PhaseResult

advancePhase : ∀ {n} → TapePhase → ProofTapeRow n → PhaseResult
advancePhase expectStart row with frameKind row
... | startFrame = accepted betweenMotifs
... | _ = rejected
advancePhase betweenMotifs row with frameKind row
... | motifBeginFrame = accepted (expectProvenance (proofStepId row))
... | stopFrame = accepted finished
... | _ = rejected
advancePhase (expectProvenance step) row with frameKind row | natEq step (proofStepId row)
... | provenanceFrame | true = accepted (expectContinuation step 0)
... | _ | _ = rejected
advancePhase (expectContinuation step next) row
  with frameKind row | natEq step (proofStepId row) | natEq next (continuationId row)
... | continuationFrame | true | true = accepted (expectMotifEnd step)
... | _ | _ | _ = rejected
advancePhase (expectMotifEnd step) row with frameKind row | natEq step (proofStepId row)
... | motifEndFrame | true = accepted betweenMotifs
... | _ | _ = rejected
advancePhase finished row = rejected

validateStructureFrom : ∀ {n} → TapePhase → ProofTape n → Bool
validateStructureFrom phase [] with phase
... | finished = true
... | _ = false
validateStructureFrom phase (row ∷ rows) with rowLocallyValid row
... | false = false
... | true with advancePhase phase row
...   | rejected = false
...   | accepted next = validateStructureFrom next rows

validateProofTape : ∀ {n} → ProofTape n → Bool
validateProofTape = validateStructureFrom expectStart

------------------------------------------------------------------------
-- Physical weaving projection.
-- Every row has a literal payload vector.  Metadata rows are intentionally
-- retained as rows: a machine profile may reserve certificate warp ends so the
-- proof framing/provenance is woven into the object rather than discarded.
------------------------------------------------------------------------

payloadLiftMask : ∀ {n} → ProofTapeRow n → Jacquard.LiftMask n
payloadLiftMask row = bitsToLiftMask (payload row)

payloadSchedule : ∀ {n} → ProofTape n → Jacquard.LiftSchedule n
payloadSchedule [] = []
payloadSchedule (row ∷ rows) = payloadLiftMask row ∷ payloadSchedule rows

wovenRows : ∀ {n} → ProofTape n → Jacquard.WovenRows n
wovenRows tape = Jacquard.executeSchedule (payloadSchedule tape)

record SelfDescribingProofTapeBoundary : Set where
  constructor self-describing-proof-tape-boundary
  field
    literalBitsLocallyParityCheckable : Bool
    framingAndMotifBoundariesTyped : Bool
    proofStepAndContinuationIdsPresent : Bool
    provenanceChannelPresent : Bool
    invalidLocalParityRejectsBeforeWeaving : Bool
    structuralOrderRejectsBeforeWeaving : Bool
    payloadRowsLowerToCanonicalJacquardSchedule : Bool
    metadataMustBePhysicallyPackedByMachineProfile : Bool

canonicalSelfDescribingProofTapeBoundary : SelfDescribingProofTapeBoundary
canonicalSelfDescribingProofTapeBoundary =
  self-describing-proof-tape-boundary
    true true true true true true true true

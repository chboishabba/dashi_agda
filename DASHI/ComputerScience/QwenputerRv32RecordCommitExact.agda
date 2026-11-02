module DASHI.ComputerScience.QwenputerRv32RecordCommitExact where

-- SOURCE:
-- Divyansh Agrawal, "RV32 inside Qwen3.5", P0/P1/P2 (2026),
-- https://github.com/divagr18/qwenputer/blob/main/experimental/riscv/docs/rv32.md
-- P0 "Trace format (spec.py)" and "The commit rule"; P2 QS/QD/BD.
--
-- DASHI-owned exact grammar and commit-timing theorem.
-- IMPORTANT: the earlier ADDR/VAL/STEP finite memory microprotocol in
-- QwenputerGatedDeltaArchitectureExact is not the source RV32 wire format.
-- The source uses record-final F0/F1/F2/NT/J/ST/SS/HALT tokens.
-- These proofs assume a supplied reference instruction transition; they
-- do not discharge real RV32 instruction decoding or compiled-weight
-- simulation. R and QS/QD/BD are nonterminal in the modeled records.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Faithful token FAMILY names. Payload ranges and the source's real
-- tokenizer indices require a separate codebook proof. No fake equality
-- with Qwenputer's emitted vocabulary is asserted here.
------------------------------------------------------------------------

data TraceToken : Set where
  V : Nat → TraceToken
  R : Nat → TraceToken
  QS QD BD : Nat → TraceToken
  FLT HEX : Nat → TraceToken
  F0 F1 F2 NT : TraceToken
  J : Nat → TraceToken
  ST0 ST1 SS0 SS1 : TraceToken
  HALT : TraceToken

-- Nonterminal tokens are statically separated from instruction commits.
data PrefixToken : Set where
  payload : Nat → PrefixToken
  refresh : Nat → PrefixToken
  quotientStart quotientDigit bignumDigit : Nat → PrefixToken
  faultCause faultHex : Nat → PrefixToken

data CommitToken : Set where
  shortValue mediumValue longValue noWrite : CommitToken
  jumpWord : Nat → CommitToken
  storeFullLow storeFullHigh storePartialLow storePartialHigh : CommitToken
  terminate : CommitToken

encodePrefix : PrefixToken → TraceToken
encodePrefix (payload n) = V n
encodePrefix (refresh n) = R n
encodePrefix (quotientStart n) = QS n
encodePrefix (quotientDigit n) = QD n
encodePrefix (bignumDigit n) = BD n
encodePrefix (faultCause n) = FLT n
encodePrefix (faultHex n) = HEX n

encodeCommit : CommitToken → TraceToken
encodeCommit shortValue = F0
encodeCommit mediumValue = F1
encodeCommit longValue = F2
encodeCommit noWrite = NT
encodeCommit (jumpWord n) = J n
encodeCommit storeFullLow = ST0
encodeCommit storeFullHigh = ST1
encodeCommit storePartialLow = SS0
encodeCommit storePartialHigh = SS1
encodeCommit terminate = HALT

-- Abstract ISA-state transition: the actual RV32 reference transition
-- must be supplied later, with proof it matches each emitted record.
stepToken : {State : Set} → (State → State) → TraceToken → State → State
stepToken execute (V _) s = s
stepToken execute (R _) s = s
stepToken execute (QS _) s = s
stepToken execute (QD _) s = s
stepToken execute (BD _) s = s
stepToken execute (FLT _) s = s
stepToken execute (HEX _) s = s
stepToken execute F0 s = execute s
stepToken execute F1 s = execute s
stepToken execute F2 s = execute s
stepToken execute NT s = execute s
stepToken execute (J _) s = execute s
stepToken execute ST0 s = execute s
stepToken execute ST1 s = execute s
stepToken execute SS0 s = execute s
stepToken execute SS1 s = execute s
stepToken execute HALT s = execute s

prefixDoesNotCommit :
  {State : Set} (execute : State → State)
  (p : PrefixToken) (s : State) →
  stepToken execute (encodePrefix p) s ≡ s
prefixDoesNotCommit execute (payload n) s = refl
prefixDoesNotCommit execute (refresh n) s = refl
prefixDoesNotCommit execute (quotientStart n) s = refl
prefixDoesNotCommit execute (quotientDigit n) s = refl
prefixDoesNotCommit execute (bignumDigit n) s = refl
prefixDoesNotCommit execute (faultCause n) s = refl
prefixDoesNotCommit execute (faultHex n) s = refl

finalTokenCommits :
  {State : Set} (execute : State → State)
  (last : CommitToken) (s : State) →
  stepToken execute (encodeCommit last) s ≡ execute s
finalTokenCommits execute shortValue s = refl
finalTokenCommits execute mediumValue s = refl
finalTokenCommits execute longValue s = refl
finalTokenCommits execute noWrite s = refl
finalTokenCommits execute (jumpWord n) s = refl
finalTokenCommits execute storeFullLow s = refl
finalTokenCommits execute storeFullHigh s = refl
finalTokenCommits execute storePartialLow s = refl
finalTokenCommits execute storePartialHigh s = refl
finalTokenCommits execute terminate s = refl

-- Executable, typed record emitter and independent flat-token interpreter.
emitRecord : List PrefixToken → CommitToken → List TraceToken
emitRecord [] last = encodeCommit last ∷ []
emitRecord (p ∷ ps) last = encodePrefix p ∷ emitRecord ps last

runTokens :
  {State : Set} → (State → State) → List TraceToken → State → State
runTokens execute [] s = s
runTokens execute (token ∷ tokens) s =
  runTokens execute tokens (stepToken execute token s)

-- A record cannot commit early, and MUST commit exactly once at its
-- terminal token. The reference transition is an explicit argument.
-- This is a theorem for all finite-length prefixes, not just examples.
recordExactlyOneCommit :
  {State : Set} (execute : State → State)
  (prefix : List PrefixToken) (last : CommitToken) (s : State) →
  runTokens execute (emitRecord prefix last) s ≡ execute s
recordExactlyOneCommit execute [] last s =
  finalTokenCommits execute last s
recordExactlyOneCommit execute (p ∷ ps) last s
  rewrite prefixDoesNotCommit execute p s =
  recordExactlyOneCommit execute ps last s

------------------------------------------------------------------------
-- Source-native instruction-record classes. These are the permitted
-- *examples* of the P0/P1/P2 trace shapes. The full codebook/formatter,
-- ISA operand decoding, long division and bignum carry machine are OPEN.
------------------------------------------------------------------------

data SourceRecord : Set where
  result15 : SourceRecord
  result30 : Nat → SourceRecord
  result45 : Nat → Nat → SourceRecord
  noRegisterWrite : SourceRecord
  takenBranch : Nat → SourceRecord
  storeWord : Bool → SourceRecord
  storeBytes : Nat → Nat → Nat → Bool → SourceRecord
  faultRecord : Nat → Nat → SourceRecord
  divisionResult : Nat → List Nat → Nat → SourceRecord
  bignumResult : List Nat → Nat → SourceRecord

divisionPrefix : List Nat → List PrefixToken
divisionPrefix [] = []
divisionPrefix (n ∷ ns) =
  quotientDigit n ∷ divisionPrefix ns

bignumPrefix : List Nat → List PrefixToken
bignumPrefix [] = []
bignumPrefix (n ∷ ns) =
  bignumDigit n ∷ bignumPrefix ns

addPrefix : List PrefixToken → List PrefixToken → List PrefixToken
addPrefix [] ys = ys
addPrefix (x ∷ xs) ys = x ∷ addPrefix xs ys

recordPrefix : SourceRecord → List PrefixToken
recordPrefix result15 = []
recordPrefix (result30 lo) = payload lo ∷ []
recordPrefix (result45 lo hi) = payload lo ∷ payload hi ∷ []
recordPrefix noRegisterWrite = []
recordPrefix (takenBranch _) = []
recordPrefix (storeWord _) = []
recordPrefix (storeBytes a b c _) =
  payload a ∷ payload b ∷ payload c ∷ []
recordPrefix (faultRecord cause pcword) =
  faultCause cause ∷ faultHex pcword ∷ []
recordPrefix (divisionResult k digits value) =
  quotientStart k ∷ addPrefix (divisionPrefix digits) (payload value ∷ [])
recordPrefix (bignumResult digits finalValue) =
  addPrefix (bignumPrefix digits) (payload finalValue ∷ [])

recordEnd : SourceRecord → CommitToken
recordEnd result15 = shortValue
recordEnd (result30 _) = mediumValue
recordEnd (result45 _ _) = longValue
recordEnd noRegisterWrite = noWrite
recordEnd (takenBranch target) = jumpWord target
recordEnd (storeWord false) = storeFullLow
recordEnd (storeWord true) = storeFullHigh
recordEnd (storeBytes a b c false) = storePartialLow
recordEnd (storeBytes a b c true) = storePartialHigh
recordEnd (faultRecord _ _) = terminate
recordEnd (divisionResult _ _ _) = mediumValue
recordEnd (bignumResult _ _) = mediumValue

emitSourceRecord : SourceRecord → List TraceToken
emitSourceRecord rec = emitRecord (recordPrefix rec) (recordEnd rec)

eachSourceRecordCommitsOnce :
  {State : Set} (execute : State → State)
  (rec : SourceRecord) (s : State) →
  runTokens execute (emitSourceRecord rec) s ≡ execute s
eachSourceRecordCommitsOnce execute rec s =
  recordExactlyOneCommit execute (recordPrefix rec) (recordEnd rec) s

recordValue30Example :
  emitSourceRecord (result30 37) ≡ V 37 ∷ F1 ∷ []
recordValue30Example = refl

recordMaskedStoreExample :
  emitSourceRecord (storeBytes 1 2 3 true)
  ≡ V 1 ∷ V 2 ∷ V 3 ∷ SS1 ∷ []
recordMaskedStoreExample = refl

-- No actual RV32 step function or source compiler equivalence is supplied.
record SourceTraceBoundary : Set where
  constructor sourceTraceBoundary
  field
    sourceTokenFamiliesTyped : Bool
    arbitraryRecordPrefixCannotCommit : Bool
    recordFinalTransitionOccursExactlyOnce : Bool
    realISAAndTokenizerSameObject : Bool

canonicalSourceTraceBoundary : SourceTraceBoundary
canonicalSourceTraceBoundary = sourceTraceBoundary true true true false

module DASHI.Research.OpenAIMath.OpenAIMathLiteralCodeTransportExact where

------------------------------------------------------------------------
-- M01a: source-list literal carrier/polarity bridge, on the ORIGINAL
-- finite CNF (not a replacement CNF evaluator or new SAT solver).
--
-- Existing source owner: FixedWidthTruthTableCNFExact.agda
-- Original circuit/gate compiler: PNotEqualsNPConcreteBooleanCircuitDAGExact
-- and OpenAIMathSharedTseitinOptimizedCNFExact, Golden #1040/#1212.
-- External source: openai/math 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a,
-- OAI/Algorithms/SubexponentialSAT/SAT.lean (Literal variable/positive),
-- Encoding.lean (literalCode=2*variable+(if positive then 1 else 0)).
--
-- UpstreamLiteral mirrors the two primitive fields solely to expose a
-- typed SAME-INDEX, SAME-POLARITY transport in Agda. The actual OAI Lean
-- SAT.Literal identity and Finset normalization/bitstream equality remain
-- cross-language M01 obligations, not results of a matching field shape.
-- SOURCE-WRITTEN; GOLDEN AGDA KERNEL ACCEPTANCE PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinGateCNFExact as Original
import DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinOptimizedCNFExact as Opt

-- Use the ORIGINAL Fin index, not a Nat that can point out of range.
data UpstreamLiteral (n : Nat) : Set where
  upstreamLiteral : Fin.Fin n → Bool → UpstreamLiteral n

encodeLiteral : ∀ {n : Nat} →
  CNF.Literal n → UpstreamLiteral n
encodeLiteral (CNF.positive index) = upstreamLiteral index true
encodeLiteral (CNF.negative index) = upstreamLiteral index false

decodeLiteral : ∀ {n : Nat} →
  UpstreamLiteral n → CNF.Literal n
decodeLiteral (upstreamLiteral index true) = CNF.positive index
decodeLiteral (upstreamLiteral index false) = CNF.negative index

decodeEncodeLiteral : ∀ {n : Nat} (literal : CNF.Literal n) →
  decodeLiteral (encodeLiteral literal) ≡ literal
decodeEncodeLiteral (CNF.positive index) = refl
decodeEncodeLiteral (CNF.negative index) = refl

encodeDecodeLiteral : ∀ {n : Nat} (literal : UpstreamLiteral n) →
  encodeLiteral (decodeLiteral literal) ≡ literal
encodeDecodeLiteral (upstreamLiteral index true) = refl
encodeDecodeLiteral (upstreamLiteral index false) = refl

-- Exactly the original OpenAI Encoding.literalCode arithmetic. In particular
-- positive contributes 2*i+1; negative contributes 2*i. This is polarity
-- and index identity; nothing is inferred from satisfiability alone.
sourceLiteralCode : ∀ {n : Nat} → CNF.Literal n → Nat
sourceLiteralCode (CNF.positive index) =
  2 * Fin.toℕ index + 1
sourceLiteralCode (CNF.negative index) =
  2 * Fin.toℕ index

upstreamLiteralCode : ∀ {n : Nat} → UpstreamLiteral n → Nat
upstreamLiteralCode (upstreamLiteral index true) =
  2 * Fin.toℕ index + 1
upstreamLiteralCode (upstreamLiteral index false) =
  2 * Fin.toℕ index

literalCodeExact : ∀ {n : Nat} (literal : CNF.Literal n) →
  upstreamLiteralCode (encodeLiteral literal) ≡
    sourceLiteralCode literal
literalCodeExact (CNF.positive index) = refl
literalCodeExact (CNF.negative index) = refl

encodeClause : ∀ {n : Nat} → CNF.Clause n → List (UpstreamLiteral n)
encodeClause = CNF.mapList encodeLiteral

decodeClause : ∀ {n : Nat} → List (UpstreamLiteral n) → CNF.Clause n
decodeClause = CNF.mapList decodeLiteral

decodeEncodeClause : ∀ {n : Nat} (clause : CNF.Clause n) →
  decodeClause (encodeClause clause) ≡ clause
decodeEncodeClause [] = refl
decodeEncodeClause (literal ∷ rest) =
  cong₂ _∷_ (decodeEncodeLiteral literal) (decodeEncodeClause rest)

encodeDecodeClause : ∀ {n : Nat} (clause : List (UpstreamLiteral n)) →
  encodeClause (decodeClause clause) ≡ clause
encodeDecodeClause [] = refl
encodeDecodeClause (literal ∷ rest) =
  cong₂ _∷_ (encodeDecodeLiteral literal) (encodeDecodeClause rest)

encodeSourceCNF : ∀ {n : Nat} →
  CNF.CNF n → List (List (UpstreamLiteral n))
encodeSourceCNF = CNF.mapList encodeClause

decodeSourceCNF : ∀ {n : Nat} →
  List (List (UpstreamLiteral n)) → CNF.CNF n
decodeSourceCNF = CNF.mapList decodeClause

decodeEncodeSourceCNF : ∀ {n : Nat} (source : CNF.CNF n) →
  decodeSourceCNF (encodeSourceCNF source) ≡ source
decodeEncodeSourceCNF [] = refl
decodeEncodeSourceCNF (clause ∷ rest) =
  cong₂ _∷_ (decodeEncodeClause clause) (decodeEncodeSourceCNF rest)

encodeDecodeSourceCNF : ∀ {n : Nat}
  (formula : List (List (UpstreamLiteral n))) →
  encodeSourceCNF (decodeSourceCNF formula) ≡ formula
encodeDecodeSourceCNF [] = refl
encodeDecodeSourceCNF (clause ∷ rest) =
  cong₂ _∷_ (encodeDecodeClause clause) (encodeDecodeSourceCNF rest)

-- Reuse original CNF.eval, rather than implementing another evaluator.
-- The Boolean function on EVERY finite assignment is literally unchanged.
sourceCNFTruthRoundTrip : ∀ {n : Nat} (source : CNF.CNF n)
  (bits : CNF.Bits n) →
  CNF.evaluateCNF (decodeSourceCNF (encodeSourceCNF source)) bits ≡
    CNF.evaluateCNF source bits
sourceCNFTruthRoundTrip source bits =
  cong (λ formula → CNF.evaluateCNF formula bits)
    (decodeEncodeSourceCNF source)

-- Literal-code LIST identity before Finset deduplication and sorting.
-- The OpenAI code rule is checked at each source literal recursively.
sourceClauseCodes : ∀ {n : Nat} → CNF.Clause n → List Nat
sourceClauseCodes = CNF.mapList sourceLiteralCode

upstreamClauseCodes : ∀ {n : Nat} →
  List (UpstreamLiteral n) → List Nat
upstreamClauseCodes = CNF.mapList upstreamLiteralCode

sourceClauseCodesExact : ∀ {n : Nat} (clause : CNF.Clause n) →
  upstreamClauseCodes (encodeClause clause) ≡ sourceClauseCodes clause
sourceClauseCodesExact [] = refl
sourceClauseCodesExact (literal ∷ rest) =
  cong₂ _∷_ (literalCodeExact literal) (sourceClauseCodesExact rest)

sourceCNFCodes : ∀ {n : Nat} → CNF.CNF n → List (List Nat)
sourceCNFCodes = CNF.mapList sourceClauseCodes

upstreamCNFCodes : ∀ {n : Nat} →
  List (List (UpstreamLiteral n)) → List (List Nat)
upstreamCNFCodes = CNF.mapList upstreamClauseCodes

sourceCNFCodesExact : ∀ {n : Nat} (source : CNF.CNF n) →
  upstreamCNFCodes (encodeSourceCNF source) ≡ sourceCNFCodes source
sourceCNFCodesExact [] = refl
sourceCNFCodesExact (clause ∷ rest) =
  cong₂ _∷_ (sourceClauseCodesExact clause) (sourceCNFCodesExact rest)

-- Most importantly this is now a consumer of the ORIGINAL optimized
-- source DAG CNF and the original placed-CNF semantics (not a fixture CNF).
originalOptimizedCircuitLiteralTruthExact : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs)
  (bits : CNF.Bits (inputs + Circuit.gateCount circuit)) →
  CNF.evaluateCNF
    (decodeSourceCNF (encodeSourceCNF (Opt.optCircuitCNF circuit))) bits
  ≡ CNF.evaluateCNF (Original.circuitPlacedCNF circuit) bits
originalOptimizedCircuitLiteralTruthExact circuit bits =
  trans
    (sourceCNFTruthRoundTrip (Opt.optCircuitCNF circuit) bits)
    (Opt.optCircuitEqualsOriginal circuit bits)

-- OPEN M01a/M01b: connect this typed Agda list of finite literals to the
-- *actual* OAI SAT.Literal (Fin n), prove normalize-to-Finset yields the
-- source compiler's SAME object, then verify Encoding.cnfNumbers/order and
-- encodeCNF emitted bits. A Lean theorem is not an imported Agda theorem.

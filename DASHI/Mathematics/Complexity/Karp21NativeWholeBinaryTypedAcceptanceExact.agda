module DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryTypedAcceptanceExact where

------------------------------------------------------------------------
-- E2: REAL binary-only executable N21 verifier computes the SAME
-- original *TYPED* Fin/Cut signed weighted Maximum-Cut decision on
-- every original graph/certificate word (including malformed).
--
-- Unlike prior Nat-header `nativeWholeWordAccepts`, the LHS here is
-- the actual B6 whole-binary graph/certificate program; only proof
-- transports may compute Nat, Fin, or ℤ values.
--
-- This compositional proof is kernel-dependent on both B6 complete
-- binary Fin-free agreement and the pre-existing original typed
-- graph word/certificate equivalence. No bit-machine clock follows.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierExact as Binary
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierOriginalExact as Whole
import DASHI.Mathematics.Complexity.Karp21FinFreeAllWordDecoderAgreementExact as Typed
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph

nativeCanonicalTypedSparseVerifierSameWord :
  (word certificate : Word.BitWord) →
  Binary.verifyNativeWholeBinaryGraphWord word certificate
    ≡ Graph.LiteralN21.verifyCanonicalSparseGraphWord word certificate
nativeCanonicalTypedSparseVerifierSameWord word certificate =
  trans
    (Whole.nativeWholeBinaryVerifierSameOriginalFinFree word certificate)
    (Typed.n21FinFreeVerifierSameWord word certificate)

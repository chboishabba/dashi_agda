module DASHI.Mathematics.Complexity.Karp21NativeOriginalSparseCertificateTightBoundExact where

------------------------------------------------------------------------
-- G3 improvement: actual accepted N21 certificate length <= ORIGINAL
-- graph-word length (coefficient 1, not the earlier 2), SOURCE ONLY.
--
-- This is a new cross-source transport, NOT an assumed arbitrary
-- certificate bound:
--   binary graph parse success
--     -> original FIN-FREE SAME-WORD graph parse success
--     -> original 3m input budget / 2m sparse endpoint bound
--     -> actual binary cursor's exact 2m-bit certificate
--     -> accepted verifier certificate <= original input length.
--
-- It inherits B6, original gamma/3m and sparse-verifier proof
-- dependencies. No Agda 2.9 acceptance or physical verifier clock
-- is asserted. This does NOT itself inhabit the abstract original
-- PR.polynomialCertificateBound field or PR.InNP.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (just; nothing)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Graph
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphOriginalExact as OriginalGraph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original
import DASHI.Mathematics.Complexity.Karp21FinFreeRawReaderSparseBudgetExact as Budget
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierExact as Verifier
import DASHI.Mathematics.Complexity.Karp21NativeOriginalSparseCertificateBoundExact as Cert
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive

-- The proof-only observation preserves ONE original raw edge per
-- selected binary raw-edge list entry, even for signed weights.
originalEdgeObservationPreservesCount :
  (edges : List Edge.BinaryRawEdge) →
  length (Edge.originalEdgeListObservation edges) ≡ length edges
originalEdgeObservationPreservesCount [] = refl
originalEdgeObservationPreservesCount (edge ∷ edges) =
  cong suc (originalEdgeObservationPreservesCount edges)

-- An ACTUAL successful binary parser result induces precisely that
-- same original successful Fin-free graph word, with no independent
-- reader assumption and no reserialization of the graph.
nativeGraphSuccessIsOriginalGraphSuccess :
  (word n threshold : Word.BitWord)
  (edges : List Edge.BinaryRawEdge) →
  Graph.readNativeWholeBinaryGraphWord word
    ≡ just (Graph.whole-binary-graph n edges threshold) →
  Original.readRawGraphWord word
    ≡ just (OriginalGraph.observeWholeBinaryGraph
      (Graph.whole-binary-graph n edges threshold))
nativeGraphSuccessIsOriginalGraphSuccess word n threshold edges parsed =
  trans
    (sym (OriginalGraph.nativeWholeBinaryGraphWordSameOriginal word))
    observed
  where
    observed :
      OriginalGraph.observeNativeWholeBinaryGraphWord word
        ≡ just (OriginalGraph.observeWholeBinaryGraph
          (Graph.whole-binary-graph n edges threshold))
    observed rewrite parsed = refl

-- The original successful graph grammar requires 3 input bits per
-- edge, hence it already pays the stronger 2m <= graph word length.
-- This transport is on the ACTUAL binary graph parser, not a
-- separately hypothesized graph instance.
nativeOriginalGraphSparseTwoPerEdgeBudget :
  (word n threshold : Word.BitWord)
  (edges : List Edge.BinaryRawEdge) →
  Graph.readNativeWholeBinaryGraphWord word
    ≡ just (Graph.whole-binary-graph n edges threshold) →
  Sparse.twoPerEdge (length edges) ≤ Word.encodingSize word
nativeOriginalGraphSparseTwoPerEdgeBudget
  word n threshold edges parsed =
  subst
    (λ count → Sparse.twoPerEdge count ≤ Word.encodingSize word)
    (originalEdgeObservationPreservesCount edges)
    (Budget.actualFinFreeRawGraphSuccessHasSparseBudget
      word
      (OriginalGraph.observeWholeBinaryGraph
        (Graph.whole-binary-graph n edges threshold))
      (nativeGraphSuccessIsOriginalGraphSuccess
        word n threshold edges parsed))

-- The actual binary verifier's successful certificate cursor returns
-- exactly two endpoint labels per raw edge. Convert the already
-- source-written n+n proof to the original sparse TWO-PER-EDGE type.
doubleIsSparseTwoPerEdge :
  (m : Nat) → m + m ≡ Sparse.twoPerEdge m
doubleIsSparseTwoPerEdge zero = refl
doubleIsSparseTwoPerEdge (suc m)
  rewrite NatP.+-suc m m
        | doubleIsSparseTwoPerEdge m = refl

actualSparseCursorCertificateExactlyTwoPerEdge :
  (edges : List Edge.BinaryRawEdge)
  (certificate : Word.BitWord)
  (history : History.BinaryEndpointHistory)
  (ledger result : Ledger.SignedLedger) →
  Verifier.readNativeBinaryCutLedger edges certificate history ledger
    ≡ just result →
  length certificate ≡ Sparse.twoPerEdge (length edges)
actualSparseCursorCertificateExactlyTwoPerEdge
  edges certificate history ledger result parsed =
  trans
    (Cert.nativeSuccessfulSparseCursorConsumesExactlyTwoBitsPerEdge
      edges certificate history ledger result parsed)
    (doubleIsSparseTwoPerEdge (length edges))

-- The SAME graph/certificate binary runtime, no arbitrary witness-
-- length premise: this is strictly stronger than the earlier
-- bound length(cert) <= length(graph) + length(graph).
actualOriginalN21CertificateTightBound :
  (word certificate n threshold : Word.BitWord)
  (edges : List Edge.BinaryRawEdge)
  (result : Ledger.SignedLedger) →
  Graph.readNativeWholeBinaryGraphWord word
    ≡ just (Graph.whole-binary-graph n edges threshold) →
  Verifier.readNativeBinaryCutLedger edges certificate []
    Ledger.emptyLedger ≡ just result →
  length certificate ≤ Word.encodingSize word
actualOriginalN21CertificateTightBound
  word certificate n threshold edges result graph checked =
  NatP.≤-trans
    (NatP.≤-reflexive
      (actualSparseCursorCertificateExactlyTwoPerEdge
        edges certificate [] Ledger.emptyLedger result checked))
    (nativeOriginalGraphSparseTwoPerEdgeBudget
      word n threshold edges graph)

-- G3 same-original-word ACCEPTED certificate endpoint: every actual
-- accepted binary N21 verification has a certificate no longer than
-- the original input word. No NP membership is claimed before the
-- physical verifier cost and source typed PR receipts are supplied.
actualN21AcceptedCertificateFitsOriginalGraphWord :
  (word certificate : Word.BitWord) →
  Verifier.verifyNativeWholeBinaryGraphWord word certificate ≡ true →
  Word.encodingSize certificate ≤ Word.encodingSize word
actualN21AcceptedCertificateFitsOriginalGraphWord word certificate accepted
  with Graph.readNativeWholeBinaryGraphWord word in graph
... | nothing with accepted
... | ()
... | just (Graph.whole-binary-graph n edges threshold)
  with Verifier.readNativeBinaryCutLedger
    edges certificate [] Ledger.emptyLedger in checked
... | nothing with accepted
... | ()
... | just result
  with Positive.meetsOriginalPositiveThreshold result threshold
... | false with accepted
... | ()
... | true =
  actualOriginalN21CertificateTightBound
    word certificate n threshold edges result graph checked

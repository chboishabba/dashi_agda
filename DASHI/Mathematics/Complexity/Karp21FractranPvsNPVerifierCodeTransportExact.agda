module DASHI.Mathematics.Complexity.Karp21FractranPvsNPVerifierCodeTransportExact where

------------------------------------------------------------------------
-- Karp-21 × original DASHI P-vs-NP executable-cost refinement.
--
-- Reuse PR #1129's actual ExecutableVerifierCode witness surface.
-- A code that realizes the source-authoritative original signed-ℤ
-- selected-trace verifier also realizes the SAME ORIGINAL typed N21
-- verifier, by the already written all-word word/certificate equality.
--
-- The source equality is NOT a machine clock. This module neither
-- creates an abstract-to-concrete code extractor nor a PR.InNP proof.
-- Executable code, runtime bounds and program-size accounting remain
-- independent paid inputs. No P != NP lower bound is inferred.
--
-- Source ownership: PNotEqualsNPExecutablePolynomialCostRefinementExact
-- (P-vs-NP PR #1129); Karp literal N21 and original-ℤ trace owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans; sym)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPExecutablePolynomialCostRefinementExact as PNP
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawTraceReplayExact as Trace
import DASHI.Mathematics.Complexity.Karp21FractranOriginalTypedTraceAcceptanceExact as Same
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph

OriginalTraceVerifier : Word.BitWord → Word.BitWord → Bool
OriginalTraceVerifier = Trace.verifyOriginalGraphWordByTrace

OriginalTypedVerifier : Word.BitWord → Word.BitWord → Bool
OriginalTypedVerifier =
  Graph.LiteralN21.verifyCanonicalSparseGraphWord

-- Preserve concrete executable machine and codeSize literally.
-- Only the proof of runExact is transported along the same-word
-- theorem: do not imply that compilation takes zero machine steps.
karpTraceCodeRealizesOriginalTypedN21 :
  PNP.ExecutableVerifierCode OriginalTraceVerifier →
  PNP.ExecutableVerifierCode OriginalTypedVerifier
karpTraceCodeRealizesOriginalTypedN21 traceCode = record
  { PNP.ExecutableVerifierCode.Code = PNP.ExecutableVerifierCode.Code traceCode
  ; PNP.ExecutableVerifierCode.code = PNP.ExecutableVerifierCode.code traceCode
  ; PNP.ExecutableVerifierCode.run = PNP.ExecutableVerifierCode.run traceCode
  ; PNP.ExecutableVerifierCode.runExact = λ word certificate →
      trans
        (PNP.ExecutableVerifierCode.runExact traceCode word certificate)
        (Same.karpOriginalTraceSameTypedN21AllWords
          word certificate)
  ; PNP.ExecutableVerifierCode.codeSize = PNP.ExecutableVerifierCode.codeSize traceCode
  }

-- The same result in the opposite direction: any executable N21
-- realization may be read as the source trace verifier.
karpTypedCodeRealizesOriginalTrace :
  PNP.ExecutableVerifierCode OriginalTypedVerifier →
  PNP.ExecutableVerifierCode OriginalTraceVerifier
karpTypedCodeRealizesOriginalTrace typedCode = record
  { PNP.ExecutableVerifierCode.Code = PNP.ExecutableVerifierCode.Code typedCode
  ; PNP.ExecutableVerifierCode.code = PNP.ExecutableVerifierCode.code typedCode
  ; PNP.ExecutableVerifierCode.run = PNP.ExecutableVerifierCode.run typedCode
  ; PNP.ExecutableVerifierCode.runExact = λ word certificate →
      trans
        (PNP.ExecutableVerifierCode.runExact typedCode word certificate)
        (sym (Same.karpOriginalTraceSameTypedN21AllWords
          word certificate))
  ; PNP.ExecutableVerifierCode.codeSize = PNP.ExecutableVerifierCode.codeSize typedCode
  }

-- A P-vs-NP refined witness can transport to typed N21 ONLY
-- if the selected polynomial-time model actually supplies the
-- required typed-verifier clock. No runtime proof is manufactured.
karpTraceRefinedToOriginalTyped :
  (cost : PR.PolynomialCostModel Word.BitWord) →
  PNP.ExecutablePolynomialTimeVerifier cost OriginalTraceVerifier →
  PR.polynomialTimeVerifier cost OriginalTypedVerifier →
  PNP.ExecutablePolynomialTimeVerifier cost OriginalTypedVerifier
karpTraceRefinedToOriginalTyped cost (traceClock , traceCode) typedClock =
  typedClock , karpTraceCodeRealizesOriginalTypedN21 traceCode

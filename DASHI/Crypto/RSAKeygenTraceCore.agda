module DASHI.Crypto.RSAKeygenTraceCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Crypto.RSAIterationLeakBoundary as RSAIterationLeakBoundary
import DASHI.Crypto.RSAKeygenSourceBoundary as RSAKeygenSourceBoundary

------------------------------------------------------------------------
-- RSA keygen trace core.
--
-- This module stays candidate-only.  It names the local trace vocabulary for
-- generator state, candidate draws, accepted-prime observations, observed
-- iteration count, private fibers, and the trace-to-fiber projections that
-- remain blocked from any authority-bearing reading.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Vocabulary.

data RSAKeygenTraceCoreKind : Set where
  generatorStateKind :
    RSAKeygenTraceCoreKind

  candidateDrawKind :
    RSAKeygenTraceCoreKind

  candidateAtKind :
    RSAKeygenTraceCoreKind

  acceptsPrimeKind :
    RSAKeygenTraceCoreKind

  observedIterationCountKind :
    RSAKeygenTraceCoreKind

  privateFiberKind :
    RSAKeygenTraceCoreKind

  privateFiberWithTraceKind :
    RSAKeygenTraceCoreKind

  traceShrinksFiberKind :
    RSAKeygenTraceCoreKind

  traceEvidenceProjectsToFiberKind :
    RSAKeygenTraceCoreKind

  namedRSAKeygenTraceCoreKind :
    String →
    RSAKeygenTraceCoreKind

canonicalRSAKeygenTraceCoreKinds :
  List RSAKeygenTraceCoreKind
canonicalRSAKeygenTraceCoreKinds =
  generatorStateKind
  ∷ candidateDrawKind
  ∷ candidateAtKind
  ∷ acceptsPrimeKind
  ∷ observedIterationCountKind
  ∷ privateFiberKind
  ∷ privateFiberWithTraceKind
  ∷ traceShrinksFiberKind
  ∷ traceEvidenceProjectsToFiberKind
  ∷ []

canonicalRSAKeygenTraceCoreKindCount : Nat
canonicalRSAKeygenTraceCoreKindCount =
  listCount canonicalRSAKeygenTraceCoreKinds

------------------------------------------------------------------------
-- Boundary labels.

canonicalRSAKeygenSourceBoundaryLabel : String
canonicalRSAKeygenSourceBoundaryLabel =
  RSAKeygenSourceBoundary.boundaryLabel
    RSAKeygenSourceBoundary.canonicalRSAKeygenSourceBoundarySurface

canonicalRSAIterationLeakBoundaryLabel : String
canonicalRSAIterationLeakBoundaryLabel =
  RSAIterationLeakBoundary.boundaryLabel
    RSAIterationLeakBoundary.canonicalRSAIterationLeakBoundary

canonicalRSAKeygenTraceSurfaceLabel : String
canonicalRSAKeygenTraceSurfaceLabel =
  "candidate-only RSA keygen trace core"

------------------------------------------------------------------------
-- Generator state.

record GeneratorState (sourceBoundaryLabel : String) : Set where
  constructor mkGeneratorState
  field
    generatorStateLabel :
      String

    generatorStateOwner :
      String

    generatorStateSurface :
      String

    generatorStateSourceBoundaryLabel :
      String

    generatorStateLeakBoundaryLabel :
      String

    hiddenGeneratorState :
      String

    candidatePrimeStream :
      String

    generatorStateAcceptancePredicate :
      String

    generatorStateObservableTrace :
      String

    sourceFiber :
      String

    generatorStateCandidateOnly :
      Bool

    generatorStatePromoted :
      Bool

    generatorStateCandidateOnlyIsTrue :
      generatorStateCandidateOnly ≡ true

    generatorStatePromotedIsFalse :
      generatorStatePromoted ≡ false

    generatorStateSourceBoundaryLabelMatches :
      generatorStateSourceBoundaryLabel ≡ sourceBoundaryLabel

    generatorStateLeakBoundaryLabelMatches :
      generatorStateLeakBoundaryLabel ≡
      canonicalRSAIterationLeakBoundaryLabel

open GeneratorState public

canonicalRSAKeygenTraceGeneratorState :
  GeneratorState canonicalRSAKeygenSourceBoundaryLabel
canonicalRSAKeygenTraceGeneratorState =
  mkGeneratorState
    "RSA keygen trace generator state"
    "DASHI.Crypto.RSAKeygenTraceCore"
    canonicalRSAKeygenTraceSurfaceLabel
    canonicalRSAKeygenSourceBoundaryLabel
    canonicalRSAIterationLeakBoundaryLabel
    "hidden generator state"
    "candidate-prime stream"
    "acceptance predicate"
    "observable trace"
    "source fiber"
    true
    false
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Candidate draws.

record CandidateDraw
  (sourceBoundaryLabel : String)
  (state : GeneratorState sourceBoundaryLabel)
  (drawIndex : Nat) :
  Set where
  constructor mkCandidateDraw
  field
    candidateDrawLabel :
      String

    candidateDrawOwner :
      String

    candidateDrawSurface :
      String

    candidateDrawSourceBoundaryLabel :
      String

    candidateDrawLeakBoundaryLabel :
      String

    candidateDrawState :
      GeneratorState sourceBoundaryLabel

    candidateDrawIterationIndex :
      Nat

    observedIterationCountField :
      Nat

    candidatePrime :
      String

    candidateDrawAcceptancePredicate :
      String

    candidateDrawObservableTrace :
      String

    acceptsPrimeField :
      Bool

    candidateDrawCandidateOnly :
      Bool

    candidateDrawPromoted :
      Bool

    candidateDrawCandidateOnlyIsTrue :
      candidateDrawCandidateOnly ≡ true

    candidateDrawPromotedIsFalse :
      candidateDrawPromoted ≡ false

    candidateDrawObservedIterationCountIsDrawIndex :
      observedIterationCountField ≡ drawIndex

    candidateDrawSourceBoundaryLabelMatches :
      candidateDrawSourceBoundaryLabel ≡ sourceBoundaryLabel

    candidateDrawLeakBoundaryLabelMatches :
      candidateDrawLeakBoundaryLabel ≡
      canonicalRSAIterationLeakBoundaryLabel

    acceptsPrimeFieldIsTrue :
      acceptsPrimeField ≡ true

open CandidateDraw public

candidateAt :
  ∀ {sourceBoundaryLabel} →
  (state : GeneratorState sourceBoundaryLabel) →
  (drawIndex : Nat) →
  CandidateDraw sourceBoundaryLabel state drawIndex
candidateAt {sourceBoundaryLabel} state drawIndex =
  mkCandidateDraw
    "RSA candidate-at draw"
    "DASHI.Crypto.RSAKeygenTraceCore"
    canonicalRSAKeygenTraceSurfaceLabel
    sourceBoundaryLabel
    canonicalRSAIterationLeakBoundaryLabel
    state
    drawIndex
    drawIndex
    "candidate prime"
    "accepts prime"
    "observable trace"
    true
    true
    false
    refl
    refl
    refl
    refl
    refl
    refl

acceptsPrime :
  ∀ {sourceBoundaryLabel}
  {state : GeneratorState sourceBoundaryLabel}
  {drawIndex : Nat} →
  CandidateDraw sourceBoundaryLabel state drawIndex →
  Bool
acceptsPrime draw =
  acceptsPrimeField draw

observedIterationCount :
  ∀ {sourceBoundaryLabel}
  {state : GeneratorState sourceBoundaryLabel}
  {drawIndex : Nat} →
  CandidateDraw sourceBoundaryLabel state drawIndex →
  Nat
observedIterationCount draw =
  observedIterationCountField draw

canonicalRSAKeygenTraceCandidateDraw :
  CandidateDraw
    canonicalRSAKeygenSourceBoundaryLabel
    canonicalRSAKeygenTraceGeneratorState
    zero
canonicalRSAKeygenTraceCandidateDraw =
  candidateAt canonicalRSAKeygenTraceGeneratorState zero

------------------------------------------------------------------------
-- Private fiber.

record PrivateFiber
  (sourceBoundaryLabel : String)
  (state : GeneratorState sourceBoundaryLabel)
  (iterationCount : Nat) :
  Set where
  constructor mkPrivateFiber
  field
    privateFiberLabel :
      String

    privateFiberOwner :
      String

    privateFiberSurface :
      String

    privateFiberSourceBoundaryLabel :
      String

    privateFiberLeakBoundaryLabel :
      String

    privateFiberState :
      GeneratorState sourceBoundaryLabel

    privateFiberCandidateDraw :
      CandidateDraw sourceBoundaryLabel state iterationCount

    privateFiberObservedIterationCount :
      Nat

    privateFiberObservedIterationCountIsIterationCount :
      privateFiberObservedIterationCount ≡ iterationCount

    privateFiberAcceptsPrime :
      acceptsPrime privateFiberCandidateDraw ≡ true

    privateFiberCandidateOnly :
      Bool

    privateFiberCandidateOnlyIsTrue :
      privateFiberCandidateOnly ≡ true

    privateFiberPromoted :
      Bool

    privateFiberPromotedIsFalse :
      privateFiberPromoted ≡ false

    privateFiberStatement :
      String

    privateFiberRemainingGap :
      String

open PrivateFiber public

canonicalRSAKeygenTracePrivateFiber :
  PrivateFiber
    canonicalRSAKeygenSourceBoundaryLabel
    canonicalRSAKeygenTraceGeneratorState
    zero
canonicalRSAKeygenTracePrivateFiber =
  mkPrivateFiber
    "RSA private fiber"
    "DASHI.Crypto.RSAKeygenTraceCore"
    "private fiber over candidate-only RSA keygen trace state"
    canonicalRSAKeygenSourceBoundaryLabel
    canonicalRSAIterationLeakBoundaryLabel
    canonicalRSAKeygenTraceGeneratorState
    canonicalRSAKeygenTraceCandidateDraw
    zero
    refl
    refl
    true
    refl
    false
    refl
    "private fiber is candidate-only and remains descriptive"
    "factor recovery, exploit authority, and side-channel authority remain blocked"

------------------------------------------------------------------------
-- Private fiber with trace.

record PrivateFiberWithTrace
  (sourceBoundaryLabel : String)
  (state : GeneratorState sourceBoundaryLabel)
  (iterationCount : Nat) :
  Set where
  constructor mkPrivateFiberWithTrace
  field
    privateFiber :
      PrivateFiber sourceBoundaryLabel state iterationCount

    traceProjectedFiber :
      PrivateFiber sourceBoundaryLabel state iterationCount

    traceCandidateDraw :
      CandidateDraw sourceBoundaryLabel state iterationCount

    traceObservedIterationCount :
      Nat

    traceObservedIterationCountIsIterationCount :
      traceObservedIterationCount ≡ iterationCount

    traceAcceptsPrime :
      acceptsPrime traceCandidateDraw ≡ true

    traceEvidenceLabel :
      String

    traceEvidenceSourceBoundaryLabel :
      String

    traceEvidenceLeakBoundaryLabel :
      String

    traceCandidateOnly :
      Bool

    traceCandidateOnlyIsTrue :
      traceCandidateOnly ≡ true

    tracePromoted :
      Bool

    tracePromotedIsFalse :
      tracePromoted ≡ false

open PrivateFiberWithTrace public

canonicalRSAKeygenTracePrivateFiberWithTrace :
  PrivateFiberWithTrace
    canonicalRSAKeygenSourceBoundaryLabel
    canonicalRSAKeygenTraceGeneratorState
    zero
canonicalRSAKeygenTracePrivateFiberWithTrace =
  mkPrivateFiberWithTrace
    canonicalRSAKeygenTracePrivateFiber
    canonicalRSAKeygenTracePrivateFiber
    canonicalRSAKeygenTraceCandidateDraw
    zero
    refl
    refl
    "RSA private fiber with trace"
    canonicalRSAKeygenSourceBoundaryLabel
    canonicalRSAIterationLeakBoundaryLabel
    true
    refl
    false
    refl

------------------------------------------------------------------------
-- Inclusion functions.

traceShrinksFiber :
  ∀ {sourceBoundaryLabel}
  {state : GeneratorState sourceBoundaryLabel}
  {iterationCount : Nat} →
  PrivateFiberWithTrace sourceBoundaryLabel state iterationCount →
  PrivateFiber sourceBoundaryLabel state iterationCount
traceShrinksFiber trace =
  privateFiber trace

traceEvidenceProjectsToFiber :
  ∀ {sourceBoundaryLabel}
  {state : GeneratorState sourceBoundaryLabel}
  {iterationCount : Nat} →
  PrivateFiberWithTrace sourceBoundaryLabel state iterationCount →
  PrivateFiber sourceBoundaryLabel state iterationCount
traceEvidenceProjectsToFiber trace =
  traceProjectedFiber trace

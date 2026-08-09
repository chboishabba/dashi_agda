module DASHI.Physics.Moonshine.MoonshineTraceIndexedWeaveExact where

open import DASHI.Core.Prelude

import DASHI.Core.IndexedWeaveHyperfabricExact as Indexed

------------------------------------------------------------------------
-- A finite proof-bearing trace-fibre model.
--
-- This is deliberately a bounded proxy rather than an actual Monster module.
-- Two distinct hidden states share one observed trace profile, while a hidden
-- residual tag separates them.  The trace fibres form an indexed weave whose
-- only paths are equality transports between profiles.
------------------------------------------------------------------------

data TraceProfile : Set where
  tracePrefixA tracePrefixB : TraceProfile

data FiniteTraceState : Set where
  hiddenStateA hiddenStateB hiddenStateC : FiniteTraceState

traceObservation : FiniteTraceState → TraceProfile
traceObservation hiddenStateA = tracePrefixA
traceObservation hiddenStateB = tracePrefixA
traceObservation hiddenStateC = tracePrefixB

data HiddenTraceTag : Set where
  tagA tagB tagC noTraceResidual : HiddenTraceTag

hiddenTag : FiniteTraceState → HiddenTraceTag
hiddenTag hiddenStateA = tagA
hiddenTag hiddenStateB = tagB
hiddenTag hiddenStateC = tagC

TraceFibre : TraceProfile → Set
TraceFibre profile =
  Σ FiniteTraceState
    (λ state → traceObservation state ≡ profile)

hiddenStateAInTraceA : TraceFibre tracePrefixA
hiddenStateAInTraceA = hiddenStateA , refl

hiddenStateBInTraceA : TraceFibre tracePrefixA
hiddenStateBInTraceA = hiddenStateB , refl

hiddenTagOfFibre :
  {profile : TraceProfile} →
  TraceFibre profile →
  HiddenTraceTag
hiddenTagOfFibre fibre = hiddenTag (fst fibre)

hiddenStateANotB : hiddenStateA ≡ hiddenStateB → ⊥
hiddenStateANotB ()

tagANotB : tagA ≡ tagB → ⊥
tagANotB ()

traceProjectionIsNonInjective :
  traceObservation hiddenStateA ≡ traceObservation hiddenStateB
  × hiddenStateA ≡ hiddenStateB → ⊥
traceProjectionIsNonInjective = refl , hiddenStateANotB

sameTraceFibreDifferentResidualTags :
  hiddenTagOfFibre hiddenStateAInTraceA
  ≡ hiddenTagOfFibre hiddenStateBInTraceA
  → ⊥
sameTraceFibreDifferentResidualTags = tagANotB

TracePath : TraceProfile → TraceProfile → Set
TracePath source target = source ≡ target

identityTracePath :
  (profile : TraceProfile) → TracePath profile profile
identityTracePath profile = refl

infixr 40 _thenTrace_

_thenTrace_ :
  {source middle target : TraceProfile} →
  TracePath middle target →
  TracePath source middle →
  TracePath source target
q thenTrace p = trans p q

tracePathIdLeft :
  {source target : TraceProfile} →
  (path : TracePath source target) →
  identityTracePath target thenTrace path ≡ path
tracePathIdLeft refl = refl

tracePathIdRight :
  {source target : TraceProfile} →
  (path : TracePath source target) →
  path thenTrace identityTracePath source ≡ path
tracePathIdRight refl = refl

tracePathAssoc :
  {i j k l : TraceProfile} →
  (r : TracePath k l) →
  (q : TracePath j k) →
  (p : TracePath i j) →
  (r thenTrace q) thenTrace p ≡ r thenTrace (q thenTrace p)
tracePathAssoc refl refl refl = refl

transportTraceFibre :
  {source target : TraceProfile} →
  TracePath source target →
  TraceFibre source →
  TraceFibre target
transportTraceFibre refl fibre = fibre

transportTraceIdentity :
  (profile : TraceProfile) →
  (fibre : TraceFibre profile) →
  transportTraceFibre (identityTracePath profile) fibre ≡ fibre
transportTraceIdentity profile fibre = refl

transportTraceComposition :
  {source middle target : TraceProfile} →
  (q : TracePath middle target) →
  (p : TracePath source middle) →
  (fibre : TraceFibre source) →
  transportTraceFibre (q thenTrace p) fibre
  ≡ transportTraceFibre q (transportTraceFibre p fibre)
transportTraceComposition refl refl fibre = refl

TraceResidual : TraceProfile → Set
TraceResidual profile = HiddenTraceTag

zeroTraceResidual :
  (profile : TraceProfile) → TraceResidual profile
zeroTraceResidual profile = noTraceResidual

traceResidualAfter :
  {source target : TraceProfile} →
  TracePath source target →
  TraceFibre source →
  TraceResidual target
traceResidualAfter path fibre = noTraceResidual

traceResidualIdentity :
  (profile : TraceProfile) →
  (fibre : TraceFibre profile) →
  traceResidualAfter (identityTracePath profile) fibre
  ≡ zeroTraceResidual profile
traceResidualIdentity profile fibre = refl

canonicalMoonshineTraceIndexedWeave :
  Indexed.IndexedWeave TraceProfile TraceFibre
canonicalMoonshineTraceIndexedWeave =
  record
    { Path = TracePath
    ; idPath = identityTracePath
    ; _∙_ = _thenTrace_
    ; pathIdLeft = tracePathIdLeft
    ; pathIdRight = tracePathIdRight
    ; pathAssoc = tracePathAssoc
    ; transport = transportTraceFibre
    ; transportId = transportTraceIdentity
    ; transportComp = transportTraceComposition
    ; Residual = TraceResidual
    ; zeroResidual = zeroTraceResidual
    ; residualAfter = traceResidualAfter
    ; residualId = traceResidualIdentity
    }

record MoonshineTraceFibreBoundary : Set where
  constructor moonshineTraceFibreBoundary
  field
    boundedTraceProjectionIsNonInjective :
      traceObservation hiddenStateA ≡ traceObservation hiddenStateB
      × hiddenStateA ≡ hiddenStateB → ⊥
    boundedTraceResidualDistinguishes :
      hiddenTagOfFibre hiddenStateAInTraceA
      ≡ hiddenTagOfFibre hiddenStateBInTraceA
      → ⊥
    actualMonsterRepresentationConstructed : Bool
    actualMonsterRepresentationConstructedIsFalse :
      actualMonsterRepresentationConstructed ≡ false
    actualMcKayThompsonTraceEqualityProved : Bool
    actualMcKayThompsonTraceEqualityProvedIsFalse :
      actualMcKayThompsonTraceEqualityProved ≡ false

canonicalMoonshineTraceFibreBoundary : MoonshineTraceFibreBoundary
canonicalMoonshineTraceFibreBoundary =
  moonshineTraceFibreBoundary
    traceProjectionIsNonInjective
    sameTraceFibreDifferentResidualTags
    false refl
    false refl

module DASHI.Foundations.DiachronicFieldZeroToNine where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv; inv-invol)

------------------------------------------------------------------------
-- Stage-indexed field hierarchy
--
-- Important boundary: the numerals 3, 6, and 9 are not asserted to be
-- non-trivial idempotent elements of one common ring.  Each is a stage name
-- whose carrier has its own local closure operator.
------------------------------------------------------------------------

data Stage : Set where
  stage0 stage1 stage2 stage3 stage4 : Stage
  stage5 stage6 stage7 stage8 stage9 : Stage

previous : Stage → Stage
previous stage0 = stage0
previous stage1 = stage0
previous stage2 = stage1
previous stage3 = stage2
previous stage4 = stage3
previous stage5 = stage4
previous stage6 = stage5
previous stage7 = stage6
previous stage8 = stage7
previous stage9 = stage8

------------------------------------------------------------------------
-- The trans-story reading is represented as a typed interpretation surface.
-- It does not decide a person's identity; it records which relation is live.
------------------------------------------------------------------------

data IdentityClaim : Set where
  transClaim       : IdentityClaim
  notTransClaim    : IdentityClaim
  indeterminate    : IdentityClaim
  bothConditionally : IdentityClaim

data Viewpoint : Set where
  embodiedSelf rememberedSelf anticipatedSelf socialOther : Viewpoint

data TransStageMeaning : Stage → Set where
  presemanticAffect : TransStageMeaning stage0
  inheritedRule     : TransStageMeaning stage1
  liveOpposition    : TransStageMeaning stage2
  triadicResolution : TransStageMeaning stage3
  socialProjection  : TransStageMeaning stage4
  temporalMirror    : TransStageMeaning stage5
  contextualPlurality : TransStageMeaning stage6
  diachronicHarmony : TransStageMeaning stage7
  constructAwareness : TransStageMeaning stage8
  higherOrderWitness : TransStageMeaning stage9

------------------------------------------------------------------------
-- Stage 2: identity of the opposition/tension under discussion.
------------------------------------------------------------------------

record Opposition : Set where
  constructor opposition
  field
    positivePole : IdentityClaim
    negativePole : IdentityClaim

transOpposition : Opposition
transOpposition = opposition transClaim notTransClaim

TensionState : Set
TensionState = Viewpoint → Trit

canonicalTransTension : TensionState
canonicalTransTension embodiedSelf   = pos
canonicalTransTension rememberedSelf = zer
canonicalTransTension anticipatedSelf = pos
canonicalTransTension socialOther    = neg

------------------------------------------------------------------------
-- Field-local idempotents.
--
-- A LocalClosure is the exact mathematical content intended by saying that
-- 3, 6, or 9 is the idempotent "of its level": each stage has a projector on
-- its own carrier, and applying that projector twice changes nothing further.
------------------------------------------------------------------------

record LocalClosure (S : Stage) : Set₁ where
  field
    Carrier : Set
    close   : Carrier → Carrier
    close-idempotent : (x : Carrier) → close (close x) ≡ close x

------------------------------------------------------------------------
-- Lower closures are retained when promoted into a higher field.
------------------------------------------------------------------------

record PreservesLower
  {lower higher : Stage}
  (L : LocalClosure lower)
  (H : LocalClosure higher) : Set₁ where
  field
    embed : LocalClosure.Carrier L → LocalClosure.Carrier H
    preservesClosure : (x : LocalClosure.Carrier L) →
      embed (LocalClosure.close L x) ≡
      LocalClosure.close H (embed x)

------------------------------------------------------------------------
-- Stage 3: resolution does not erase the opposition; it closes a situated
-- reading into a stable claim while retaining its provenance.
------------------------------------------------------------------------

record TriadicResolution : Set where
  constructor resolved
  field
    tension  : Opposition
    viewpoint : Viewpoint
    claim    : IdentityClaim

resolveAtSelf : TriadicResolution
resolveAtSelf = resolved transOpposition embodiedSelf transClaim

stage3Closure : LocalClosure stage3
stage3Closure = record
  { Carrier = TriadicResolution
  ; close = λ x → x
  ; close-idempotent = λ _ → refl
  }

------------------------------------------------------------------------
-- Stage 6: bidirectional fold and contextual non-globality.
--
-- The fold is an involution.  No global inverse for every interpretation is
-- assumed.  Instead, local contexts may admit stabilisers.
------------------------------------------------------------------------

record SixField : Set where
  constructor sixView
  field
    pastView    : IdentityClaim
    presentView : IdentityClaim
    futureView  : IdentityClaim
    otherView   : IdentityClaim

sixFold : SixField → SixField
sixFold (sixView past present future other) =
  sixView future present past other

sixFold-involutive : (x : SixField) → sixFold (sixFold x) ≡ x
sixFold-involutive (sixView past present future other) = refl

stage6Closure : LocalClosure stage6
stage6Closure = record
  { Carrier = SixField
  ; close = λ x → sixFold (sixFold x)
  ; close-idempotent = λ _ → refl
  }

record LocalStabiliser (A : Set) : Set₁ where
  field
    stabilise : A → A
    stableAfterOne : (x : A) → stabilise (stabilise x) ≡ stabilise x

------------------------------------------------------------------------
-- Stage 9: a higher-order state contains several six-views and several
-- triadic resolutions.  It may also include causalities not centred on the
-- current subject, social possibility spaces, and alternative law spaces.
------------------------------------------------------------------------

data NineTensorKind : Set where
  selfHistory societyForm societyThought physicalLaw externalCausality : NineTensorKind

record NineTensor : Set where
  constructor tensor
  field
    kind : NineTensorKind
    localSign : Trit

record NineField : Set where
  constructor nineView
  field
    triadicView : Viewpoint → TriadicResolution
    sixViewAt   : Viewpoint → SixField
    tensorAt    : NineTensorKind → NineTensor

stage9Closure : LocalClosure stage9
stage9Closure = record
  { Carrier = NineField
  ; close = λ x → x
  ; close-idempotent = λ _ → refl
  }

------------------------------------------------------------------------
-- Nested preservation witnesses: local 3-closures survive inside 6, and
-- local 6-closures survive inside 9.  These are explicit obligations rather
-- than consequences of numerology.
------------------------------------------------------------------------

embed3Into6 : TriadicResolution → SixField
embed3Into6 r =
  sixView
    (TriadicResolution.claim r)
    (TriadicResolution.claim r)
    (TriadicResolution.claim r)
    indeterminate

threeInsideSix : PreservesLower stage3Closure stage6Closure
threeInsideSix = record
  { embed = embed3Into6
  ; preservesClosure = λ _ → refl
  }

emptyTensor : NineTensorKind → NineTensor
emptyTensor k = tensor k zer

embed6Into9 : SixField → NineField
embed6Into9 s =
  nineView
    (λ v → resolved transOpposition v indeterminate)
    (λ _ → s)
    emptyTensor

sixInsideNine : PreservesLower stage6Closure stage9Closure
sixInsideNine = record
  { embed = embed6Into9
  ; preservesClosure = λ _ → refl
  }

------------------------------------------------------------------------
-- N-dimensional diffraction pattern.
--
-- An axis is intentionally abstract: temporal, somatic, social, legal,
-- cultural, physical-law, and unrelated-causality axes can coexist.  A
-- diffraction pattern is the signed response over those axes.  Promotion
-- transports the old pattern while permitting additional dimensions.
------------------------------------------------------------------------

DiffractionPattern : Set → Set
DiffractionPattern Axis = Axis → Trit

pointwiseMirror : {Axis : Set} → DiffractionPattern Axis → DiffractionPattern Axis
pointwiseMirror pattern axis = inv (pattern axis)

pointwiseMirror-involutive :
  {Axis : Set} (pattern : DiffractionPattern Axis) (axis : Axis) →
  pointwiseMirror (pointwiseMirror pattern) axis ≡ pattern axis
pointwiseMirror-involutive pattern axis = inv-invol (pattern axis)

record DiffractionPromotion (LowAxis HighAxis : Set) : Set₁ where
  field
    injectAxis : LowAxis → HighAxis
    promote : DiffractionPattern LowAxis → DiffractionPattern HighAxis
    preservesOldAxes : (p : DiffractionPattern LowAxis) (a : LowAxis) →
      promote p (injectAxis a) ≡ p a

------------------------------------------------------------------------
-- Signed stage observation.  Positive/zero/negative are observations of a
-- state at a stage, never moral rankings of persons or identities.
------------------------------------------------------------------------

record SignedObservation (S : Stage) : Set where
  constructor observed
  field
    meaning : TransStageMeaning S
    sign    : Trit

positiveResolution : SignedObservation stage3
positiveResolution = observed triadicResolution pos

pluralBoundary : SignedObservation stage6
pluralBoundary = observed contextualPlurality zer

higherIntegration : SignedObservation stage9
higherIntegration = observed higherOrderWitness pos

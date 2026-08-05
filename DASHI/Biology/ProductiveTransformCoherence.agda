module DASHI.Biology.ProductiveTransformCoherence where

open import DASHI.Core.Prelude

import DASHI.Biology.StateDependentMultiplexTransducer as Stateful

------------------------------------------------------------------------
-- Productive coherence is compositional compatibility, not vector alignment.
-- Heterogeneous encodings may differ in sign, coordinates, phase, or carrier
-- while preserving a shared latent relation through approximately commuting
-- transforms.  This exact finite core uses zero compositional defect; later
-- metric consumers may weaken equality to a bounded defect.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

Transform : Set → Set → Set
Transform A B = A → B

infixr 9 _∘_

_∘_ :
  ∀ {A B C : Set} →
  Transform B C →
  Transform A B →
  Transform A C
(g ∘ f) x = g (f x)

identity : ∀ {A : Set} → Transform A A
identity x = x

record CommutingTriangle : Set₁ where
  field
    Input : Set
    Middle : Set
    Output : Set

    direct : Transform Input Output
    first : Transform Input Middle
    second : Transform Middle Output

    zeroDefect :
      (x : Input) →
      direct x ≡ second (first x)

open CommutingTriangle public

record LatentRealisationSquare : Set₁ where
  field
    Latent : Set
    PhysicalA : Set
    PhysicalB : Set

    latentUpdate : Transform Latent Latent
    encodeA : Transform Latent PhysicalA
    encodeB : Transform Latent PhysicalB
    physicalTransform : Transform PhysicalA PhysicalB

    representationCompatibility :
      (z : Latent) →
      physicalTransform (encodeA z)
      ≡
      encodeB (latentUpdate z)

open LatentRealisationSquare public

record ProductiveOpposition : Set₁ where
  field
    Carrier : Set
    firstOpposingTransform : Transform Carrier Carrier
    secondOpposingTransform : Transform Carrier Carrier

    recomposesToIdentity :
      (x : Carrier) →
      secondOpposingTransform (firstOpposingTransform x) ≡ x

open ProductiveOpposition public

------------------------------------------------------------------------
-- Exact examples.

canonicalDoubleInhibitionTriangle : CommutingTriangle
canonicalDoubleInhibitionTriangle =
  record
    { Input = Bool
    ; Middle = Bool
    ; Output = Bool
    ; direct = identity
    ; first = Stateful.boolNot
    ; second = Stateful.boolNot
    ; zeroDefect = λ x → sym (Stateful.boolNotInvolutive x)
    }

canonicalDoubleInhibitionIsProductive :
  (x : Bool) →
  direct canonicalDoubleInhibitionTriangle x
  ≡
  second canonicalDoubleInhibitionTriangle
    (first canonicalDoubleInhibitionTriangle x)
canonicalDoubleInhibitionIsProductive =
  zeroDefect canonicalDoubleInhibitionTriangle

canonicalProductiveOpposition : ProductiveOpposition
canonicalProductiveOpposition =
  record
    { Carrier = Bool
    ; firstOpposingTransform = Stateful.boolNot
    ; secondOpposingTransform = Stateful.boolNot
    ; recomposesToIdentity = Stateful.boolNotInvolutive
    }

------------------------------------------------------------------------
-- The same latent structure may have different local physical coordinates.
-- Here chart A uses x and chart B uses not x.  The chart transition is also
-- not, so the square commutes exactly even though the coordinate values differ.

canonicalLatentRealisationSquare : LatentRealisationSquare
canonicalLatentRealisationSquare =
  record
    { Latent = Bool
    ; PhysicalA = Bool
    ; PhysicalB = Bool
    ; latentUpdate = identity
    ; encodeA = identity
    ; encodeB = Stateful.boolNot
    ; physicalTransform = Stateful.boolNot
    ; representationCompatibility = λ z → refl
    }

canonicalLatentFalseUsesDifferentCoordinates :
  encodeA canonicalLatentRealisationSquare false
  ≢
  encodeB canonicalLatentRealisationSquare false
canonicalLatentFalseUsesDifferentCoordinates =
  Stateful.false≢true

canonicalLatentSquareCommutes :
  (z : Bool) →
  physicalTransform canonicalLatentRealisationSquare
    (encodeA canonicalLatentRealisationSquare z)
  ≡
  encodeB canonicalLatentRealisationSquare
    (latentUpdate canonicalLatentRealisationSquare z)
canonicalLatentSquareCommutes =
  representationCompatibility canonicalLatentRealisationSquare

------------------------------------------------------------------------
-- Productive noncommutativity / braid-order residual.
--
-- Applying inhibition before a saturating-true gate differs from applying
-- the same gate before inhibition.  The difference is not an error in the
-- formalism: it is a proof that path order carries information.

setTrue : Bool → Bool
setTrue _ = true

inhibitThenSaturate : Bool → Bool
inhibitThenSaturate =
  setTrue ∘ Stateful.boolNot

saturateThenInhibit : Bool → Bool
saturateThenInhibit =
  Stateful.boolNot ∘ setTrue

canonicalOrderResidualAtFalse :
  inhibitThenSaturate false
  ≢
  saturateThenInhibit false
canonicalOrderResidualAtFalse =
  Stateful.true≢false

record TransformOrderResidual : Set₁ where
  field
    Carrier : Set
    transformA : Transform Carrier Carrier
    transformB : Transform Carrier Carrier
    witness : Carrier

    orderedResultsDiffer :
      transformB (transformA witness)
      ≢
      transformA (transformB witness)

open TransformOrderResidual public

canonicalTransformOrderResidual : TransformOrderResidual
canonicalTransformOrderResidual =
  record
    { Carrier = Bool
    ; transformA = Stateful.boolNot
    ; transformB = setTrue
    ; witness = false
    ; orderedResultsDiffer = canonicalOrderResidualAtFalse
    }

record ProductiveCoherenceBoundary : Set where
  constructor productiveCoherenceBoundary
  field
    coherenceRequiresParallelVectors : Bool
    coherenceRequiresParallelVectorsIsFalse :
      coherenceRequiresParallelVectors ≡ false

    oppositionIsAlwaysDestructive : Bool
    oppositionIsAlwaysDestructiveIsFalse :
      oppositionIsAlwaysDestructive ≡ false

    transformOrderCanAlwaysBeDiscarded : Bool
    transformOrderCanAlwaysBeDiscardedIsFalse :
      transformOrderCanAlwaysBeDiscarded ≡ false

    exactCommutationImpliesBiologicalIdentity : Bool
    exactCommutationImpliesBiologicalIdentityIsFalse :
      exactCommutationImpliesBiologicalIdentity ≡ false

canonicalProductiveCoherenceBoundary : ProductiveCoherenceBoundary
canonicalProductiveCoherenceBoundary =
  productiveCoherenceBoundary
    false refl
    false refl
    false refl
    false refl

module DASHI.Topology.ClopenNDimFibreBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.TriadicFiniteQuotient as Quotient

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc n) = base * pow base n

immediateChildCount : Nat → Nat
immediateChildCount dimension = pow 3 dimension

oneDimChildren : immediateChildCount 1 ≡ 3
oneDimChildren = refl

twoDimChildren : immediateChildCount 2 ≡ 9
twoDimChildren = refl

threeDimChildren : immediateChildCount 3 ≡ 27
threeDimChildren = refl

record ClopenBallDescriptor : Set where
  constructor clopenBallDescriptor
  field
    centreLabel : String
    prefixDepth : Nat
    fibreDimension : Nat
    childCount : Nat
    childCountChecks : childCount ≡ immediateChildCount fibreDimension
    interpretation : String

open ClopenBallDescriptor public

canonicalTwoDimBall : ClopenBallDescriptor
canonicalTwoDimBall =
  clopenBallDescriptor
    "shared two-coordinate prefix"
    4
    2
    9
    refl
    "a two-dimensional triadic clopen context has nine immediate child contexts"

FiniteFibreAt : Nat → Nat → Set
FiniteFibreAt depth dimension = Quotient.Residue3Pow (depth * dimension)

record PantsFibreBundleBoundary : Set₁ where
  field
    Base : Set
    Fibre : Base → Set
    Section : Set
    sectionAt : Section → (base : Base) → Fibre base
    pantsBaseConnected : Set
    fibresClopen : Set
    routingLaw : Set
    gluingLaw : Set

record ClopenNDimBoundary : Set where
  constructor clopenNDimBoundary
  field
    clopenBallIsConnectedRealPants : Bool
    clopenBallIsConnectedRealPantsIsFalse :
      clopenBallIsConnectedRealPants ≡ false
    dimensionDeterminesImmediateTriadicChildren : Bool
    finitePrefixModelIsFullPadicAnalyticSpace : Bool
    finitePrefixModelIsFullPadicAnalyticSpaceIsFalse :
      finitePrefixModelIsFullPadicAnalyticSpace ≡ false
    arbitraryBundleGluingPromoted : Bool
    arbitraryBundleGluingPromotedIsFalse : arbitraryBundleGluingPromoted ≡ false
    interpretation : String

canonicalClopenNDimBoundary : ClopenNDimBoundary
canonicalClopenNDimBoundary =
  clopenNDimBoundary
    false refl
    true
    false refl
    false refl
    "connected pants/rhizome geometry may carry totally disconnected finite or p-adic fibres; one-, two-, and three-coordinate fibres expose 3, 9, and 27 local refinements"

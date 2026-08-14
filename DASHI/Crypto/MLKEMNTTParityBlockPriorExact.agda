module DASHI.Crypto.MLKEMNTTParityBlockPriorExact where

------------------------------------------------------------------------
-- TWO-BLOCK PRIOR FACTORISATION, THEN QUADRATIC RECOUPLING
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- SamplePolyCBD samples source coefficients independently in R_q. Reduction
-- modulo each quadratic factor sends even source powers to the constant part
-- and odd source powers to the linear part.  Hence a product source prior has a
-- natural two-block even/odd transport.
--
-- FIPS BaseCaseMultiply (Algorithm 12) immediately recouples those target
-- components:
--   c0 = a0*b0 + a1*b1*gamma
--   c1 = a0*b1 + a1*b0.
--
-- Thus the useful positive decomposition is at most a two-block prior split at
-- this level; it is not 128 independently searchable verifier lanes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Generic exact support-level product-prior transport.
------------------------------------------------------------------------

record ProductPriorTransform : Set₁ where
  constructor productPriorTransform
  field
    EvenSource OddSource ConstantTarget LinearTarget : Set
    encodeEven : EvenSource → ConstantTarget
    decodeEven : ConstantTarget → EvenSource
    encodeOdd : OddSource → LinearTarget
    decodeOdd : LinearTarget → OddSource
    evenRoundTrip : ∀ source → decodeEven (encodeEven source) ≡ source
    oddRoundTrip : ∀ source → decodeOdd (encodeOdd source) ≡ source
    EvenPrior : EvenSource → Set
    OddPrior : OddSource → Set

open ProductPriorTransform public

TargetPrior :
  (transform : ProductPriorTransform) →
  ConstantTarget transform → LinearTarget transform → Set
TargetPrior transform constant linear =
  EvenPrior transform (decodeEven transform constant)
  × OddPrior transform (decodeOdd transform linear)

targetPriorFactorsByParity :
  ∀ (transform : ProductPriorTransform) constant linear →
  TargetPrior transform constant linear →
  EvenPrior transform (decodeEven transform constant)
  × OddPrior transform (decodeOdd transform linear)
targetPriorFactorsByParity transform constant linear prior = prior

sourcePriorMapsToProductTargetPrior :
  ∀ (transform : ProductPriorTransform) even odd →
  EvenPrior transform even →
  OddPrior transform odd →
  TargetPrior transform
    (encodeEven transform even)
    (encodeOdd transform odd)
sourcePriorMapsToProductTargetPrior transform even odd evenPrior oddPrior
  rewrite evenRoundTrip transform even
        | oddRoundTrip transform odd =
  evenPrior , oddPrior

------------------------------------------------------------------------
-- Exact source-block sizes across the approved module dimensions.
------------------------------------------------------------------------

parityBlockSourceCoefficientCount : Nat → Nat
parityBlockSourceCoefficientCount k = k * 128

totalSourceSecretCoefficientCount : Nat → Nat
totalSourceSecretCoefficientCount k = 2 * parityBlockSourceCoefficientCount k

mlKem512ParityBlockCount : parityBlockSourceCoefficientCount 2 ≡ 256
mlKem512ParityBlockCount = refl

mlKem768ParityBlockCount : parityBlockSourceCoefficientCount 3 ≡ 384
mlKem768ParityBlockCount = refl

mlKem1024ParityBlockCount : parityBlockSourceCoefficientCount 4 ≡ 512
mlKem1024ParityBlockCount = refl

mlKem512TwoParityBlocksCoverSecret : totalSourceSecretCoefficientCount 2 ≡ 512
mlKem512TwoParityBlocksCoverSecret = refl

mlKem768TwoParityBlocksCoverSecret : totalSourceSecretCoefficientCount 3 ≡ 768
mlKem768TwoParityBlocksCoverSecret = refl

mlKem1024TwoParityBlocksCoverSecret : totalSourceSecretCoefficientCount 4 ≡ 1024
mlKem1024TwoParityBlocksCoverSecret = refl

------------------------------------------------------------------------
-- FIPS quadratic multiplication dependency.
------------------------------------------------------------------------

data LocalComponent : Set where
  component0 component1 : LocalComponent

data UsesInputComponent : LocalComponent → LocalComponent → Set where
  c0Uses0 : UsesInputComponent component0 component0
  c0Uses1 : UsesInputComponent component0 component1
  c1Uses0 : UsesInputComponent component1 component0
  c1Uses1 : UsesInputComponent component1 component1

record OutputUsesBothInputs (output : LocalComponent) : Set where
  constructor outputUsesBothInputs
  field
    uses0 : UsesInputComponent output component0
    uses1 : UsesInputComponent output component1

open OutputUsesBothInputs public

baseCaseOutput0UsesBoth : OutputUsesBothInputs component0
baseCaseOutput0UsesBoth = outputUsesBothInputs c0Uses0 c0Uses1

baseCaseOutput1UsesBoth : OutputUsesBothInputs component1
baseCaseOutput1UsesBoth = outputUsesBothInputs c1Uses0 c1Uses1

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record ParityPriorVerifierBoundary : Set where
  constructor parityPriorVerifierBoundary
  field
    paritySplitRequiresProductSourcePrior : Bool
    paritySplitRequiresProductSourcePriorIsTrue :
      paritySplitRequiresProductSourcePrior ≡ true
    baseCaseMultiplicationRecouplesBothComponents : Bool
    baseCaseMultiplicationRecouplesBothComponentsIsTrue :
      baseCaseMultiplicationRecouplesBothComponents ≡ true
    twoPriorBlocksMeanTwoIndependentVerifierProblems : Bool
    twoPriorBlocksMeanTwoIndependentVerifierProblemsIsFalse :
      twoPriorBlocksMeanTwoIndependentVerifierProblems ≡ false
    parityFactorisationMeans128IndependentLanes : Bool
    parityFactorisationMeans128IndependentLanesIsFalse :
      parityFactorisationMeans128IndependentLanes ≡ false

open ParityPriorVerifierBoundary public

canonicalParityPriorVerifierBoundary : ParityPriorVerifierBoundary
canonicalParityPriorVerifierBoundary =
  parityPriorVerifierBoundary true refl true refl false refl false refl

module DASHI.Crypto.MLKEMNTTParityBlockPriorExact where

------------------------------------------------------------------------
-- TWO-BLOCK PRIOR FACTORISATION, THEN QUADRATIC RECOUPLING
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- SamplePolyCBD samples source coefficients independently in R_q.  Reduction
-- modulo each quadratic factor sends even powers to the constant part and odd
-- powers to the linear part.  Thus, at the carrier/support level, a coefficient-
-- product prior admits a natural two-block split (even/odd source coefficients).
--
-- But FIPS BaseCaseMultiply (Algorithm 12) recombines the two components:
--   c0 = a0*b0 + a1*b1*gamma
--   c1 = a0*b1 + a1*b0.
-- Hence the public noisy equations do not become two independent verifier
-- problems merely because the source prior admits two parity blocks.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
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
-- FIPS quadratic multiplication dependency.
--
-- The formulas are represented as dependency evidence rather than redoing
-- modular arithmetic here.  Both output components consume both secret/input
-- components, which is the exact reconciliation seam for a two-block prior.
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

record ParityPriorVerifierBoundary : Set where
  constructor parityPriorVerifierBoundary
  field
    sourcePriorCanSplitIntoTwoParityBlocks : Set
    baseCaseMultiplicationRecouplesBlocks : Set

open ParityPriorVerifierBoundary public

canonicalParityPriorVerifierBoundary : ParityPriorVerifierBoundary
canonicalParityPriorVerifierBoundary =
  parityPriorVerifierBoundary
    (OutputUsesBothInputs component0)
    (OutputUsesBothInputs component1)

------------------------------------------------------------------------
-- Interpretation boundary:
--
-- * two parity blocks is a potentially useful prior factorisation;
-- * it is not 128 independently searchable NTT lanes;
-- * Algorithm-12 multiplication immediately creates a reconciliation relation
--   between the two local components inside every quadratic coordinate.
------------------------------------------------------------------------

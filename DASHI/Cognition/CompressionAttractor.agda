{-# OPTIONS --safe #-}
module DASHI.Cognition.CompressionAttractor where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit as T using (Trit; neg; zer; pos)
open import DASHI.Foundations.TernaryBlockRenormalisation as B
  using
    ( Trit3
    ; tri
    ; first
    ; coarse3
    ; refineDiagonal
    ; coarse-refineDiagonal
    )

------------------------------------------------------------------------
-- Compression attractors
--
-- The analytic phrase "converges to an attractor" is represented here by an
-- exact finite settling certificate.  An analytic or continuous model can
-- instantiate the same interface with a discretised certified settling time,
-- while this module itself makes no unproved limit claim.

iterate : {State : Set} → Nat → (State → State) → State → State
iterate zero step state = state
iterate (suc n) step state = iterate n step (step state)

CompressionEquivalent :
  {State Code : Set} →
  (State → Code) →
  State →
  State →
  Set
CompressionEquivalent compress left right =
  compress left ≡ compress right

compression-equivalent-reflexive :
  {State Code : Set}
  (compress : State → Code)
  (state : State) →
  CompressionEquivalent compress state state
compression-equivalent-reflexive compress state = refl

compression-equivalent-symmetric :
  {State Code : Set}
  (compress : State → Code)
  {left right : State} →
  CompressionEquivalent compress left right →
  CompressionEquivalent compress right left
compression-equivalent-symmetric compress equality = sym equality

compression-equivalent-transitive :
  {State Code : Set}
  (compress : State → Code)
  {left middle right : State} →
  CompressionEquivalent compress left middle →
  CompressionEquivalent compress middle right →
  CompressionEquivalent compress left right
compression-equivalent-transitive compress left≈middle middle≈right =
  trans left≈middle middle≈right

record CompressionAttractor (State Code : Set) : Set₁ where
  field
    step : State → State
    compress : State → Code
    Basin : Code → State → Set
    centre : Code → State
    settlingTime : Code → State → Nat

    basin-settles :
      ∀ {code state} →
      Basin code state →
      compress (iterate (settlingTime code state) step state) ≡ code

    centre-in-basin :
      (code : Code) →
      Basin code (centre code)

    centre-fixed :
      (code : Code) →
      step (centre code) ≡ centre code

    centre-represents :
      (code : Code) →
      compress (centre code) ≡ code

open CompressionAttractor public

record StrictCompressionWitness
  {State Code : Set}
  (compress : State → Code) : Set where
  field
    leftMicrostate : State
    rightMicrostate : State
    microstates-distinct :
      ¬ (leftMicrostate ≡ rightMicrostate)
    sameCompressedCode :
      compress leftMicrostate ≡ compress rightMicrostate

open StrictCompressionWitness public

------------------------------------------------------------------------
-- Concrete instance on the existing exact DASHI 3 -> 1 block.
--
-- The canonicalisation map replaces a microstate by the chosen diagonal
-- representative of its coarse trit.  It therefore settles in one step and
-- preserves the coarse code exactly.

canonicaliseBlock : Trit3 → Trit3
canonicaliseBlock state =
  refineDiagonal (coarse3 state)

blockBasin : Trit → Trit3 → Set
blockBasin code state =
  coarse3 state ≡ code

blockSettlingTime : Trit → Trit3 → Nat
blockSettlingTime code state = 1

block-basin-settles :
  ∀ {code state} →
  blockBasin code state →
  coarse3
    (iterate
      (blockSettlingTime code state)
      canonicaliseBlock
      state)
    ≡ code
block-basin-settles {code} {state} basin =
  trans
    (coarse-refineDiagonal (coarse3 state))
    basin

block-centre-in-basin :
  (code : Trit) →
  blockBasin code (refineDiagonal code)
block-centre-in-basin =
  coarse-refineDiagonal

block-centre-fixed :
  (code : Trit) →
  canonicaliseBlock (refineDiagonal code) ≡ refineDiagonal code
block-centre-fixed code
  rewrite coarse-refineDiagonal code = refl

block-centre-represents :
  (code : Trit) →
  coarse3 (refineDiagonal code) ≡ code
block-centre-represents =
  coarse-refineDiagonal

blockCompressionAttractor : CompressionAttractor Trit3 Trit
blockCompressionAttractor =
  record
    { step = canonicaliseBlock
    ; compress = coarse3
    ; Basin = blockBasin
    ; centre = refineDiagonal
    ; settlingTime = blockSettlingTime
    ; basin-settles = block-basin-settles
    ; centre-in-basin = block-centre-in-basin
    ; centre-fixed = block-centre-fixed
    ; centre-represents = block-centre-represents
    }

block-canonicalisation-idempotent :
  (state : Trit3) →
  canonicaliseBlock (canonicaliseBlock state) ≡
  canonicaliseBlock state
block-canonicalisation-idempotent state
  rewrite coarse-refineDiagonal (coarse3 state) = refl

neg-is-not-zero : ¬ (neg ≡ zer)
neg-is-not-zero ()

zero-fibre-microstates-distinct :
  ¬ (tri neg pos zer ≡ tri zer zer zer)
zero-fibre-microstates-distinct equality =
  neg-is-not-zero (cong first equality)

block-strict-compression :
  StrictCompressionWitness coarse3
block-strict-compression =
  record
    { leftMicrostate = tri neg pos zer
    ; rightMicrostate = tri zer zer zer
    ; microstates-distinct = zero-fibre-microstates-distinct
    ; sameCompressedCode = refl
    }

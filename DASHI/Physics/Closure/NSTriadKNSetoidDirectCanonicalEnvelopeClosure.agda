module DASHI.Physics.Closure.NSTriadKNSetoidDirectCanonicalEnvelopeClosure where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- Loukas Grafakos; Rodolfo H. Torres; Augustin-Louis Cauchy; Agda
-- standard-library contributors; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; "A Multilinear Schur Test and Multiplier Operators"; and
-- "Setoid direct-canonical 128/93 output-relocation closure".
-- Venue/year: Springer, 1985; Dalhousie University/arXiv, 2022; Journal of
-- Functional Analysis 187 (2001), 1--24; Agda standard library; DASHI formal
-- development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- 10.1006/jfan.2001.3804; the repository theorem has no DOI.
-- Uses: the exact rational canonical kernel
--   (1/4)^j (1/32)^d
-- and its cutoff-uniform mass 128/93, transported into an ordered setoid by a
-- rational embedding.
-- Relationship: removes global exp/log and arbitrary-real power operations
-- from the proof-critical path.  A caller proves the literal coefficient is
-- directly sandwiched by the embedded canonical kernel; all finite summation
-- and the two-sided 128/93 conclusion then follow constructively.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Rational

record SetoidOrderedRationalEnvelopeCarrier {s e : Level} :
    Set (lsuc (s Level.⊔ e)) where
  field
    Scalar : Set s
    _≈_ : Scalar → Scalar → Set e
    zero : Scalar
    add : Scalar → Scalar → Scalar
    negate : Scalar → Scalar
    leq : Scalar → Scalar → Set s
    rationalEmbed : ℚ → Scalar

    approxReflexive : ∀ value → _≈_ value value
    approxSymmetric : ∀ {left right} → _≈_ left right → _≈_ right left
    approxTransitive : ∀ {a b c} → _≈_ a b → _≈_ b c → _≈_ a c

    addCongruent : ∀ {a a′ b b′} →
      _≈_ a a′ → _≈_ b b′ → _≈_ (add a b) (add a′ b′)
    negateCongruent : ∀ {a b} → _≈_ a b → _≈_ (negate a) (negate b)

    leqReflexive : ∀ value → leq value value
    leqTransitive : ∀ {a b c} → leq a b → leq b c → leq a c
    leqRespectsLeft : ∀ {a a′ b} → _≈_ a a′ → leq a b → leq a′ b
    leqRespectsRight : ∀ {a b b′} → _≈_ b b′ → leq a b → leq a b′
    addMonotone : ∀ {a b c d} →
      leq a b → leq c d → leq (add a c) (add b d)
    negateAntitone : ∀ {a b} → leq a b → leq (negate b) (negate a)

    negateAdd : ∀ a b →
      _≈_ (negate (add a b)) (add (negate a) (negate b))

    embedZero : _≈_ (rationalEmbed 0ℚ) zero
    embedAdd : ∀ left right →
      _≈_ (rationalEmbed (left + right))
          (add (rationalEmbed left) (rationalEmbed right))
    embedOrder : ∀ {left right} →
      left ≤ right → leq (rationalEmbed left) (rationalEmbed right)

open SetoidOrderedRationalEnvelopeCarrier public

sumTo : ∀ {s e} (C : SetoidOrderedRationalEnvelopeCarrier {s} {e}) →
  (Nat → Scalar C) → Nat → Scalar C
sumTo C values zero = values zero
sumTo C values (suc cutoff) =
  add C (values (suc cutoff)) (sumTo C values cutoff)

sumToCong : ∀ {s e} (C : SetoidOrderedRationalEnvelopeCarrier {s} {e})
    left right cutoff →
  (∀ index → _≈_ C (left index) (right index)) →
  _≈_ C (sumTo C left cutoff) (sumTo C right cutoff)
sumToCong C left right zero pointwise = pointwise zero
sumToCong C left right (suc cutoff) pointwise =
  addCongruent C
    (pointwise (suc cutoff))
    (sumToCong C left right cutoff pointwise)

sumToMonotone : ∀ {s e} (C : SetoidOrderedRationalEnvelopeCarrier {s} {e})
    left right cutoff →
  (∀ index → leq C (left index) (right index)) →
  leq C (sumTo C left cutoff) (sumTo C right cutoff)
sumToMonotone C left right zero pointwise = pointwise zero
sumToMonotone C left right (suc cutoff) pointwise =
  addMonotone C
    (pointwise (suc cutoff))
    (sumToMonotone C left right cutoff pointwise)

sumEmbedMeaning : ∀ {s e}
    (C : SetoidOrderedRationalEnvelopeCarrier {s} {e}) values cutoff →
  _≈_ C
    (sumTo C (λ index → rationalEmbed C (values index)) cutoff)
    (rationalEmbed C (Rational.sumTo values cutoff))
sumEmbedMeaning C values zero = approxReflexive C _
sumEmbedMeaning C values (suc cutoff) =
  approxTransitive C
    (addCongruent C
      (approxReflexive C _)
      (sumEmbedMeaning C values cutoff))
    (approxSymmetric C
      (embedAdd C
        (values (suc cutoff))
        (Rational.sumTo values cutoff)))

rowSum : ∀ {s e} (C : SetoidOrderedRationalEnvelopeCarrier {s} {e}) →
  (Nat → Nat → Scalar C) → Nat → Nat → Scalar C
rowSum C kernel lowShell gapCutoff =
  sumTo C (kernel lowShell) gapCutoff

rectangleSum : ∀ {s e} (C : SetoidOrderedRationalEnvelopeCarrier {s} {e}) →
  (Nat → Nat → Scalar C) → Nat → Nat → Scalar C
rectangleSum C kernel lowCutoff gapCutoff =
  sumTo C
    (λ lowShell → rowSum C kernel lowShell gapCutoff)
    lowCutoff

rectangleSumMonotone : ∀ {s e}
    (C : SetoidOrderedRationalEnvelopeCarrier {s} {e})
    left right lowCutoff gapCutoff →
  (∀ low gap → leq C (left low gap) (right low gap)) →
  leq C
    (rectangleSum C left lowCutoff gapCutoff)
    (rectangleSum C right lowCutoff gapCutoff)
rectangleSumMonotone C left right lowCutoff gapCutoff pointwise =
  sumToMonotone C
    (λ low → rowSum C left low gapCutoff)
    (λ low → rowSum C right low gapCutoff)
    lowCutoff
    (λ low →
      sumToMonotone C
        (left low) (right low) gapCutoff (pointwise low))

rowEmbedMeaning : ∀ {s e}
    (C : SetoidOrderedRationalEnvelopeCarrier {s} {e})
    kernel lowShell gapCutoff →
  _≈_ C
    (rowSum C
      (λ low gap → rationalEmbed C (kernel low gap))
      lowShell gapCutoff)
    (rationalEmbed C (Rational.rowSum kernel lowShell gapCutoff))
rowEmbedMeaning C kernel lowShell gapCutoff =
  sumEmbedMeaning C (kernel lowShell) gapCutoff

rectangleEmbedMeaning : ∀ {s e}
    (C : SetoidOrderedRationalEnvelopeCarrier {s} {e})
    kernel lowCutoff gapCutoff →
  _≈_ C
    (rectangleSum C
      (λ low gap → rationalEmbed C (kernel low gap))
      lowCutoff gapCutoff)
    (rationalEmbed C
      (Rational.rectangleSum kernel lowCutoff gapCutoff))
rectangleEmbedMeaning C kernel lowCutoff gapCutoff =
  approxTransitive C
    (sumToCong C
      (λ low →
        rowSum C
          (λ left gap → rationalEmbed C (kernel left gap))
          low gapCutoff)
      (λ low →
        rationalEmbed C (Rational.rowSum kernel low gapCutoff))
      lowCutoff
      (λ low → rowEmbedMeaning C kernel low gapCutoff))
    (sumEmbedMeaning C
      (λ low → Rational.rowSum kernel low gapCutoff)
      lowCutoff)

embeddedCanonicalCutoffBound : ∀ {s e}
    (C : SetoidOrderedRationalEnvelopeCarrier {s} {e})
    lowCutoff gapCutoff →
  leq C
    (rectangleSum C
      (λ low gap → rationalEmbed C (Rational.canonicalKernel low gap))
      lowCutoff gapCutoff)
    (rationalEmbed C Geo.oneTwentyEightNinetyThirds)
embeddedCanonicalCutoffBound C lowCutoff gapCutoff =
  leqRespectsLeft C
    (approxSymmetric C
      (rectangleEmbedMeaning C
        Rational.canonicalKernel lowCutoff gapCutoff))
    (embedOrder C
      (Rational.canonicalKernelCutoffUniformBound
        lowCutoff gapCutoff))

sumToNeg : ∀ {s e}
    (C : SetoidOrderedRationalEnvelopeCarrier {s} {e})
    values cutoff →
  _≈_ C
    (sumTo C (λ index → negate C (values index)) cutoff)
    (negate C (sumTo C values cutoff))
sumToNeg C values zero = approxReflexive C _
sumToNeg C values (suc cutoff) =
  approxTransitive C
    (addCongruent C
      (approxReflexive C _)
      (sumToNeg C values cutoff))
    (approxSymmetric C
      (negateAdd C
        (values (suc cutoff))
        (sumTo C values cutoff)))

rectangleSumNeg : ∀ {s e}
    (C : SetoidOrderedRationalEnvelopeCarrier {s} {e})
    kernel lowCutoff gapCutoff →
  _≈_ C
    (rectangleSum C
      (λ low gap → negate C (kernel low gap))
      lowCutoff gapCutoff)
    (negate C (rectangleSum C kernel lowCutoff gapCutoff))
rectangleSumNeg C kernel lowCutoff gapCutoff =
  approxTransitive C
    (sumToCong C
      (λ low →
        rowSum C (λ left gap → negate C (kernel left gap))
          low gapCutoff)
      (λ low → negate C (rowSum C kernel low gapCutoff))
      lowCutoff
      (λ low → sumToNeg C (kernel low) gapCutoff))
    (sumToNeg C
      (λ low → rowSum C kernel low gapCutoff)
      lowCutoff)

record DirectCanonicalCoefficientBridge {s e}
    (C : SetoidOrderedRationalEnvelopeCarrier {s} {e}) :
    Set (lsuc (s Level.⊔ e)) where
  field
    signedCoefficient : Nat → Nat → Scalar C
    signedCoefficientUpper : ∀ low gap →
      leq C
        (signedCoefficient low gap)
        (rationalEmbed C (Rational.canonicalKernel low gap))
    signedCoefficientLower : ∀ low gap →
      leq C
        (negate C
          (rationalEmbed C (Rational.canonicalKernel low gap)))
        (signedCoefficient low gap)

open DirectCanonicalCoefficientBridge public

record SetoidDirectCanonicalArchetypeTheorem {s e}
    (C : SetoidOrderedRationalEnvelopeCarrier {s} {e})
    (bridge : DirectCanonicalCoefficientBridge C) :
    Set (lsuc (s Level.⊔ e)) where
  field
    cutoffUpper : ∀ lowCutoff gapCutoff →
      leq C
        (rectangleSum C (signedCoefficient bridge)
          lowCutoff gapCutoff)
        (rationalEmbed C Geo.oneTwentyEightNinetyThirds)
    cutoffLower : ∀ lowCutoff gapCutoff →
      leq C
        (negate C (rationalEmbed C Geo.oneTwentyEightNinetyThirds))
        (rectangleSum C (signedCoefficient bridge)
          lowCutoff gapCutoff)

open SetoidDirectCanonicalArchetypeTheorem public

setoidDirectCanonicalArchetypeTheorem : ∀ {s e}
    (C : SetoidOrderedRationalEnvelopeCarrier {s} {e})
    (bridge : DirectCanonicalCoefficientBridge C) →
  SetoidDirectCanonicalArchetypeTheorem C bridge
setoidDirectCanonicalArchetypeTheorem C bridge = record
  { cutoffUpper = λ lowCutoff gapCutoff →
      leqTransitive C
        (rectangleSumMonotone C
          (signedCoefficient bridge)
          (λ low gap →
            rationalEmbed C (Rational.canonicalKernel low gap))
          lowCutoff gapCutoff
          (signedCoefficientUpper bridge))
        (embeddedCanonicalCutoffBound C lowCutoff gapCutoff)
  ; cutoffLower = λ lowCutoff gapCutoff →
      let
        canonical = λ low gap →
          rationalEmbed C (Rational.canonicalKernel low gap)
        canonicalBound =
          embeddedCanonicalCutoffBound C lowCutoff gapCutoff
        negatedBound = negateAntitone C canonicalBound
        pointwiseLower =
          rectangleSumMonotone C
            (λ low gap → negate C (canonical low gap))
            (signedCoefficient bridge)
            lowCutoff gapCutoff
            (signedCoefficientLower bridge)
      in
      leqTransitive C
        negatedBound
        (leqTransitive C
          (leqRespectsLeft C
            (approxSymmetric C
              (rectangleSumNeg C canonical lowCutoff gapCutoff))
            (leqReflexive C
              (negate C
                (rectangleSum C canonical lowCutoff gapCutoff))))
          pointwiseLower)
  }

setoidDirectCanonicalSummationClosed : Bool
setoidDirectCanonicalSummationClosed = true

setoidDirectCanonicalExpLogIndependent : Bool
setoidDirectCanonicalExpLogIndependent = true

setoidDirectCanonicalSummationClosedIsTrue :
  setoidDirectCanonicalSummationClosed ≡ true
setoidDirectCanonicalSummationClosedIsTrue = refl

setoidDirectCanonicalExpLogIndependentIsTrue :
  setoidDirectCanonicalExpLogIndependent ≡ true
setoidDirectCanonicalExpLogIndependentIsTrue = refl

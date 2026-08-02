module DASHI.Physics.Closure.NSTriadKNOutputRelocationEmbeddedEnvelopeClosure where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Loukas Grafakos;
-- Rodolfo H. Torres; Augustin-Louis Cauchy; Agda standard-library
-- contributors; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; "A Multilinear Schur Test and Multiplier Operators"; and
-- "Ordered rational-embedding closure of the output-relocation envelope".
-- Venue/year: Springer, 1985; arXiv, 2022; Journal of Functional Analysis 187
-- (2001), 1--24; Agda standard library; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- 10.1006/jfan.2001.3804; the repository transport theorem has no DOI.
-- Uses: the exact rational 128/93 cutoff bound, an ordered semiring-like
-- carrier with an order-preserving rational embedding, and termwise low/gap
-- plus signed-coefficient domination.
-- Relationship: proves the physical-carrier cutoff bound abstractly.  It
-- separates the already-closed rational summation from the remaining concrete
-- adapter: instantiate the ordered carrier, prove the two H^s factor
-- comparisons, and prove the literal coefficient's two-sided domination.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as RationalMajorant

record OrderedRationalEnvelopeCarrier {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    zero : Scalar
    add multiply : Scalar → Scalar → Scalar
    negate : Scalar → Scalar
    leq : Scalar → Scalar → Set s
    rationalEmbed : ℚ → Scalar

    leqReflexive : ∀ value → leq value value
    leqTransitive : ∀ {a b c} → leq a b → leq b c → leq a c
    addMonotone : ∀ {a b c d} →
      leq a b → leq c d → leq (add a c) (add b d)
    multiplyMonotoneNonnegative : ∀ {a b c d} →
      leq zero a → leq a b → leq zero c → leq c d →
      leq (multiply a c) (multiply b d)
    negateAntitone : ∀ {a b} → leq a b → leq (negate b) (negate a)
    negateAdd : ∀ a b →
      negate (add a b) ≡ add (negate a) (negate b)

    embedZero : rationalEmbed 0ℚ ≡ zero
    embedAdd : ∀ left right →
      rationalEmbed (left + right)
      ≡ add (rationalEmbed left) (rationalEmbed right)
    embedMultiply : ∀ left right →
      rationalEmbed (left * right)
      ≡ multiply (rationalEmbed left) (rationalEmbed right)
    embedOrder : ∀ {left right} →
      left ≤ right → leq (rationalEmbed left) (rationalEmbed right)

open OrderedRationalEnvelopeCarrier public

sumTo : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s}) →
  (Nat → Scalar C) → Nat → Scalar C
sumTo C values zero = values zero
sumTo C values (suc cutoff) =
  add C (values (suc cutoff)) (sumTo C values cutoff)

sumToCong : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s})
    left right cutoff →
  (∀ index → left index ≡ right index) →
  sumTo C left cutoff ≡ sumTo C right cutoff
sumToCong C left right zero pointwise = pointwise zero
sumToCong C left right (suc cutoff) pointwise =
  cong₂ (add C)
    (pointwise (suc cutoff))
    (sumToCong C left right cutoff pointwise)

sumToMonotone : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s})
    left right cutoff →
  (∀ index → leq C (left index) (right index)) →
  leq C (sumTo C left cutoff) (sumTo C right cutoff)
sumToMonotone C left right zero pointwise = pointwise zero
sumToMonotone C left right (suc cutoff) pointwise =
  addMonotone C
    (pointwise (suc cutoff))
    (sumToMonotone C left right cutoff pointwise)

sumEmbedMeaning : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s})
    values cutoff →
  sumTo C (λ index → rationalEmbed C (values index)) cutoff
  ≡ rationalEmbed C (RationalMajorant.sumTo values cutoff)
sumEmbedMeaning C values zero = refl
sumEmbedMeaning C values (suc cutoff) =
  trans
    (cong
      (λ rest →
        add C (rationalEmbed C (values (suc cutoff))) rest)
      (sumEmbedMeaning C values cutoff))
    (sym
      (embedAdd C
        (values (suc cutoff))
        (RationalMajorant.sumTo values cutoff)))

rowSum : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s}) →
  (Nat → Nat → Scalar C) → Nat → Nat → Scalar C
rowSum C kernel lowShell gapCutoff =
  sumTo C (kernel lowShell) gapCutoff

rectangleSum : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s}) →
  (Nat → Nat → Scalar C) → Nat → Nat → Scalar C
rectangleSum C kernel lowCutoff gapCutoff =
  sumTo C (λ lowShell → rowSum C kernel lowShell gapCutoff) lowCutoff

rectangleSumMonotone : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s})
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

rowEmbedMeaning : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s})
    kernel lowShell gapCutoff →
  rowSum C
    (λ low gap → rationalEmbed C (kernel low gap))
    lowShell gapCutoff
  ≡ rationalEmbed C
      (RationalMajorant.rowSum kernel lowShell gapCutoff)
rowEmbedMeaning C kernel lowShell gapCutoff =
  sumEmbedMeaning C (kernel lowShell) gapCutoff

rectangleEmbedMeaning : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s})
    kernel lowCutoff gapCutoff →
  rectangleSum C
    (λ low gap → rationalEmbed C (kernel low gap))
    lowCutoff gapCutoff
  ≡ rationalEmbed C
      (RationalMajorant.rectangleSum kernel lowCutoff gapCutoff)
rectangleEmbedMeaning C kernel lowCutoff gapCutoff =
  trans
    (sumToCong C
      (λ low →
        rowSum C
          (λ left gap → rationalEmbed C (kernel left gap))
          low gapCutoff)
      (λ low →
        rationalEmbed C
          (RationalMajorant.rowSum kernel low gapCutoff))
      lowCutoff
      (λ low → rowEmbedMeaning C kernel low gapCutoff))
    (sumEmbedMeaning C
      (λ low → RationalMajorant.rowSum kernel low gapCutoff)
      lowCutoff)

embeddedCanonicalCutoffBound : ∀ {s}
    (C : OrderedRationalEnvelopeCarrier {s}) lowCutoff gapCutoff →
  leq C
    (rectangleSum C
      (λ low gap →
        rationalEmbed C (RationalMajorant.canonicalKernel low gap))
      lowCutoff gapCutoff)
    (rationalEmbed C Geo.oneTwentyEightNinetyThirds)
embeddedCanonicalCutoffBound C lowCutoff gapCutoff =
  let
    embeddedRationalBound =
      embedOrder C
        (RationalMajorant.canonicalKernelCutoffUniformBound
          lowCutoff gapCutoff)
  in
  subst
    (λ left →
      leq C left (rationalEmbed C Geo.oneTwentyEightNinetyThirds))
    (sym
      (rectangleEmbedMeaning C
        RationalMajorant.canonicalKernel lowCutoff gapCutoff))
    embeddedRationalBound

sumToNeg : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s})
    values cutoff →
  sumTo C (λ index → negate C (values index)) cutoff
  ≡ negate C (sumTo C values cutoff)
sumToNeg C values zero = refl
sumToNeg C values (suc cutoff) =
  trans
    (cong
      (λ rest → add C (negate C (values (suc cutoff))) rest)
      (sumToNeg C values cutoff))
    (sym
      (negateAdd C
        (values (suc cutoff))
        (sumTo C values cutoff)))

rectangleSumNeg : ∀ {s} (C : OrderedRationalEnvelopeCarrier {s})
    kernel lowCutoff gapCutoff →
  rectangleSum C
    (λ low gap → negate C (kernel low gap))
    lowCutoff gapCutoff
  ≡ negate C (rectangleSum C kernel lowCutoff gapCutoff)
rectangleSumNeg C kernel lowCutoff gapCutoff =
  trans
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

record EmbeddedOutputRelocationShellBridge {s : Level}
    (C : OrderedRationalEnvelopeCarrier {s}) : Set (lsuc s) where
  field
    lowFactor gapFactor : Nat → Scalar C
    signedCoefficient : Nat → Nat → Scalar C

    lowFactorNonnegative : ∀ lowShell →
      leq C (zero C) (lowFactor lowShell)
    gapFactorNonnegative : ∀ gap →
      leq C (zero C) (gapFactor gap)

    lowShellDominatedByQuarter : ∀ lowShell →
      leq C
        (lowFactor lowShell)
        (rationalEmbed C (Geo.pow Geo.quarter lowShell))
    gapDominatedByThirtySecond : ∀ gap →
      leq C
        (gapFactor gap)
        (rationalEmbed C (Geo.pow Geo.thirtySecond gap))

    signedCoefficientUpper : ∀ lowShell gap →
      leq C
        (signedCoefficient lowShell gap)
        (multiply C (lowFactor lowShell) (gapFactor gap))
    signedCoefficientLower : ∀ lowShell gap →
      leq C
        (negate C (multiply C (lowFactor lowShell) (gapFactor gap)))
        (signedCoefficient lowShell gap)

open EmbeddedOutputRelocationShellBridge public

embeddedRationalNonnegative : ∀ {s}
    (C : OrderedRationalEnvelopeCarrier {s}) value →
  0ℚ ≤ value →
  leq C (zero C) (rationalEmbed C value)
embeddedRationalNonnegative C value valueNonnegative =
  subst
    (λ lower → leq C lower (rationalEmbed C value))
    (embedZero C)
    (embedOrder C valueNonnegative)

bridgeMajorant : ∀ {s} {C : OrderedRationalEnvelopeCarrier {s}} →
  EmbeddedOutputRelocationShellBridge C → Nat → Nat → Scalar C
bridgeMajorant {C = C} bridge lowShell gap =
  multiply C (lowFactor bridge lowShell) (gapFactor bridge gap)

bridgeMajorantDominatedByCanonical : ∀ {s}
    {C : OrderedRationalEnvelopeCarrier {s}}
    (bridge : EmbeddedOutputRelocationShellBridge C) lowShell gap →
  leq C
    (bridgeMajorant bridge lowShell gap)
    (rationalEmbed C (RationalMajorant.canonicalKernel lowShell gap))
bridgeMajorantDominatedByCanonical {C = C} bridge lowShell gap =
  let
    productBound =
      multiplyMonotoneNonnegative C
        (lowFactorNonnegative bridge lowShell)
        (lowShellDominatedByQuarter bridge lowShell)
        (gapFactorNonnegative bridge gap)
        (gapDominatedByThirtySecond bridge gap)

    embeddedProduct =
      embedMultiply C
        (Geo.pow Geo.quarter lowShell)
        (Geo.pow Geo.thirtySecond gap)
  in
  subst
    (λ upper → leq C (bridgeMajorant bridge lowShell gap) upper)
    (sym embeddedProduct)
    productBound

bridgeMajorantCutoffBound : ∀ {s}
    {C : OrderedRationalEnvelopeCarrier {s}}
    (bridge : EmbeddedOutputRelocationShellBridge C)
    lowCutoff gapCutoff →
  leq C
    (rectangleSum C (bridgeMajorant bridge) lowCutoff gapCutoff)
    (rationalEmbed C Geo.oneTwentyEightNinetyThirds)
bridgeMajorantCutoffBound {C = C} bridge lowCutoff gapCutoff =
  leqTransitive C
    (rectangleSumMonotone C
      (bridgeMajorant bridge)
      (λ low gap →
        rationalEmbed C (RationalMajorant.canonicalKernel low gap))
      lowCutoff gapCutoff
      (bridgeMajorantDominatedByCanonical bridge))
    (embeddedCanonicalCutoffBound C lowCutoff gapCutoff)

signedCoefficientUpperCanonical : ∀ {s}
    {C : OrderedRationalEnvelopeCarrier {s}}
    (bridge : EmbeddedOutputRelocationShellBridge C) lowShell gap →
  leq C
    (signedCoefficient bridge lowShell gap)
    (rationalEmbed C (RationalMajorant.canonicalKernel lowShell gap))
signedCoefficientUpperCanonical {C = C} bridge lowShell gap =
  leqTransitive C
    (signedCoefficientUpper bridge lowShell gap)
    (bridgeMajorantDominatedByCanonical bridge lowShell gap)

signedCoefficientLowerCanonical : ∀ {s}
    {C : OrderedRationalEnvelopeCarrier {s}}
    (bridge : EmbeddedOutputRelocationShellBridge C) lowShell gap →
  leq C
    (negate C
      (rationalEmbed C (RationalMajorant.canonicalKernel lowShell gap)))
    (signedCoefficient bridge lowShell gap)
signedCoefficientLowerCanonical {C = C} bridge lowShell gap =
  leqTransitive C
    (negateAntitone C
      (bridgeMajorantDominatedByCanonical bridge lowShell gap))
    (signedCoefficientLower bridge lowShell gap)

embeddedSignedUpperBound : ∀ {s}
    {C : OrderedRationalEnvelopeCarrier {s}}
    (bridge : EmbeddedOutputRelocationShellBridge C)
    lowCutoff gapCutoff →
  leq C
    (rectangleSum C (signedCoefficient bridge) lowCutoff gapCutoff)
    (rationalEmbed C Geo.oneTwentyEightNinetyThirds)
embeddedSignedUpperBound {C = C} bridge lowCutoff gapCutoff =
  leqTransitive C
    (rectangleSumMonotone C
      (signedCoefficient bridge)
      (λ low gap →
        rationalEmbed C (RationalMajorant.canonicalKernel low gap))
      lowCutoff gapCutoff
      (signedCoefficientUpperCanonical bridge))
    (embeddedCanonicalCutoffBound C lowCutoff gapCutoff)

embeddedSignedLowerBound : ∀ {s}
    {C : OrderedRationalEnvelopeCarrier {s}}
    (bridge : EmbeddedOutputRelocationShellBridge C)
    lowCutoff gapCutoff →
  leq C
    (negate C (rationalEmbed C Geo.oneTwentyEightNinetyThirds))
    (rectangleSum C (signedCoefficient bridge) lowCutoff gapCutoff)
embeddedSignedLowerBound {C = C} bridge lowCutoff gapCutoff =
  let
    pointwiseLower =
      rectangleSumMonotone C
        (λ low gap →
          negate C
            (rationalEmbed C
              (RationalMajorant.canonicalKernel low gap)))
        (signedCoefficient bridge)
        lowCutoff gapCutoff
        (signedCoefficientLowerCanonical bridge)

    normalizedLower :
      leq C
        (negate C
          (rectangleSum C
            (λ low gap →
              rationalEmbed C
                (RationalMajorant.canonicalKernel low gap))
            lowCutoff gapCutoff))
        (rectangleSum C (signedCoefficient bridge) lowCutoff gapCutoff)
    normalizedLower =
      subst
        (λ lower →
          leq C lower
            (rectangleSum C (signedCoefficient bridge)
              lowCutoff gapCutoff))
        (rectangleSumNeg C
          (λ low gap →
            rationalEmbed C
              (RationalMajorant.canonicalKernel low gap))
          lowCutoff gapCutoff)
        pointwiseLower

    negatedUniformBound =
      negateAntitone C
        (embeddedCanonicalCutoffBound C lowCutoff gapCutoff)
  in
  leqTransitive C negatedUniformBound normalizedLower

record EmbeddedConditionalArchetypeTheorem {s : Level}
    (C : OrderedRationalEnvelopeCarrier {s})
    (bridge : EmbeddedOutputRelocationShellBridge C) : Set (lsuc s) where
  constructor theorem
  field
    outputCondition : ∀ lowCutoff gapCutoff →
      leq C
        (rectangleSum C (bridgeMajorant bridge) lowCutoff gapCutoff)
        (rationalEmbed C Geo.oneTwentyEightNinetyThirds)
    firstAdjointCondition : ∀ lowCutoff gapCutoff →
      leq C
        (rectangleSum C (bridgeMajorant bridge) lowCutoff gapCutoff)
        (rationalEmbed C Geo.oneTwentyEightNinetyThirds)
    secondAdjointCondition : ∀ lowCutoff gapCutoff →
      leq C
        (rectangleSum C (bridgeMajorant bridge) lowCutoff gapCutoff)
        (rationalEmbed C Geo.oneTwentyEightNinetyThirds)
    signedUpper : ∀ lowCutoff gapCutoff →
      leq C
        (rectangleSum C (signedCoefficient bridge) lowCutoff gapCutoff)
        (rationalEmbed C Geo.oneTwentyEightNinetyThirds)
    signedLower : ∀ lowCutoff gapCutoff →
      leq C
        (negate C (rationalEmbed C Geo.oneTwentyEightNinetyThirds))
        (rectangleSum C (signedCoefficient bridge) lowCutoff gapCutoff)

open EmbeddedConditionalArchetypeTheorem public

embeddedConditionalArchetypeTheorem : ∀ {s}
    (C : OrderedRationalEnvelopeCarrier {s})
    (bridge : EmbeddedOutputRelocationShellBridge C) →
  EmbeddedConditionalArchetypeTheorem C bridge
embeddedConditionalArchetypeTheorem C bridge = theorem
  (bridgeMajorantCutoffBound bridge)
  (bridgeMajorantCutoffBound bridge)
  (bridgeMajorantCutoffBound bridge)
  (embeddedSignedUpperBound bridge)
  (embeddedSignedLowerBound bridge)

orderedRationalEmbeddingClosureTheoremClosed : Bool
orderedRationalEmbeddingClosureTheoremClosed = true

allDownstreamOfEmbeddedShellBridgeClosed : Bool
allDownstreamOfEmbeddedShellBridgeClosed = true

concreteOrderedCarrierAdapterClosed : Bool
concreteOrderedCarrierAdapterClosed = false

concreteEmbeddedShellBridgeClosed : Bool
concreteEmbeddedShellBridgeClosed = false

orderedRationalEmbeddingClosureTheoremClosedIsTrue :
  orderedRationalEmbeddingClosureTheoremClosed ≡ true
orderedRationalEmbeddingClosureTheoremClosedIsTrue = refl

allDownstreamOfEmbeddedShellBridgeClosedIsTrue :
  allDownstreamOfEmbeddedShellBridgeClosed ≡ true
allDownstreamOfEmbeddedShellBridgeClosedIsTrue = refl

concreteOrderedCarrierAdapterClosedIsFalse :
  concreteOrderedCarrierAdapterClosed ≡ false
concreteOrderedCarrierAdapterClosedIsFalse = refl

concreteEmbeddedShellBridgeClosedIsFalse :
  concreteEmbeddedShellBridgeClosed ≡ false
concreteEmbeddedShellBridgeClosedIsFalse = refl

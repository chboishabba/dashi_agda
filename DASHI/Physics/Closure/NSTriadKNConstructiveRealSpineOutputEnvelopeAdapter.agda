module DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputEnvelopeAdapter where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Loukas Grafakos;
-- Rodolfo H. Torres; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; "A Multilinear Schur Test and Multiplier Operators"; and
-- "Native ConstructiveRealSpine adapter for the output-relocation envelope".
-- Venue/year: Springer, 1985; arXiv, 2022; Journal of Functional Analysis 187
-- (2001), 1--24; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- 10.1006/jfan.2001.3804; the repository adapter has no DOI.
-- Uses: DASHI.Analysis.ConstructiveRealSpine as the native carrier boundary,
-- the exact rational embedding/order laws absent from that intentionally small
-- spine, and the embedded 128/93 output-relocation closure theorem.
-- Relationship: no parallel real-number carrier is introduced.  Given one
-- native constructed real, its rational embedding/order capability, and the
-- three concrete shell-bridge facts, this module constructs the complete
-- cutoff-uniform output-relocation theorem.  Concrete capability inhabitants
-- remain fail-closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)

import DASHI.Analysis.ConstructiveRealSpine as Spine
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationEmbeddedEnvelopeClosure as Embedded

record ConstructiveRealSpineEnvelopeCapability
    (R : Spine.ConstructedOrderedCompleteReal) : Set₁ where
  field
    rationalEmbed : ℚ → Spine.Real R

    leqReflexive : ∀ value → Spine._≤_ R value value
    leqTransitive : ∀ {a b c} →
      Spine._≤_ R a b → Spine._≤_ R b c → Spine._≤_ R a c
    addMonotone : ∀ {a b c d} →
      Spine._≤_ R a b → Spine._≤_ R c d →
      Spine._≤_ R (Spine._+_ R a c) (Spine._+_ R b d)
    multiplyMonotoneNonnegative : ∀ {a b c d} →
      Spine._≤_ R (Spine.zero R) a →
      Spine._≤_ R a b →
      Spine._≤_ R (Spine.zero R) c →
      Spine._≤_ R c d →
      Spine._≤_ R (Spine._*_ R a c) (Spine._*_ R b d)
    negateAntitone : ∀ {a b} →
      Spine._≤_ R a b → Spine._≤_ R (Spine.neg R b) (Spine.neg R a)
    negateAdd : ∀ a b →
      Spine.neg R (Spine._+_ R a b)
      ≡ Spine._+_ R (Spine.neg R a) (Spine.neg R b)

    embedZero : rationalEmbed 0ℚ ≡ Spine.zero R
    embedAdd : ∀ left right →
      rationalEmbed (left + right)
      ≡ Spine._+_ R (rationalEmbed left) (rationalEmbed right)
    embedMultiply : ∀ left right →
      rationalEmbed (left * right)
      ≡ Spine._*_ R (rationalEmbed left) (rationalEmbed right)
    embedOrder : ∀ {left right} →
      left ≤ right → Spine._≤_ R (rationalEmbed left) (rationalEmbed right)

open ConstructiveRealSpineEnvelopeCapability public

asOrderedRationalEnvelopeCarrier : ∀ R →
  ConstructiveRealSpineEnvelopeCapability R →
  Embedded.OrderedRationalEnvelopeCarrier
asOrderedRationalEnvelopeCarrier R capability = record
  { Scalar = Spine.Real R
  ; zero = Spine.zero R
  ; add = Spine._+_ R
  ; multiply = Spine._*_ R
  ; negate = Spine.neg R
  ; leq = Spine._≤_ R
  ; rationalEmbed = rationalEmbed capability
  ; leqReflexive = leqReflexive capability
  ; leqTransitive = leqTransitive capability
  ; addMonotone = addMonotone capability
  ; multiplyMonotoneNonnegative =
      multiplyMonotoneNonnegative capability
  ; negateAntitone = negateAntitone capability
  ; negateAdd = negateAdd capability
  ; embedZero = embedZero capability
  ; embedAdd = embedAdd capability
  ; embedMultiply = embedMultiply capability
  ; embedOrder = embedOrder capability
  }

record ConstructiveRealSpineOutputShellData
    (R : Spine.ConstructedOrderedCompleteReal)
    (capability : ConstructiveRealSpineEnvelopeCapability R) : Set₁ where
  field
    lowFactor gapFactor : Nat → Spine.Real R
    signedCoefficient : Nat → Nat → Spine.Real R

    lowFactorNonnegative : ∀ lowShell →
      Spine._≤_ R (Spine.zero R) (lowFactor lowShell)
    gapFactorNonnegative : ∀ gap →
      Spine._≤_ R (Spine.zero R) (gapFactor gap)

    lowShellDominatedByQuarter : ∀ lowShell →
      Spine._≤_ R
        (lowFactor lowShell)
        (rationalEmbed capability (Geo.pow Geo.quarter lowShell))
    gapDominatedByThirtySecond : ∀ gap →
      Spine._≤_ R
        (gapFactor gap)
        (rationalEmbed capability (Geo.pow Geo.thirtySecond gap))

    signedCoefficientUpper : ∀ lowShell gap →
      Spine._≤_ R
        (signedCoefficient lowShell gap)
        (Spine._*_ R (lowFactor lowShell) (gapFactor gap))
    signedCoefficientLower : ∀ lowShell gap →
      Spine._≤_ R
        (Spine.neg R
          (Spine._*_ R (lowFactor lowShell) (gapFactor gap)))
        (signedCoefficient lowShell gap)

open ConstructiveRealSpineOutputShellData public

asEmbeddedOutputRelocationShellBridge : ∀ R capability →
  ConstructiveRealSpineOutputShellData R capability →
  Embedded.EmbeddedOutputRelocationShellBridge
    (asOrderedRationalEnvelopeCarrier R capability)
asEmbeddedOutputRelocationShellBridge R capability data = record
  { lowFactor = lowFactor data
  ; gapFactor = gapFactor data
  ; signedCoefficient = signedCoefficient data
  ; lowFactorNonnegative = lowFactorNonnegative data
  ; gapFactorNonnegative = gapFactorNonnegative data
  ; lowShellDominatedByQuarter = lowShellDominatedByQuarter data
  ; gapDominatedByThirtySecond = gapDominatedByThirtySecond data
  ; signedCoefficientUpper = signedCoefficientUpper data
  ; signedCoefficientLower = signedCoefficientLower data
  }

constructiveRealSpineOutputRelocationTheorem : ∀ R capability
    (data : ConstructiveRealSpineOutputShellData R capability) →
  Embedded.EmbeddedConditionalArchetypeTheorem
    (asOrderedRationalEnvelopeCarrier R capability)
    (asEmbeddedOutputRelocationShellBridge R capability data)
constructiveRealSpineOutputRelocationTheorem R capability data =
  Embedded.embeddedConditionalArchetypeTheorem
    (asOrderedRationalEnvelopeCarrier R capability)
    (asEmbeddedOutputRelocationShellBridge R capability data)

nativeConstructiveRealSpineAdapterSpecified : Bool
nativeConstructiveRealSpineAdapterSpecified = true

nativeSpineToEmbeddedClosureTheoremClosed : Bool
nativeSpineToEmbeddedClosureTheoremClosed = true

concreteSpineEnvelopeCapabilityClosed : Bool
concreteSpineEnvelopeCapabilityClosed = false

concreteSpineOutputShellDataClosed : Bool
concreteSpineOutputShellDataClosed = false

nativeConstructiveRealSpineAdapterSpecifiedIsTrue :
  nativeConstructiveRealSpineAdapterSpecified ≡ true
nativeConstructiveRealSpineAdapterSpecifiedIsTrue = refl

nativeSpineToEmbeddedClosureTheoremClosedIsTrue :
  nativeSpineToEmbeddedClosureTheoremClosed ≡ true
nativeSpineToEmbeddedClosureTheoremClosedIsTrue = refl

concreteSpineEnvelopeCapabilityClosedIsFalse :
  concreteSpineEnvelopeCapabilityClosed ≡ false
concreteSpineEnvelopeCapabilityClosedIsFalse = refl

concreteSpineOutputShellDataClosedIsFalse :
  concreteSpineOutputShellDataClosed ≡ false
concreteSpineOutputShellDataClosedIsFalse = refl

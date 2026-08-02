module DASHI.Physics.Closure.NSTriadKNOutputRelocationSquaredToAbsoluteBridge where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz; Loukas Grafakos;
-- Seungly Oh; DASHI repository contributors.
-- Title: "The Kato-Ponce Inequality" and "Ordered square cancellation for the
-- output-relocation coefficient majorant".
-- Venue/year: Communications in Partial Differential Equations 39 (2014),
-- 1128--1157; DASHI formal development, 2026.
-- DOI: 10.1080/03605302.2013.822885; the repository order theorem has no DOI.
-- Uses: the exact finite squared coefficient estimate, nonnegativity of the
-- absolute value and shell factors, monotonicity of multiplication on the
-- nonnegative cone, 0*0=0, and reflection of order by squaring there.
-- Relationship: replaces the formerly primitive absolute-coefficient estimate
-- by a squared estimate of the form naturally emitted by finite
-- Cauchy--Schwarz/Bernstein.  A concrete constructive-real carrier must still
-- supply the standard nonnegative square-order reflection law.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationEmbeddedEnvelopeClosure as Embedded
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAbsoluteCoefficientBridge as Absolute

square : ∀ {s} {C : Embedded.OrderedRationalEnvelopeCarrier {s}} →
  Embedded.Scalar C → Embedded.Scalar C
square {C = C} value = Embedded.multiply C value value

record NonnegativeSquareOrderCapability {s : Level}
    (C : Embedded.OrderedRationalEnvelopeCarrier {s})
    (absoluteOrder : Absolute.AbsoluteValueOrderCapability C) : Set (lsuc s) where
  field
    multiplyZeroZero :
      Embedded.multiply C (Embedded.zero C) (Embedded.zero C)
      ≡ Embedded.zero C
    absoluteNonnegative : ∀ value →
      Embedded.leq C (Embedded.zero C)
        (Absolute.absolute absoluteOrder value)
    squareReflectsOrderOnNonnegative : ∀ {left right} →
      Embedded.leq C (Embedded.zero C) left →
      Embedded.leq C (Embedded.zero C) right →
      Embedded.leq C (square left) (square right) →
      Embedded.leq C left right

open NonnegativeSquareOrderCapability public

record SquaredCoefficientFactorMajorant {s : Level}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    (absoluteOrder : Absolute.AbsoluteValueOrderCapability C) : Set (lsuc s) where
  field
    signedCoefficient : Nat → Nat → Embedded.Scalar C
    lowFactor gapFactor : Nat → Embedded.Scalar C
    lowFactorNonnegative : ∀ lowShell →
      Embedded.leq C (Embedded.zero C) (lowFactor lowShell)
    gapFactorNonnegative : ∀ gap →
      Embedded.leq C (Embedded.zero C) (gapFactor gap)
    squaredCoefficientDominatedBySquaredFactors : ∀ lowShell gap →
      Embedded.leq C
        (square (Absolute.absolute absoluteOrder
          (signedCoefficient lowShell gap)))
        (square (Embedded.multiply C
          (lowFactor lowShell) (gapFactor gap)))

open SquaredCoefficientFactorMajorant public

factorProductNonnegative : ∀ {s}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    {absoluteOrder : Absolute.AbsoluteValueOrderCapability C}
    (squareOrder : NonnegativeSquareOrderCapability C absoluteOrder)
    (majorant : SquaredCoefficientFactorMajorant absoluteOrder)
    lowShell gap →
  Embedded.leq C (Embedded.zero C)
    (Embedded.multiply C
      (lowFactor majorant lowShell)
      (gapFactor majorant gap))
factorProductNonnegative {C = C} squareOrder majorant lowShell gap =
  subst
    (λ lower →
      Embedded.leq C lower
        (Embedded.multiply C
          (lowFactor majorant lowShell)
          (gapFactor majorant gap)))
    (multiplyZeroZero squareOrder)
    (Embedded.multiplyMonotoneNonnegative C
      (Embedded.leqReflexive C (Embedded.zero C))
      (lowFactorNonnegative majorant lowShell)
      (Embedded.leqReflexive C (Embedded.zero C))
      (gapFactorNonnegative majorant gap))

absoluteCoefficientDominatedByFactors : ∀ {s}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    {absoluteOrder : Absolute.AbsoluteValueOrderCapability C}
    (squareOrder : NonnegativeSquareOrderCapability C absoluteOrder)
    (majorant : SquaredCoefficientFactorMajorant absoluteOrder)
    lowShell gap →
  Embedded.leq C
    (Absolute.absolute absoluteOrder
      (signedCoefficient majorant lowShell gap))
    (Embedded.multiply C
      (lowFactor majorant lowShell)
      (gapFactor majorant gap))
absoluteCoefficientDominatedByFactors {C = C} {absoluteOrder}
    squareOrder majorant lowShell gap =
  squareReflectsOrderOnNonnegative squareOrder
    (absoluteNonnegative squareOrder
      (signedCoefficient majorant lowShell gap))
    (factorProductNonnegative squareOrder majorant lowShell gap)
    (squaredCoefficientDominatedBySquaredFactors majorant lowShell gap)

asAbsoluteCoefficientFactorMajorant : ∀ {s}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    {absoluteOrder : Absolute.AbsoluteValueOrderCapability C} →
  NonnegativeSquareOrderCapability C absoluteOrder →
  SquaredCoefficientFactorMajorant absoluteOrder →
  Absolute.AbsoluteCoefficientFactorMajorant absoluteOrder
asAbsoluteCoefficientFactorMajorant squareOrder majorant = record
  { signedCoefficient = signedCoefficient majorant
  ; lowFactor = lowFactor majorant
  ; gapFactor = gapFactor majorant
  ; absoluteCoefficientDominatedByFactors =
      absoluteCoefficientDominatedByFactors squareOrder majorant
  }

squaredToAbsoluteCoefficientBridgeClosed : Bool
squaredToAbsoluteCoefficientBridgeClosed = true

factorProductNonnegativityDerivedCorrectly : Bool
factorProductNonnegativityDerivedCorrectly = true

concreteNonnegativeSquareOrderCapabilityClosed : Bool
concreteNonnegativeSquareOrderCapabilityClosed = false

squaredToAbsoluteCoefficientBridgeClosedIsTrue :
  squaredToAbsoluteCoefficientBridgeClosed ≡ true
squaredToAbsoluteCoefficientBridgeClosedIsTrue = refl

factorProductNonnegativityDerivedCorrectlyIsTrue :
  factorProductNonnegativityDerivedCorrectly ≡ true
factorProductNonnegativityDerivedCorrectlyIsTrue = refl

concreteNonnegativeSquareOrderCapabilityClosedIsFalse :
  concreteNonnegativeSquareOrderCapabilityClosed ≡ false
concreteNonnegativeSquareOrderCapabilityClosedIsFalse = refl

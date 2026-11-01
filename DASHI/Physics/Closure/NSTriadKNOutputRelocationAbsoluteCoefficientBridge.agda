module DASHI.Physics.Closure.NSTriadKNOutputRelocationAbsoluteCoefficientBridge where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz; Loukas Grafakos;
-- Rodolfo H. Torres; DASHI repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators" and
-- "Absolute-magnitude to two-sided coefficient domination for output
-- relocation".
-- Venue/year: Cauchy's finite-sum inequality, 1821; Schwarz's integral
-- inequality, 1888; Journal of Functional Analysis 187 (2001), 1--24; DASHI
-- formal development, 2026.
-- DOI: 10.1006/jfan.2001.3804; no DOI applies to the classical order lemma or
-- this repository-specialised formalisation.
-- Uses: the elementary order sandwich -|x| <= x <= |x|, antitonicity of
-- negation, and one absolute-coefficient majorant.
-- Relationship: signedCoefficientUpper and signedCoefficientLower are derived
-- theorem outputs.  A caller supplies only the literal coefficient's absolute
-- magnitude bound by the factorised positive shell kernel.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationEmbeddedEnvelopeClosure as Embedded

record AbsoluteValueOrderCapability {s : Level}
    (C : Embedded.OrderedRationalEnvelopeCarrier {s}) : Set (lsuc s) where
  field
    absolute : Embedded.Scalar C → Embedded.Scalar C
    valueBelowAbsolute : ∀ value →
      Embedded.leq C value (absolute value)
    negativeAbsoluteBelowValue : ∀ value →
      Embedded.leq C (Embedded.negate C (absolute value)) value

open AbsoluteValueOrderCapability public

record AbsoluteCoefficientFactorMajorant {s : Level}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    (absoluteOrder : AbsoluteValueOrderCapability C) : Set (lsuc s) where
  field
    signedCoefficient : Nat → Nat → Embedded.Scalar C
    lowFactor gapFactor : Nat → Embedded.Scalar C
    absoluteCoefficientDominatedByFactors : ∀ lowShell gap →
      Embedded.leq C
        (absolute absoluteOrder (signedCoefficient lowShell gap))
        (Embedded.multiply C (lowFactor lowShell) (gapFactor gap))

open AbsoluteCoefficientFactorMajorant public

signedCoefficientUpper : ∀ {s}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    {absoluteOrder : AbsoluteValueOrderCapability C}
    (majorant : AbsoluteCoefficientFactorMajorant absoluteOrder)
    lowShell gap →
  Embedded.leq C
    (signedCoefficient majorant lowShell gap)
    (Embedded.multiply C
      (lowFactor majorant lowShell)
      (gapFactor majorant gap))
signedCoefficientUpper {C = C} {absoluteOrder} majorant lowShell gap =
  Embedded.leqTransitive C
    (valueBelowAbsolute absoluteOrder
      (signedCoefficient majorant lowShell gap))
    (absoluteCoefficientDominatedByFactors majorant lowShell gap)

signedCoefficientLower : ∀ {s}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    {absoluteOrder : AbsoluteValueOrderCapability C}
    (majorant : AbsoluteCoefficientFactorMajorant absoluteOrder)
    lowShell gap →
  Embedded.leq C
    (Embedded.negate C
      (Embedded.multiply C
        (lowFactor majorant lowShell)
        (gapFactor majorant gap)))
    (signedCoefficient majorant lowShell gap)
signedCoefficientLower {C = C} {absoluteOrder} majorant lowShell gap =
  Embedded.leqTransitive C
    (Embedded.negateAntitone C
      (absoluteCoefficientDominatedByFactors majorant lowShell gap))
    (negativeAbsoluteBelowValue absoluteOrder
      (signedCoefficient majorant lowShell gap))

record AbsoluteOutputRelocationShellData {s : Level}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    (absoluteOrder : AbsoluteValueOrderCapability C) : Set (lsuc s) where
  field
    lowFactor gapFactor : Nat → Embedded.Scalar C
    signedCoefficient : Nat → Nat → Embedded.Scalar C

    lowFactorNonnegative : ∀ lowShell →
      Embedded.leq C (Embedded.zero C) (lowFactor lowShell)
    gapFactorNonnegative : ∀ gap →
      Embedded.leq C (Embedded.zero C) (gapFactor gap)

    lowShellDominatedByQuarter : ∀ lowShell →
      Embedded.leq C
        (lowFactor lowShell)
        (Embedded.rationalEmbed C (Geo.pow Geo.quarter lowShell))
    gapDominatedByThirtySecond : ∀ gap →
      Embedded.leq C
        (gapFactor gap)
        (Embedded.rationalEmbed C (Geo.pow Geo.thirtySecond gap))

    absoluteCoefficientDominatedByFactors : ∀ lowShell gap →
      Embedded.leq C
        (absolute absoluteOrder (signedCoefficient lowShell gap))
        (Embedded.multiply C (lowFactor lowShell) (gapFactor gap))

open AbsoluteOutputRelocationShellData public

asAbsoluteCoefficientFactorMajorant : ∀ {s}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    (absoluteOrder : AbsoluteValueOrderCapability C) →
    AbsoluteOutputRelocationShellData absoluteOrder →
    AbsoluteCoefficientFactorMajorant absoluteOrder
asAbsoluteCoefficientFactorMajorant absoluteOrder data = record
  { signedCoefficient = signedCoefficient data
  ; lowFactor = lowFactor data
  ; gapFactor = gapFactor data
  ; absoluteCoefficientDominatedByFactors =
      absoluteCoefficientDominatedByFactors data
  }

asEmbeddedOutputRelocationShellBridge : ∀ {s}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    (absoluteOrder : AbsoluteValueOrderCapability C) →
    (data : AbsoluteOutputRelocationShellData absoluteOrder) →
  Embedded.EmbeddedOutputRelocationShellBridge C
asEmbeddedOutputRelocationShellBridge absoluteOrder data = record
  { lowFactor = lowFactor data
  ; gapFactor = gapFactor data
  ; signedCoefficient = signedCoefficient data
  ; lowFactorNonnegative = lowFactorNonnegative data
  ; gapFactorNonnegative = gapFactorNonnegative data
  ; lowShellDominatedByQuarter = lowShellDominatedByQuarter data
  ; gapDominatedByThirtySecond = gapDominatedByThirtySecond data
  ; signedCoefficientUpper =
      signedCoefficientUpper
        (asAbsoluteCoefficientFactorMajorant absoluteOrder data)
  ; signedCoefficientLower =
      signedCoefficientLower
        (asAbsoluteCoefficientFactorMajorant absoluteOrder data)
  }

absoluteMagnitudeToTwoSidedDominationClosed : Bool
absoluteMagnitudeToTwoSidedDominationClosed = true

signedUpperAndLowerAreDerived : Bool
signedUpperAndLowerAreDerived = true

concreteAbsoluteCoefficientMajorantClosed : Bool
concreteAbsoluteCoefficientMajorantClosed = false

absoluteMagnitudeToTwoSidedDominationClosedIsTrue :
  absoluteMagnitudeToTwoSidedDominationClosed ≡ true
absoluteMagnitudeToTwoSidedDominationClosedIsTrue = refl

signedUpperAndLowerAreDerivedIsTrue :
  signedUpperAndLowerAreDerived ≡ true
signedUpperAndLowerAreDerivedIsTrue = refl

concreteAbsoluteCoefficientMajorantClosedIsFalse :
  concreteAbsoluteCoefficientMajorantClosed ≡ false
concreteAbsoluteCoefficientMajorantClosedIsFalse = refl

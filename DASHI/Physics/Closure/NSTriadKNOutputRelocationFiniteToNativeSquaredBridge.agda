module DASHI.Physics.Closure.NSTriadKNOutputRelocationFiniteToNativeSquaredBridge where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz; Sergei
-- Bernstein; Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael
-- Danchin; Loukas Grafakos; Seungly Oh; DASHI repository contributors.
-- Title: "The Kato-Ponce Inequality"; "Fourier Analysis and Nonlinear
-- Partial Differential Equations"; and "Finite-to-native squared
-- output-relocation coefficient bridge".
-- Venue/year: Communications in Partial Differential Equations 39 (2014),
-- 1128--1157; Springer, 2011; DASHI formal development, 2026.
-- DOI: 10.1080/03605302.2013.822885;
-- 10.1007/978-3-642-16830-7; the repository bridge has no DOI.
-- Uses: the exact rational finite-shell squared coefficient theorem and the
-- ordered rational embedding already used by the 128/93 envelope closure.
-- Relationship: makes the literal representation seam explicit.  Once the
-- square of the native coefficient is identified with the embedded finite
-- fibre square and the square of the physical factor is identified with the
-- embedded shell-cardinality majorant, the native squared estimate is a
-- theorem rather than a fresh analytic assumption.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationEmbeddedEnvelopeClosure as Embedded
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAbsoluteCoefficientBridge as Absolute
import DASHI.Physics.Closure.NSTriadKNOutputRelocationSquaredToAbsoluteBridge as Squared
import DASHI.Physics.Closure.NSTriadKNOutputRelocationFiniteSquaredCoefficientMajorant as Finite
import DASHI.Physics.Closure.NSTriadKNRationalDirectConvolutionBound as Direct

record NativeFiniteSquaredCoefficientRealization {s : Level}
    (C : Embedded.OrderedRationalEnvelopeCarrier {s})
    (absoluteOrder : Absolute.AbsoluteValueOrderCapability C) : Set (lsuc s) where
  field
    signedCoefficient : Nat → Nat → Embedded.Scalar C
    lowFactor gapFactor : Nat → Embedded.Scalar C
    lowFactorNonnegative : ∀ lowShell →
      Embedded.leq C (Embedded.zero C) (lowFactor lowShell)
    gapFactorNonnegative : ∀ gap →
      Embedded.leq C (Embedded.zero C) (gapFactor gap)

    finiteModel : Nat → Nat → Finite.FiniteOutputRelocationSquaredModel

    coefficientSquareMeaning : ∀ lowShell gap →
      Squared.square
        (Absolute.absolute absoluteOrder
          (signedCoefficient lowShell gap))
      ≡ Embedded.rationalEmbed C
          (Finite.unitOutputShellSquared
            (Finite.outputs (finiteModel lowShell gap)))

    factorSquareMeaning : ∀ lowShell gap →
      Embedded.rationalEmbed C
        (Direct.shellCardinalityFactor
          (Finite.cardinality (finiteModel lowShell gap)))
      ≡ Squared.square
          (Embedded.multiply C
            (lowFactor lowShell)
            (gapFactor gap))

open NativeFiniteSquaredCoefficientRealization public

nativeSquaredCoefficientBound : ∀ {s}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    {absoluteOrder : Absolute.AbsoluteValueOrderCapability C}
    (realization : NativeFiniteSquaredCoefficientRealization C absoluteOrder)
    lowShell gap →
  Embedded.leq C
    (Squared.square
      (Absolute.absolute absoluteOrder
        (signedCoefficient realization lowShell gap)))
    (Squared.square
      (Embedded.multiply C
        (lowFactor realization lowShell)
        (gapFactor realization gap)))
nativeSquaredCoefficientBound {C = C} {absoluteOrder}
    realization lowShell gap =
  let
    model = finiteModel realization lowShell gap

    embeddedFiniteBound =
      Embedded.embedOrder C (Finite.finiteModelSquaredBound model)

    upperRewritten =
      subst
        (λ upper →
          Embedded.leq C
            (Embedded.rationalEmbed C
              (Finite.unitOutputShellSquared (Finite.outputs model)))
            upper)
        (factorSquareMeaning realization lowShell gap)
        embeddedFiniteBound
  in
  subst
    (λ lower →
      Embedded.leq C lower
        (Squared.square
          (Embedded.multiply C
            (lowFactor realization lowShell)
            (gapFactor realization gap))))
    (sym (coefficientSquareMeaning realization lowShell gap))
    upperRewritten

asSquaredCoefficientFactorMajorant : ∀ {s}
    {C : Embedded.OrderedRationalEnvelopeCarrier {s}}
    {absoluteOrder : Absolute.AbsoluteValueOrderCapability C} →
  NativeFiniteSquaredCoefficientRealization C absoluteOrder →
  Squared.SquaredCoefficientFactorMajorant absoluteOrder
asSquaredCoefficientFactorMajorant realization = record
  { signedCoefficient = signedCoefficient realization
  ; lowFactor = lowFactor realization
  ; gapFactor = gapFactor realization
  ; lowFactorNonnegative = lowFactorNonnegative realization
  ; gapFactorNonnegative = gapFactorNonnegative realization
  ; squaredCoefficientDominatedBySquaredFactors =
      nativeSquaredCoefficientBound realization
  }

finiteToNativeSquaredBridgeClosed : Bool
finiteToNativeSquaredBridgeClosed = true

literalFiniteFibreRepresentationClosed : Bool
literalFiniteFibreRepresentationClosed = false

finiteToNativeSquaredBridgeClosedIsTrue :
  finiteToNativeSquaredBridgeClosed ≡ true
finiteToNativeSquaredBridgeClosedIsTrue = refl

literalFiniteFibreRepresentationClosedIsFalse :
  literalFiniteFibreRepresentationClosed ≡ false
literalFiniteFibreRepresentationClosedIsFalse = refl

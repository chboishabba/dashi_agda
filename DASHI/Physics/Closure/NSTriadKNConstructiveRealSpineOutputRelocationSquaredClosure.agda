module DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputRelocationSquaredClosure where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- Augustin-Louis Cauchy; Hermann Amandus Schwarz; Sergei Bernstein;
-- Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin;
-- Loukas Grafakos; Seungly Oh; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; "The Kato-Ponce Inequality"; "Fourier Analysis and Nonlinear
-- Partial Differential Equations"; and "Squared finite-fibre native closure
-- of the output-relocation shell theorem".
-- Venue/year: Springer, 1985 and 2011; arXiv, 2022; Communications in Partial
-- Differential Equations 39 (2014), 1128--1157; DASHI formal development,
-- 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- 10.1080/03605302.2013.822885; 10.1007/978-3-642-16830-7;
-- the repository composition theorem has no DOI.
-- Uses: the semantically pinned ConstructiveRealSpine output-relocation
-- package, the exact rational finite-shell square bound, finite-to-native
-- representation transport and nonnegative square-order cancellation.
-- Relationship: callers no longer provide the final absolute coefficient
-- estimate.  They provide the literal finite-fibre realization and the
-- standard ordered-square reflection law; the existing native 128/93 theorem
-- is then emitted automatically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.ConstructiveRealSpine as Spine
import DASHI.Physics.Closure.NSTriadKNOutputRelocationEmbeddedEnvelopeClosure as Embedded
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAbsoluteCoefficientBridge as Absolute
import DASHI.Physics.Closure.NSTriadKNOutputRelocationSquaredToAbsoluteBridge as Squared
import DASHI.Physics.Closure.NSTriadKNOutputRelocationFiniteSquaredCoefficientMajorant as Finite
import DASHI.Physics.Closure.NSTriadKNOutputRelocationFiniteToNativeSquaredBridge as FiniteNative
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPowerMonotonicityBridge as Power
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputEnvelopeAdapter as Adapter
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputRelocationDerivedClosure as Derived

record ConstructiveRealSpineSquareOrderCapability
    (R : Spine.ConstructedOrderedCompleteReal)
    (capability : Adapter.ConstructiveRealSpineEnvelopeCapability R)
    (absoluteOrder : Derived.ConstructiveRealSpineAbsoluteOrderCapability
      R capability) : Set₁ where
  field
    absoluteNonnegative : ∀ value →
      Spine._≤_ R (Spine.zero R) (Spine.abs R value)
    squareReflectsOrderOnNonnegative : ∀ {left right} →
      Spine._≤_ R (Spine.zero R) left →
      Spine._≤_ R (Spine.zero R) right →
      Spine._≤_ R
        (Spine._*_ R left left)
        (Spine._*_ R right right) →
      Spine._≤_ R left right

open ConstructiveRealSpineSquareOrderCapability public

asNonnegativeSquareOrderCapability : ∀ R capability absoluteOrder →
  ConstructiveRealSpineSquareOrderCapability R capability absoluteOrder →
  Squared.NonnegativeSquareOrderCapability
    (Adapter.asOrderedRationalEnvelopeCarrier R capability)
    (Derived.asAbsoluteValueOrderCapability R capability absoluteOrder)
asNonnegativeSquareOrderCapability R capability absoluteOrder squareOrder = record
  { absoluteNonnegative = absoluteNonnegative squareOrder
  ; squareReflectsOrderOnNonnegative =
      squareReflectsOrderOnNonnegative squareOrder
  }

record ConstructiveRealSpineFiniteSquaredCoefficientRealization
    (R : Spine.ConstructedOrderedCompleteReal)
    (capability : Adapter.ConstructiveRealSpineEnvelopeCapability R)
    (power : Derived.ConstructiveRealSpineBaseTwoPowerCapability R capability)
    (decay : Derived.ConstructiveRealSpineOutputDecayData R capability power)
    (absoluteOrder : Derived.ConstructiveRealSpineAbsoluteOrderCapability
      R capability) : Set₁ where
  field
    signedCoefficient : Nat → Nat → Spine.Real R
    finiteModel : Nat → Nat → Finite.FiniteOutputRelocationSquaredModel

    coefficientSquareMeaning : ∀ lowShell gap →
      Spine._*_ R
        (Spine.abs R (signedCoefficient lowShell gap))
        (Spine.abs R (signedCoefficient lowShell gap))
      ≡ Adapter.rationalEmbed capability
          (Finite.unitOutputShellSquared
            (Finite.outputs (finiteModel lowShell gap)))

    factorSquareMeaning : ∀ lowShell gap →
      Adapter.rationalEmbed capability
        (DASHI.Physics.Closure.NSTriadKNRationalDirectConvolutionBound.shellCardinalityFactor
          (Finite.cardinality (finiteModel lowShell gap)))
      ≡ Spine._*_ R
          (Spine._*_ R
            (Derived.spineLowFactor R capability power decay lowShell)
            (Derived.spineGapFactor R capability power decay gap))
          (Spine._*_ R
            (Derived.spineLowFactor R capability power decay lowShell)
            (Derived.spineGapFactor R capability power decay gap))

open ConstructiveRealSpineFiniteSquaredCoefficientRealization public

asNativeFiniteSquaredCoefficientRealization : ∀
    R capability power decay absoluteOrder →
  ConstructiveRealSpineFiniteSquaredCoefficientRealization
    R capability power decay absoluteOrder →
  FiniteNative.NativeFiniteSquaredCoefficientRealization
    (Adapter.asOrderedRationalEnvelopeCarrier R capability)
    (Derived.asAbsoluteValueOrderCapability R capability absoluteOrder)
asNativeFiniteSquaredCoefficientRealization
    R capability power decay absoluteOrder realization = record
  { signedCoefficient = signedCoefficient realization
  ; lowFactor = Derived.spineLowFactor R capability power decay
  ; gapFactor = Derived.spineGapFactor R capability power decay
  ; lowFactorNonnegative =
      Power.lowShellFactorNonnegative
        (Derived.asBaseTwoIntegerPowerAnchors R capability power)
        (Derived.asOutputRelocationDecayExponentData
          R capability power decay)
  ; gapFactorNonnegative =
      Power.gapShellFactorNonnegative
        (Derived.asBaseTwoIntegerPowerAnchors R capability power)
        (Derived.asOutputRelocationDecayExponentData
          R capability power decay)
  ; finiteModel = finiteModel realization
  ; coefficientSquareMeaning = coefficientSquareMeaning realization
  ; factorSquareMeaning = factorSquareMeaning realization
  }

asConstructiveRealSpineLiteralMagnitudeDataFromSquared : ∀
    R capability power decay absoluteOrder
    (squareOrder : ConstructiveRealSpineSquareOrderCapability
      R capability absoluteOrder) →
  ConstructiveRealSpineFiniteSquaredCoefficientRealization
    R capability power decay absoluteOrder →
  Derived.ConstructiveRealSpineLiteralMagnitudeData
    R capability power decay absoluteOrder
asConstructiveRealSpineLiteralMagnitudeDataFromSquared
    R capability power decay absoluteOrder squareOrder realization =
  let
    nativeRealization =
      asNativeFiniteSquaredCoefficientRealization
        R capability power decay absoluteOrder realization

    squaredMajorant =
      FiniteNative.asSquaredCoefficientFactorMajorant nativeRealization
  in
  record
    { signedCoefficient = signedCoefficient realization
    ; absoluteCoefficientDominatedByFactors =
        Squared.absoluteCoefficientDominatedByFactors
          (asNonnegativeSquareOrderCapability
            R capability absoluteOrder squareOrder)
          squaredMajorant
    }

constructiveRealSpineSquaredOutputRelocationTheorem : ∀
    R capability power decay absoluteOrder
    (squareOrder : ConstructiveRealSpineSquareOrderCapability
      R capability absoluteOrder)
    (realization : ConstructiveRealSpineFiniteSquaredCoefficientRealization
      R capability power decay absoluteOrder) →
  Embedded.EmbeddedConditionalArchetypeTheorem
    (Adapter.asOrderedRationalEnvelopeCarrier R capability)
    (Adapter.asEmbeddedOutputRelocationShellBridge
      R capability
      (Derived.asConstructiveRealSpineOutputShellData
        R capability power decay absoluteOrder
        (asConstructiveRealSpineLiteralMagnitudeDataFromSquared
          R capability power decay absoluteOrder squareOrder realization)))
constructiveRealSpineSquaredOutputRelocationTheorem
    R capability power decay absoluteOrder squareOrder realization =
  Derived.constructiveRealSpineDerivedOutputRelocationTheorem
    R capability power decay absoluteOrder
    (asConstructiveRealSpineLiteralMagnitudeDataFromSquared
      R capability power decay absoluteOrder squareOrder realization)

finiteSquaredCoefficientCoreClosed : Bool
finiteSquaredCoefficientCoreClosed = true

squaredToAbsoluteNativeClosureClosed : Bool
squaredToAbsoluteNativeClosureClosed = true

concreteLiteralFiniteFibreRealizationClosed : Bool
concreteLiteralFiniteFibreRealizationClosed = false

finiteSquaredCoefficientCoreClosedIsTrue :
  finiteSquaredCoefficientCoreClosed ≡ true
finiteSquaredCoefficientCoreClosedIsTrue = refl

squaredToAbsoluteNativeClosureClosedIsTrue :
  squaredToAbsoluteNativeClosureClosed ≡ true
squaredToAbsoluteNativeClosureClosedIsTrue = refl

concreteLiteralFiniteFibreRealizationClosedIsFalse :
  concreteLiteralFiniteFibreRealizationClosed ≡ false
concreteLiteralFiniteFibreRealizationClosedIsFalse = refl

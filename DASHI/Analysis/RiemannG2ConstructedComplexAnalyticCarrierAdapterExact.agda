module DASHI.Analysis.RiemannG2ConstructedComplexAnalyticCarrierAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannG2CanonicalCharacterHighestAlphaReconciliationExact as HXCut

------------------------------------------------------------------------
-- CONSTRUCTED COMPLEX -> RIEMANN ANALYTIC CARRIER ADAPTER
--
-- The ordinary constructed complex package already owns the concrete scalar
-- and pair carriers plus zero/one, addition, multiplication, conjugation and
-- real/imaginary projections.  ComplexAnalyticCarrier adds only the analytic
-- function/predicate layer.  Under the standing repo-complete assumption, do
-- not rediscover a second complex carrier: package the existing constructed
-- carrier with the already-owned function layer, then ask whether the exact
-- Riemann AnalyticSubstrate.carrier is this literal record.
--
-- This is deliberately weaker than constructing an AnalyticSubstrate: Gamma,
-- Mellin, zeta and xi remain whatever genuine objects the selected substrate
-- already owns.  It is only the carrier realization needed by H_X.
------------------------------------------------------------------------

record ConstructedComplexAnalyticFunctionLayer
    (C : Complex.ConstructedComplexPackage) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)
  field
    Function : Set
    apply : Function → Complex.ComplexPair R → Complex.ComplexPair R
    Holomorphic : Function → Set
    Entire : Function → Set
    Meromorphic : Function → Set
    SimplePoleAt : Function → Complex.ComplexPair R → Set

open ConstructedComplexAnalyticFunctionLayer public

constructedComplexAnalyticCarrier :
  (C : Complex.ConstructedComplexPackage) →
  ConstructedComplexAnalyticFunctionLayer C →
  Analytic.ComplexAnalyticCarrier
constructedComplexAnalyticCarrier C F =
  let R = Real.real (Complex.realPackage C)
  in record
    { Analytic.ComplexAnalyticCarrier.Complex = Complex.ComplexPair R
    ; Analytic.ComplexAnalyticCarrier.Real = Real.Real R
    ; Analytic.ComplexAnalyticCarrier.zeroC = Complex.zeroC
    ; Analytic.ComplexAnalyticCarrier.oneC = Complex.oneC
    ; Analytic.ComplexAnalyticCarrier._+C_ = Complex._+C_
    ; Analytic.ComplexAnalyticCarrier._*C_ = Complex._*C_
    ; Analytic.ComplexAnalyticCarrier.negC =
        λ z → Complex._-C_ Complex.zeroC z
    ; Analytic.ComplexAnalyticCarrier.conjC = Complex.conjugateC
    ; Analytic.ComplexAnalyticCarrier.realPart = Complex.re
    ; Analytic.ComplexAnalyticCarrier.imaginaryPart = Complex.im
    ; Analytic.ComplexAnalyticCarrier.Function = Function F
    ; Analytic.ComplexAnalyticCarrier.apply = apply F
    ; Analytic.ComplexAnalyticCarrier.Holomorphic = Holomorphic F
    ; Analytic.ComplexAnalyticCarrier.Entire = Entire F
    ; Analytic.ComplexAnalyticCarrier.Meromorphic = Meromorphic F
    ; Analytic.ComplexAnalyticCarrier.SimplePoleAt = SimplePoleAt F
    }

constructedCarrierRealIsDonor :
  (C : Complex.ConstructedComplexPackage) →
  (F : ConstructedComplexAnalyticFunctionLayer C) →
  Analytic.ComplexAnalyticCarrier.Real (constructedComplexAnalyticCarrier C F)
  ≡ Real.Real (Real.real (Complex.realPackage C))
constructedCarrierRealIsDonor C F = refl

constructedCarrierComplexIsDonor :
  (C : Complex.ConstructedComplexPackage) →
  (F : ConstructedComplexAnalyticFunctionLayer C) →
  Analytic.ComplexAnalyticCarrier.Complex (constructedComplexAnalyticCarrier C F)
  ≡ Complex.ComplexPair (Real.real (Complex.realPackage C))
constructedCarrierComplexIsDonor C F = refl

------------------------------------------------------------------------
-- One whole-record equality now generates the two carrier equalities required
-- by the #676 H_X cut.  This is strictly stronger than independently asserting
-- Real and Complex equality and prevents those coordinates from coming from
-- different analytic realizations.
------------------------------------------------------------------------

record CanonicalConstructedCarrierRealization
    (analytic : Analytic.AnalyticSubstrate)
    (C : Complex.ConstructedComplexPackage)
    (F : ConstructedComplexAnalyticFunctionLayer C) : Set₁ where
  field
    carrierIdentity :
      Analytic.AnalyticSubstrate.carrier analytic
      ≡ constructedComplexAnalyticCarrier C F
    realizationReference : String

open CanonicalConstructedCarrierRealization public

realCarrierIdentityFromWholeCarrier :
  ∀ {analytic C F} →
  CanonicalConstructedCarrierRealization analytic C F →
  Analytic.ComplexAnalyticCarrier.Real
    (Analytic.AnalyticSubstrate.carrier analytic)
  ≡ Real.Real (Real.real (Complex.realPackage C))
realCarrierIdentityFromWholeCarrier A =
  cong Analytic.ComplexAnalyticCarrier.Real (carrierIdentity A)

complexCarrierIdentityFromWholeCarrier :
  ∀ {analytic C F} →
  CanonicalConstructedCarrierRealization analytic C F →
  Analytic.ComplexAnalyticCarrier.Complex
    (Analytic.AnalyticSubstrate.carrier analytic)
  ≡ Complex.ComplexPair (Real.real (Complex.realPackage C))
complexCarrierIdentityFromWholeCarrier A =
  cong Analytic.ComplexAnalyticCarrier.Complex (carrierIdentity A)

toCanonicalCharacterCarrierAttachment :
  ∀ {analytic C F} →
  CanonicalConstructedCarrierRealization analytic C F →
  HXCut.CanonicalCharacterCarrierAttachment analytic
toCanonicalCharacterCarrierAttachment {C = C} A = record
  { HXCut.DonorReal = Real.Real (Real.real (Complex.realPackage C))
  ; HXCut.DonorComplex = Complex.ComplexPair (Real.real (Complex.realPackage C))
  ; HXCut.realCarrierIdentity = realCarrierIdentityFromWholeCarrier A
  ; HXCut.complexCarrierIdentity = complexCarrierIdentityFromWholeCarrier A
  ; HXCut.attachmentReference = realizationReference A
  }

------------------------------------------------------------------------
-- Search pruning.
------------------------------------------------------------------------

data CarrierAttachmentAction : Set where
  reuseTerminalOnePointAnalyticModel
  assertRealAndComplexNamesMatch
  recoverWholeCanonicalCarrierIdentity
  realizeCanonicalCharacterOperations
  continueToTestModulation
  : CarrierAttachmentAction

CarrierAttachmentRelevant : CarrierAttachmentAction → Set
CarrierAttachmentRelevant reuseTerminalOnePointAnalyticModel = ⊥
CarrierAttachmentRelevant assertRealAndComplexNamesMatch = ⊥
CarrierAttachmentRelevant recoverWholeCanonicalCarrierIdentity = ⊤
CarrierAttachmentRelevant realizeCanonicalCharacterOperations = ⊤
CarrierAttachmentRelevant continueToTestModulation = ⊤

terminalOnePointModelPruned :
  CarrierAttachmentRelevant reuseTerminalOnePointAnalyticModel → ⊥
terminalOnePointModelPruned x = x

nameOnlyCarrierMatchPruned :
  CarrierAttachmentRelevant assertRealAndComplexNamesMatch → ⊥
nameOnlyCarrierMatchPruned x = x

record ConstructedComplexAnalyticCarrierAdapterBoundary : Set where
  constructor constructed-complex-analytic-carrier-adapter-boundary
  field
    ordinaryComplexPairCarrierNeedsReconstruction : Bool
    ordinaryComplexPairCarrierNeedsReconstructionIsFalse :
      ordinaryComplexPairCarrierNeedsReconstruction ≡ false

    analyticFunctionLayerCanBeSeparatedFromComplexCarrierChoice : Bool
    analyticFunctionLayerCanBeSeparatedFromComplexCarrierChoiceIsTrue :
      analyticFunctionLayerCanBeSeparatedFromComplexCarrierChoice ≡ true

    wholeCarrierEqualityImpliesBothCarrierCoordinates : Bool
    wholeCarrierEqualityImpliesBothCarrierCoordinatesIsTrue :
      wholeCarrierEqualityImpliesBothCarrierCoordinates ≡ true

    terminalOnePointModelIsAcceptedAsCanonicalRiemannCarrier : Bool
    terminalOnePointModelIsAcceptedAsCanonicalRiemannCarrierIsFalse :
      terminalOnePointModelIsAcceptedAsCanonicalRiemannCarrier ≡ false

    wholeCarrierIdentityAloneClosesFullHX : Bool
    wholeCarrierIdentityAloneClosesFullHXIsFalse :
      wholeCarrierIdentityAloneClosesFullHX ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalConstructedComplexAnalyticCarrierAdapterBoundary :
  ConstructedComplexAnalyticCarrierAdapterBoundary
canonicalConstructedComplexAnalyticCarrierAdapterBoundary =
  constructed-complex-analytic-carrier-adapter-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Do not reconstruct ordinary complex numbers and do not promote the repository's one-point terminal analytic test model. Build the canonical ComplexAnalyticCarrier from the already-owned ConstructedComplexPackage plus the genuine analytic function layer. Then recover one equality between the selected Riemann AnalyticSubstrate.carrier and that literal carrier. This single same-object receipt generates both Real and Complex carrier identities. Operation/theorem realization for H_X remains a separate payment, after which the route continues immediately to canonical test modulation."

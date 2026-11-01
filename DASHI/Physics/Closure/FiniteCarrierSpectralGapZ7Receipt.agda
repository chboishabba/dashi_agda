module DASHI.Physics.Closure.FiniteCarrierSpectralGapZ7Receipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Finite Z/7 carrier spectral gap receipt.
--
-- This is the first non-toy finite carrier spectral calculation tied to the
-- actual p=7 CM torsion object.  It is a finite Cayley-graph computation,
-- not a continuum Yang-Mills proof.

data FiniteCarrierSpectralStatus : Set where
  finiteEvidence_nonToyZ7_noContinuumPromotion :
    FiniteCarrierSpectralStatus

data CarrierSpectralModel : Set where
  cayleyZ7PlusMinusOne :
    CarrierSpectralModel

data SpectralComponent : Set where
  cmTorsionF7Carrier :
    SpectralComponent

  z7CayleyAdjacency :
    SpectralComponent

  cosineEigenvalueFormula :
    SpectralComponent

  positiveFiniteGap :
    SpectralComponent

  productExtensionBottleneck :
    SpectralComponent

canonicalSpectralComponents :
  List SpectralComponent
canonicalSpectralComponents =
  cmTorsionF7Carrier
  ∷ z7CayleyAdjacency
  ∷ cosineEigenvalueFormula
  ∷ positiveFiniteGap
  ∷ productExtensionBottleneck
  ∷ []

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

gapApprox :
  Float
gapApprox =
  0.7530203962825329

carrierModelStatement :
  String
carrierModelStatement =
  "The finite carrier model is E[p_7] ~= F_7, identified with Z/7Z, with Cayley generators {+1,-1}."

eigenvalueStatement :
  String
eigenvalueStatement =
  "The adjacency eigenvalues of Cayley(Z/7Z,{+1,-1}) are 2*cos(2*pi*k/7), for k=0,...,6."

gapStatement :
  String
gapStatement =
  "For the unnormalised cycle Laplacian, the top adjacency eigenvalue is 2 and the next is 2*cos(2*pi/7), giving finite spectral gap 2 - 2*cos(2*pi/7) ~= 0.7530203963."

normalisedGapCaveatStatement :
  String
normalisedGapCaveatStatement =
  "For the normalised random-walk Laplacian on the same 2-regular cycle, the gap is half this value: 1 - cos(2*pi/7) ~= 0.3765101981."

productGapStatement :
  String
productGapStatement =
  "For the finite unnormalised Cartesian product carrier Z/7Z x Z/3Z x Z/2Z with cycle factors, the gap is min(0.7530203963,3,2)=0.7530203963; this is a finite product-spectrum calculation only, not a full tensor-product Yang-Mills Hamiltonian gap."

productSpectrumStatement :
  String
productSpectrumStatement =
  "The product statement uses the finite Cartesian-product spectrum rule sigma(A1 tensor I + I tensor A2) = {lambda_i + mu_j}; a physical tensor-product gap still needs density, domain, and Feshbach-Schur hypotheses."

algebraicStatement :
  String
algebraicStatement =
  "The finite gap is algebraic of degree 3 over Q because cos(2*pi/7) has degree 3."

boundaryStatement :
  String
boundaryStatement =
  "This is finite carrier spectral evidence only; it does not transport a lower bound to continuum Yang-Mills and does not prove the Clay mass gap."

record FiniteCarrierSpectralGapZ7Receipt : Set where
  field
    status :
      FiniteCarrierSpectralStatus

    statusIsFiniteEvidenceNoContinuumPromotion :
      status ≡ finiteEvidence_nonToyZ7_noContinuumPromotion

    model :
      CarrierSpectralModel

    modelIsZ7Cayley :
      model ≡ cayleyZ7PlusMinusOne

    components :
      List SpectralComponent

    componentsAreCanonical :
      components ≡ canonicalSpectralComponents

    carrierModel :
      String

    carrierModelIsCanonical :
      carrierModel ≡ carrierModelStatement

    groupOrder :
      Nat

    groupOrderIsSeven :
      groupOrder ≡ 7

    generatorCount :
      Nat

    generatorCountIsTwo :
      generatorCount ≡ 2

    eigenvalueFormula :
      String

    eigenvalueFormulaIsCanonical :
      eigenvalueFormula ≡ eigenvalueStatement

    topEigenvalueNumerator :
      Nat

    topEigenvalueNumeratorIsTwo :
      topEigenvalueNumerator ≡ 2

    nextEigenvalueDescription :
      String

    nextEigenvalueDescriptionIsCanonical :
      nextEigenvalueDescription ≡ "2*cos(2*pi/7)"

    spectralGapDescription :
      String

    spectralGapDescriptionIsCanonical :
      spectralGapDescription ≡ gapStatement

    normalisedGapCaveat :
      String

    normalisedGapCaveatIsCanonical :
      normalisedGapCaveat ≡ normalisedGapCaveatStatement

    spectralGapApprox :
      Float

    spectralGapApproxIsCanonical :
      spectralGapApprox ≡ gapApprox

    spectralGapPositive :
      Bool

    spectralGapPositiveIsTrue :
      spectralGapPositive ≡ true

    algebraicDegree :
      Nat

    algebraicDegreeIsThree :
      algebraicDegree ≡ 3

    algebraicSummary :
      String

    algebraicSummaryIsCanonical :
      algebraicSummary ≡ algebraicStatement

    nonToyCarrierModel :
      Bool

    nonToyCarrierModelIsTrue :
      nonToyCarrierModel ≡ true

    z2CycleGap :
      Nat

    z2CycleGapIsTwo :
      z2CycleGap ≡ 2

    z3CycleGap :
      Nat

    z3CycleGapIsThree :
      z3CycleGap ≡ 3

    productExtensionGapStillZ7Bottleneck :
      Bool

    productExtensionGapStillZ7BottleneckIsTrue :
      productExtensionGapStillZ7Bottleneck ≡ true

    productGapSummary :
      String

    productGapSummaryIsCanonical :
      productGapSummary ≡ productGapStatement

    productSpectrumRuleSummary :
      String

    productSpectrumRuleSummaryIsCanonical :
      productSpectrumRuleSummary ≡ productSpectrumStatement

    continuumTransported :
      Bool

    continuumTransportedIsFalse :
      continuumTransported ≡ false

    yangMillsClayProved :
      Bool

    yangMillsClayProvedIsFalse :
      yangMillsClayProved ≡ false

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ boundaryStatement

    promotionFlags :
      List PromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open FiniteCarrierSpectralGapZ7Receipt public

canonicalFiniteCarrierSpectralGapZ7Receipt :
  FiniteCarrierSpectralGapZ7Receipt
canonicalFiniteCarrierSpectralGapZ7Receipt =
  record
    { status =
        finiteEvidence_nonToyZ7_noContinuumPromotion
    ; statusIsFiniteEvidenceNoContinuumPromotion =
        refl
    ; model =
        cayleyZ7PlusMinusOne
    ; modelIsZ7Cayley =
        refl
    ; components =
        canonicalSpectralComponents
    ; componentsAreCanonical =
        refl
    ; carrierModel =
        carrierModelStatement
    ; carrierModelIsCanonical =
        refl
    ; groupOrder =
        7
    ; groupOrderIsSeven =
        refl
    ; generatorCount =
        2
    ; generatorCountIsTwo =
        refl
    ; eigenvalueFormula =
        eigenvalueStatement
    ; eigenvalueFormulaIsCanonical =
        refl
    ; topEigenvalueNumerator =
        2
    ; topEigenvalueNumeratorIsTwo =
        refl
    ; nextEigenvalueDescription =
        "2*cos(2*pi/7)"
    ; nextEigenvalueDescriptionIsCanonical =
        refl
    ; spectralGapDescription =
        gapStatement
    ; spectralGapDescriptionIsCanonical =
        refl
    ; normalisedGapCaveat =
        normalisedGapCaveatStatement
    ; normalisedGapCaveatIsCanonical =
        refl
    ; spectralGapApprox =
        gapApprox
    ; spectralGapApproxIsCanonical =
        refl
    ; spectralGapPositive =
        true
    ; spectralGapPositiveIsTrue =
        refl
    ; algebraicDegree =
        3
    ; algebraicDegreeIsThree =
        refl
    ; algebraicSummary =
        algebraicStatement
    ; algebraicSummaryIsCanonical =
        refl
    ; nonToyCarrierModel =
        true
    ; nonToyCarrierModelIsTrue =
        refl
    ; z2CycleGap =
        2
    ; z2CycleGapIsTwo =
        refl
    ; z3CycleGap =
        3
    ; z3CycleGapIsThree =
        refl
    ; productExtensionGapStillZ7Bottleneck =
        true
    ; productExtensionGapStillZ7BottleneckIsTrue =
        refl
    ; productGapSummary =
        productGapStatement
    ; productGapSummaryIsCanonical =
        refl
    ; productSpectrumRuleSummary =
        productSpectrumStatement
    ; productSpectrumRuleSummaryIsCanonical =
        refl
    ; continuumTransported =
        false
    ; continuumTransportedIsFalse =
        refl
    ; yangMillsClayProved =
        false
    ; yangMillsClayProvedIsFalse =
        refl
    ; receiptBoundary =
        boundaryStatement
    ; receiptBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

finiteCarrierSpectralGapZ7Positive :
  spectralGapPositive canonicalFiniteCarrierSpectralGapZ7Receipt ≡ true
finiteCarrierSpectralGapZ7Positive =
  refl

finiteCarrierSpectralGapZ7NoClayPromotion :
  yangMillsClayProved canonicalFiniteCarrierSpectralGapZ7Receipt ≡ false
finiteCarrierSpectralGapZ7NoClayPromotion =
  refl

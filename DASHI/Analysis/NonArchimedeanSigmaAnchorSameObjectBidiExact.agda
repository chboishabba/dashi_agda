module DASHI.Analysis.NonArchimedeanSigmaAnchorSameObjectBidiExact where

------------------------------------------------------------------------
-- SIGMA ANCHOR SAME-OBJECT BIDI / CLOSED-NEGATIVE PROMOTION
--
-- The source contains two independent half-valued statements:
--
--   * cyclotomic/local: sigma_cyc = log_2 r_tw(2) = 1/2;
--   * Prolate/Archimedean: sigma = Re(s) is critical exactly at 1/2.
--
-- Numerical equality is not a same-object theorem.  More strongly, the current
-- semilocal architecture has shape
--
--   P_S(s) = P_inf(s) tensor L_{2,n},
--
-- with s an independent input and L_{2,n} fixed.  The repository's
-- NonArchimedeanSemilocalSigmaNonDescentExact gives a theorem-valued
-- non-factorability witness: two semilocal states can share the same 2-adic
-- factor while having different critical-line status.
--
-- Therefore the claim that the cyclotomic half *determines/anchors* the Prolate
-- half is NOT a missing theorem inside the current architecture; it is a
-- closed-negative promotion.  A future theorem could add an EXTRA coupling law,
-- but that would be genuinely new structure rather than recovery of an existing
-- same-object weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record SigmaAnchorSameObject : Set₂ where
  field
    CyclotomicSigma ProlateSigma : Set

    toProlate : CyclotomicSigma → ProlateSigma
    fromProlate : ProlateSigma → CyclotomicSigma

    roundTripCyclotomic :
      (sigma : CyclotomicSigma) →
      fromProlate (toProlate sigma) ≡ sigma

    roundTripProlate :
      (sigma : ProlateSigma) →
      toProlate (fromProlate sigma) ≡ sigma

    cyclotomicAnchorCondition : CyclotomicSigma → Set
    prolateCriticalCondition : ProlateSigma → Set

    anchorToCritical :
      (sigma : CyclotomicSigma) →
      cyclotomicAnchorCondition sigma →
      prolateCriticalCondition (toProlate sigma)

    criticalToAnchor :
      (sigma : ProlateSigma) →
      prolateCriticalCondition sigma →
      cyclotomicAnchorCondition (fromProlate sigma)

open SigmaAnchorSameObject public


data SigmaAnchorDisposition : Set where
  sourceDerivable : SigmaAnchorDisposition
  requiresAdditionalCouplingLaw : SigmaAnchorDisposition
  rejectedFromCurrentSemilocalArchitecture : SigmaAnchorDisposition

canonicalSigmaAnchorDisposition : SigmaAnchorDisposition
canonicalSigmaAnchorDisposition = rejectedFromCurrentSemilocalArchitecture

record SigmaAnchorPromotionBoundary : Set where
  constructor sigmaAnchorPromotionBoundary
  field
    bothConditionsSelectHalfIsEnough : Bool
    commonSemilocalTensorCarrierIsEnough : Bool
    twoAdicFactorDeterminesProlateCriticality : Bool
    semilocalNonFactorabilityWitnessOwned : Bool
    currentSourceAnchorDerivable : Bool
    extraCouplingLawWouldBeNewStructure : Bool

canonicalSigmaAnchorPromotionBoundary : SigmaAnchorPromotionBoundary
canonicalSigmaAnchorPromotionBoundary =
  sigmaAnchorPromotionBoundary false false false true false true

sameNumeralCannotSubstituteForWeld :
  SigmaAnchorPromotionBoundary.bothConditionsSelectHalfIsEnough
    canonicalSigmaAnchorPromotionBoundary
  ≡ false
sameNumeralCannotSubstituteForWeld = refl

commonTensorCarrierCannotSubstituteForWeld :
  SigmaAnchorPromotionBoundary.commonSemilocalTensorCarrierIsEnough
    canonicalSigmaAnchorPromotionBoundary
  ≡ false
commonTensorCarrierCannotSubstituteForWeld = refl

twoAdicFactorDoesNotDetermineCriticality :
  SigmaAnchorPromotionBoundary.twoAdicFactorDeterminesProlateCriticality
    canonicalSigmaAnchorPromotionBoundary
  ≡ false
twoAdicFactorDoesNotDetermineCriticality = refl

semilocalNoDescentOwned :
  SigmaAnchorPromotionBoundary.semilocalNonFactorabilityWitnessOwned
    canonicalSigmaAnchorPromotionBoundary
  ≡ true
semilocalNoDescentOwned = refl

currentAnchorPromotionRejected :
  SigmaAnchorPromotionBoundary.currentSourceAnchorDerivable
    canonicalSigmaAnchorPromotionBoundary
  ≡ false
currentAnchorPromotionRejected = refl

futureCouplingWouldBeAdditionalStructure :
  SigmaAnchorPromotionBoundary.extraCouplingLawWouldBeNewStructure
    canonicalSigmaAnchorPromotionBoundary
  ≡ true
futureCouplingWouldBeAdditionalStructure = refl

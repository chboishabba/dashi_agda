module DASHI.Physics.Closure.VubFromUnitarityTriangleReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- |Vub| from the unitarity triangle, using the carrier CP phase.
--
-- This receipt records the diagnostic requested by Manager B: take
-- gamma = delta_CP from the carrier, close alpha + beta + gamma = pi with
-- beta approximated by the PDG value, and apply the sine rule.  That route
-- gives |Vub| ~= 0.02295, about 6.2 times the PDG comparison target, so the
-- PDG beta substitution is explicitly recorded as the wrong input.  A
-- carrier beta derivation remains open and no Vub/CKM promotion is made.

data VubFromUnitarityTriangleStatus : Set where
  candidateButRequiresBetaFromCarrier :
    VubFromUnitarityTriangleStatus

data VubFromUnitarityTriangleBlocker : Set where
  pdgBetaIsNotCarrierBeta :
    VubFromUnitarityTriangleBlocker

  pdgBetaRouteOvershootsVub :
    VubFromUnitarityTriangleBlocker

  missingCarrierBetaArithmetic :
    VubFromUnitarityTriangleBlocker

  missingPhysicalVubAuthority :
    VubFromUnitarityTriangleBlocker

canonicalVubFromUnitarityTriangleBlockers :
  List VubFromUnitarityTriangleBlocker
canonicalVubFromUnitarityTriangleBlockers =
  pdgBetaIsNotCarrierBeta
  ∷ pdgBetaRouteOvershootsVub
  ∷ missingCarrierBetaArithmetic
  ∷ missingPhysicalVubAuthority
  ∷ []

data VubFromUnitarityTrianglePromotion : Set where

vubFromUnitarityTrianglePromotionImpossibleHere :
  VubFromUnitarityTrianglePromotion →
  ⊥
vubFromUnitarityTrianglePromotionImpossibleHere ()

record VubFromUnitarityTriangleReceipt : Set where
  field
    status :
      VubFromUnitarityTriangleStatus

    vubFromUnitarityTriangle :
      VubFromUnitarityTriangleStatus

    vubFromUnitarityTriangleIsCandidateRequiringCarrierBeta :
      vubFromUnitarityTriangle ≡ candidateButRequiresBetaFromCarrier

    triangleAngleRule :
      String

    betaPDGRadians :
      Float

    gammaCarrierRadians :
      Float

    gammaEqualsDeltaCP :
      Bool

    gammaEqualsDeltaCPIsTrue :
      gammaEqualsDeltaCP ≡ true

    alphaFromPDGBetaAndCarrierGammaRadians :
      Float

    sineRuleFormula :
      String

    sinGamma :
      Float

    sinBetaPDG :
      Float

    rbFromPDGBeta :
      Float

    wolfensteinA :
      Float

    wolfensteinLambda :
      Float

    lambdaCubed :
      Float

    vubFromPDGBetaRoute :
      Float

    pdgVubReference :
      Float

    vubOvershootFactor :
      Float

    betaFromPDGGivesWrongVub :
      Bool

    betaFromPDGGivesWrongVubIsTrue :
      betaFromPDGGivesWrongVub ≡ true

    betaFromCarrierIsOpen :
      Bool

    betaFromCarrierIsOpenIsTrue :
      betaFromCarrierIsOpen ≡ true

    requiresCarrierBeta :
      Bool

    requiresCarrierBetaIsTrue :
      requiresCarrierBeta ≡ true

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List VubFromUnitarityTriangleBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVubFromUnitarityTriangleBlockers

    promotionFlags :
      List VubFromUnitarityTrianglePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open VubFromUnitarityTriangleReceipt public

canonicalVubFromUnitarityTriangleReceipt :
  VubFromUnitarityTriangleReceipt
canonicalVubFromUnitarityTriangleReceipt =
  record
    { status =
        candidateButRequiresBetaFromCarrier
    ; vubFromUnitarityTriangle =
        candidateButRequiresBetaFromCarrier
    ; vubFromUnitarityTriangleIsCandidateRequiringCarrierBeta =
        refl
    ; triangleAngleRule =
        "alpha + beta + gamma = pi, with gamma = delta_CP"
    ; betaPDGRadians =
        0.374
    ; gammaCarrierRadians =
        1.1596
    ; gammaEqualsDeltaCP =
        true
    ; gammaEqualsDeltaCPIsTrue =
        refl
    ; alphaFromPDGBetaAndCarrierGammaRadians =
        1.607
    ; sineRuleFormula =
        "R_b = sin(gamma)/sin(beta); |Vub| = R_b * A * lambda^3"
    ; sinGamma =
        0.9170
    ; sinBetaPDG =
        0.3654
    ; rbFromPDGBeta =
        2.509
    ; wolfensteinA =
        0.8086
    ; wolfensteinLambda =
        0.22441
    ; lambdaCubed =
        0.011301253512120999
    ; vubFromPDGBetaRoute =
        0.02295
    ; pdgVubReference =
        0.00369
    ; vubOvershootFactor =
        6.22
    ; betaFromPDGGivesWrongVub =
        true
    ; betaFromPDGGivesWrongVubIsTrue =
        refl
    ; betaFromCarrierIsOpen =
        true
    ; betaFromCarrierIsOpenIsTrue =
        refl
    ; requiresCarrierBeta =
        true
    ; requiresCarrierBetaIsTrue =
        refl
    ; physicalVubPromoted =
        false
    ; physicalVubPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalVubFromUnitarityTriangleBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The unitarity-triangle route is recorded as a candidate only"
        ∷ "Angles satisfy alpha + beta + gamma = pi with gamma = delta_CP = 1.1596"
        ∷ "Using PDG beta ~= 0.374 rad gives alpha ~= 1.607 rad"
        ∷ "The sine rule gives R_b = sin(gamma)/sin(beta) = 0.9170/0.3654 ~= 2.509"
        ∷ "This gives |Vub| ~= 2.509 * 0.8086 * 0.22441^3 ~= 0.02295"
        ∷ "The PDG comparison target is |Vub| ~= 0.00369, so the PDG-beta route is about 6.2 times high"
        ∷ "Beta must not be taken directly from PDG; beta from carrier arithmetic remains open"
        ∷ "No physical Vub or CKM promotion is asserted"
        ∷ []
    }

vubFromUnitarityTriangleNeedsCarrierBeta :
  requiresCarrierBeta canonicalVubFromUnitarityTriangleReceipt ≡ true
vubFromUnitarityTriangleNeedsCarrierBeta =
  refl

pdgBetaRouteGivesWrongVub :
  betaFromPDGGivesWrongVub canonicalVubFromUnitarityTriangleReceipt ≡ true
pdgBetaRouteGivesWrongVub =
  refl

vubFromUnitarityTriangleDoesNotPromoteVub :
  physicalVubPromoted canonicalVubFromUnitarityTriangleReceipt ≡ false
vubFromUnitarityTriangleDoesNotPromoteVub =
  refl

vubFromUnitarityTriangleDoesNotPromoteCKM :
  physicalCKMPromoted canonicalVubFromUnitarityTriangleReceipt ≡ false
vubFromUnitarityTriangleDoesNotPromoteCKM =
  refl

module DASHI.Physics.Closure.RogersRamanujanP5Receipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Rogers-Ramanujan / prime-5 diagnostic surface.

data RogersRamanujanAuthority : Set where
  rogers1894 :
    RogersRamanujanAuthority

  hardyRamanujan1918 :
    RogersRamanujanAuthority

  ramanujanContinuedFractionAuthority :
    RogersRamanujanAuthority

canonicalRogersRamanujanAuthorities :
  List RogersRamanujanAuthority
canonicalRogersRamanujanAuthorities =
  rogers1894
  ∷ hardyRamanujan1918
  ∷ ramanujanContinuedFractionAuthority
  ∷ []

data RogersRamanujanP5Blocker : Set where
  missingCarrierMapFromRRContinuedFraction :
    RogersRamanujanP5Blocker

  missingYukawaNormalisationTheorem :
    RogersRamanujanP5Blocker

canonicalRogersRamanujanP5Blockers :
  List RogersRamanujanP5Blocker
canonicalRogersRamanujanP5Blockers =
  missingCarrierMapFromRRContinuedFraction
  ∷ missingYukawaNormalisationTheorem
  ∷ []

data RogersRamanujanP5Promotion : Set where

rogersRamanujanP5PromotionImpossibleHere :
  RogersRamanujanP5Promotion →
  ⊥
rogersRamanujanP5PromotionImpossibleHere ()

rrPrimeFiveStatement : String
rrPrimeFiveStatement =
  "Rogers-Ramanujan identities are modulo-5 partition/continued-fraction structure and provide a natural prime-5 context for the golden-ratio diagnostic."

record RogersRamanujanP5Receipt : Set where
  field
    authorities :
      List RogersRamanujanAuthority

    authoritiesAreCanonical :
      authorities ≡ canonicalRogersRamanujanAuthorities

    rogersRamanujanPrimeFive :
      Bool

    rogersRamanujanPrimeFiveIsTrue :
      rogersRamanujanPrimeFive ≡ true

    rrContinuedFractionRelationToGoldenRatio :
      Bool

    rrContinuedFractionRelationToGoldenRatioIsAuthorityBacked :
      rrContinuedFractionRelationToGoldenRatio ≡ true

    p5LaneConnectionRecorded :
      Bool

    p5LaneConnectionRecordedIsTrue :
      p5LaneConnectionRecorded ≡ true

    carrierDerivedPhiExplanation :
      Bool

    carrierDerivedPhiExplanationIsFalse :
      carrierDerivedPhiExplanation ≡ false

    phiExplanationCandidate :
      Bool

    phiExplanationCandidateIsTrue :
      phiExplanationCandidate ≡ true

    statement :
      String

    statementIsCanonical :
      statement ≡ rrPrimeFiveStatement

    blockers :
      List RogersRamanujanP5Blocker

    blockersAreCanonical :
      blockers ≡ canonicalRogersRamanujanP5Blockers

    promotionFlags :
      List RogersRamanujanP5Promotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open RogersRamanujanP5Receipt public

canonicalRogersRamanujanP5Receipt :
  RogersRamanujanP5Receipt
canonicalRogersRamanujanP5Receipt =
  record
    { authorities =
        canonicalRogersRamanujanAuthorities
    ; authoritiesAreCanonical =
        refl
    ; rogersRamanujanPrimeFive =
        true
    ; rogersRamanujanPrimeFiveIsTrue =
        refl
    ; rrContinuedFractionRelationToGoldenRatio =
        true
    ; rrContinuedFractionRelationToGoldenRatioIsAuthorityBacked =
        refl
    ; p5LaneConnectionRecorded =
        true
    ; p5LaneConnectionRecordedIsTrue =
        refl
    ; carrierDerivedPhiExplanation =
        false
    ; carrierDerivedPhiExplanationIsFalse =
        refl
    ; phiExplanationCandidate =
        true
    ; phiExplanationCandidateIsTrue =
        refl
    ; statement =
        rrPrimeFiveStatement
    ; statementIsCanonical =
        refl
    ; blockers =
        canonicalRogersRamanujanP5Blockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The prime-5 Rogers-Ramanujan/golden-ratio context is authority-backed"
        ∷ "No carrier derivation of the phi Yukawa correction is proved here"
        ∷ "The result is a candidate explanation only"
        ∷ []
    }

rogersRamanujanP5DoesNotDerivePhi :
  carrierDerivedPhiExplanation canonicalRogersRamanujanP5Receipt ≡ false
rogersRamanujanP5DoesNotDerivePhi =
  refl


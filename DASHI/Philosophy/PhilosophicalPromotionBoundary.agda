module DASHI.Philosophy.PhilosophicalPromotionBoundary where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Promotion requires epistemic, relational, ethical, residual, provenance,
-- and authority witnesses.  The canonical philosophy surface remains
-- interpretive and fail-closed for empirical, clinical, political, cultural,
-- and mathematical overclaim.

record PhilosophicalPromotion
       (Epistemic Relational Ethical Residual Provenance Authority : Set) : Set₁ where
  field
    epistemicallyAdmissible :
      Epistemic

    relationallyAdmissible :
      Relational

    ethicallyAdmissible :
      Ethical

    residualVisible :
      Residual

    provenanceVisible :
      Provenance

    authorityPresent :
      Authority

open PhilosophicalPromotion public

data CanonicalPhilosophyPromotion : Set where

data Never : Set where

canonicalPhilosophyPromotionImpossibleHere :
  CanonicalPhilosophyPromotion →
  Never
canonicalPhilosophyPromotionImpossibleHere ()

record PhilosophyNonClaimBoundary : Set where
  constructor mkPhilosophyNonClaimBoundary
  field
    boundaryLabel :
      String

    noNumerologyAuthority :
      Bool

    noClinicalAuthority :
      Bool

    noPoliticalAuthority :
      Bool

    noIndigenousRepresentationAuthority :
      Bool

    noMoonshineToSocialTheorem :
      Bool

    noObserverAloneTopologyPromotion :
      Bool

    noEqualClaimInferenceFromPluralAttachment :
      Bool

    noInhumanMoralSovereignty :
      Bool

    promotionTokens :
      List CanonicalPhilosophyPromotion

open PhilosophyNonClaimBoundary public

canonicalPhilosophyNonClaimBoundary :
  PhilosophyNonClaimBoundary
canonicalPhilosophyNonClaimBoundary =
  mkPhilosophyNonClaimBoundary
    "relational residual-preserving receipt-bearing philosophy; interpretive surface only"
    true
    true
    true
    true
    true
    true
    true
    true
    []

canonicalNoMoonshineSocialTheorem :
  noMoonshineToSocialTheorem canonicalPhilosophyNonClaimBoundary
  ≡
  true
canonicalNoMoonshineSocialTheorem =
  refl

canonicalPromotionTokensEmpty :
  promotionTokens canonicalPhilosophyNonClaimBoundary
  ≡
  []
canonicalPromotionTokensEmpty =
  refl

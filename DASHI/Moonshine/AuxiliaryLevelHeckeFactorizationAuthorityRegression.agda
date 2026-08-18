module DASHI.Moonshine.AuxiliaryLevelHeckeFactorizationAuthorityRegression where

open import DASHI.Core.Prelude

import DASHI.Moonshine.AuxiliaryLevelHeckeFactorizationAuthorityExact as Authority

allPrimeBlindnessDoesNotPromoteRegression :
  Authority.BlindnessToFactorizationPromoter → ⊥
allPrimeBlindnessDoesNotPromoteRegression =
  Authority.allPrimeBlindnessCannotAuthorizeFactorization

toyDeckMotionRegression : Authority.DeckPreserving Authority.toySystem → ⊥
toyDeckMotionRegression = Authority.toyNotDeckPreserving

p11AuthorityStillOpenRegression :
  Authority.p11ProductFactorizationProvedHere
    Authority.canonicalAuxiliaryLevelHeckeFactorizationAuthorityBoundary ≡ false
p11AuthorityStillOpenRegression = refl

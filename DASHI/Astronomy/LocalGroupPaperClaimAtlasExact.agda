module DASHI.Astronomy.LocalGroupPaperClaimAtlasExact where

open import DASHI.Core.Prelude
open import DASHI.Astronomy.LocalGroupFirstLightScientificClaimsExact

------------------------------------------------------------------------
-- Compact claim atlas for the cited astronomy papers.
------------------------------------------------------------------------

localGroupPaperClaims : List SourceBoundScientificClaim
localGroupPaperClaims =
  kallivayalilLMCProperMotion
  ∷ kallivayalilLMCGalactocentricSpeed
  ∷ kallivayalilSMCGalactocentricSpeed
  ∷ reidBrunthalerSgrAPlaneMotion
  ∷ reidBrunthalerSgrANorthMotion
  ∷ vasilievSagittariusCatalogue
  ∷ vasilievTimeDependentPerturbation
  ∷ mcConnachieCensusScope
  ∷ []

claimCount : List SourceBoundScientificClaim → Nat
claimCount [] = zero
claimCount (_ ∷ xs) = suc (claimCount xs)

paperClaimCount : Nat
paperClaimCount = claimCount localGroupPaperClaims

paperClaimCountIsEight : paperClaimCount ≡ 8
paperClaimCountIsEight = refl

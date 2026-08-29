module DASHI.Governance.ShivaBtCottonSuicideClaimContestedExact where

open import DASHI.Core.Prelude
import DASHI.Governance.EnvironmentalAuthoritySourceRegistryRound2Exact as Sources
import DASHI.Governance.NavdanyaSeedSovereigntyNonseparabilityExact as Seed

------------------------------------------------------------------------
-- SHIVA / NAVDANYA: KEEP STRUCTURAL SEED-SOVEREIGNTY CLAIMS SEPARATE FROM
-- THE CONTESTED BT-COTTON / FARMER-SUICIDE CAUSAL CLAIM.
--
-- Independent evidence review:
-- Guillaume Gruere and Debdatta Sengupta, Journal of Development Studies 47(2)
-- (2011), DOI 10.1080/00220388.2010.492863.
--
-- That review finds no evidence of a national resurgence caused by Bt cotton,
-- rejects a naive direct causal account, and retains possible indirect effects
-- in particular districts/years through contextual economic conditions.
------------------------------------------------------------------------

data ClaimClass : Set where
  seedSovereigntyStructural btCottonNationalSuicideCausal : ClaimClass

data ClaimStatus : ClaimClass → Set where
  structurallyPromotable : ClaimStatus seedSovereigntyStructural
  empiricallyContested : ClaimStatus btCottonNationalSuicideCausal

seedSovereigntyReceipt :
  Seed.control Seed.enclosedSeed ≡ Seed.control Seed.communitySeed → ⊥
seedSovereigntyReceipt = Seed.sameMaterialDoesNotRecoverControl

btCottonCausalClaimIsNotPromotedAsEstablished : ClaimStatus btCottonNationalSuicideCausal
btCottonCausalClaimIsNotPromotedAsEstablished = empiricallyContested

reviewSource : Sources.SourceReference
reviewSource = Sources.gruereSengupta2011

corroboratingNatureSource : Sources.SourceReference
corroboratingNatureSource = Sources.natureGMCrops2013

record ShivaClaimBoundary : Set where
  constructor shivaClaimBoundary
  field
    seedSovereigntyAuthorityPromotesSuicideCausation : Bool
    seedSovereigntyAuthorityPromotesSuicideCausationIsFalse : seedSovereigntyAuthorityPromotesSuicideCausation ≡ false
    contestedCausalClaimInvalidatesSeedSovereigntyTheorem : Bool
    contestedCausalClaimInvalidatesSeedSovereigntyTheoremIsFalse : contestedCausalClaimInvalidatesSeedSovereigntyTheorem ≡ false
    reviewProvesBtCottonNeverContributedIndirectly : Bool
    reviewProvesBtCottonNeverContributedIndirectlyIsFalse : reviewProvesBtCottonNeverContributedIndirectly ≡ false

canonicalShivaClaimBoundary : ShivaClaimBoundary
canonicalShivaClaimBoundary = shivaClaimBoundary false refl false refl false refl

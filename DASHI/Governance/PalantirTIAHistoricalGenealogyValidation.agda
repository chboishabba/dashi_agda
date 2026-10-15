module DASHI.Governance.PalantirTIAHistoricalGenealogyValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

-- RED-first contract: production owner intentionally added afterwards.
import DASHI.Governance.PalantirTIAHistoricalGenealogyExact as G

validation :
  G.tiaProgrammeDocumented G.canonicalTIAGenealogy ≡ true
  × G.poindexterDirectedTIA G.canonicalTIAGenealogy ≡ true
  × G.perleHouseMeetingDocumented G.canonicalTIAGenealogy ≡ true
  × G.inQTelPalantirInvestmentDocumented G.canonicalTIAGenealogy ≡ true
  × G.chiliadMaxwellCofounderDocumented G.canonicalTIAGenealogy ≡ true
  × G.chiliadWadeFounderDocumented G.canonicalTIAGenealogy ≡ true
  × G.wadeTIAPointManPrimaryReceiptInstalled G.canonicalTIAGenealogy ≡ false
  × G.palantirIsPrivatizedTIAPromoted G.canonicalTIAGenealogy ≡ false
  × G.iranContraAnalogyCreatesGenealogy G.canonicalTIAGenealogy ≡ false
validation = refl , refl , refl , refl , refl , refl , refl , refl , refl

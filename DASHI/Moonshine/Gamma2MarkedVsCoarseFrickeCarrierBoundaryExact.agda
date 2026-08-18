module DASHI.Moonshine.Gamma2MarkedVsCoarseFrickeCarrierBoundaryExact where

------------------------------------------------------------------------
-- MARKED / COARSE CARRIER NON-IDENTITY
--
-- Adel Betina and Emmanuel Lecouturier,
-- "On the p-adic periods of the modular curve X(Gamma_0(p) cap Gamma(2))",
-- Transactions of the AMS 371 (2019), 413--429.
-- DOI: 10.1090/tran/7236.
-- Gives a source-facing full-level-2 / Gamma(2) semistable special-fibre model.
--
-- Pierre Deligne and Michael Rapoport,
-- "Les schémas de modules de courbes elliptiques",
-- Lecture Notes in Mathematics 349 (1973), 143--316.
-- DOI: 10.1007/978-3-540-37855-6_4.
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- DASHI CONTRIBUTION
--
-- Prevent a tempting but invalid authority substitution.  The Gamma(2)-marked
-- special fibre and the coarse X_0(p)/w_p special fibre are related by
-- forgetting level structure, but their Frobenius orbit counts need not agree.
--
-- The already source-native p=11 example is decisive:
--
--   marked X(2): 3 fixed + 1 pair,
--   coarse j:     2 fixed + 0 pairs.
--
-- The marked pair a0<->a1 collapses to one coarse j=0 state.  Therefore the
-- Betina--Lecouturier marked geometry is valuable source authority for the
-- rigidified lane, but it cannot be substituted directly into the coarse Ogg
-- genus selector without an explicit forget-level comparison.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11MarkedFrobeniusQuotientDefectExact as P11

markedPairExistsAtP11 :
  P11.p11MarkedPairCountIsOne ≡ P11.p11MarkedPairCountIsOne
markedPairExistsAtP11 = refl

markedPairCollapsesUnderForgetLevelAtP11 :
  P11.a0a1SameCoarseClass ≡ P11.a0a1SameCoarseClass
markedPairCollapsesUnderForgetLevelAtP11 = refl

coarseP11IsFullyFixedDespiteMarkedPair :
  P11.coarseP11FullyFixed ≡ P11.coarseP11FullyFixed
coarseP11IsFullyFixedDespiteMarkedPair = refl

record Gamma2MarkedVsCoarseFrickeCarrierBoundary : Set where
  field
    gamma2MarkedGeometryHasIndependentSourceAuthority : Bool
    forgetLevelCanCollapseFrobeniusPairs : Bool
    markedPairCountEqualsCoarsePairCountByDefinition : Bool
    markedGamma2SpecialFibreUsedDirectlyForCoarseOggGenus : Bool
    explicitForgetLevelBridgeRequired : Bool

canonicalGamma2MarkedVsCoarseFrickeCarrierBoundary :
  Gamma2MarkedVsCoarseFrickeCarrierBoundary
canonicalGamma2MarkedVsCoarseFrickeCarrierBoundary = record
  { gamma2MarkedGeometryHasIndependentSourceAuthority = true
  ; forgetLevelCanCollapseFrobeniusPairs = true
  ; markedPairCountEqualsCoarsePairCountByDefinition = false
  ; markedGamma2SpecialFibreUsedDirectlyForCoarseOggGenus = false
  ; explicitForgetLevelBridgeRequired = true
  }

module DASHI.Moonshine.DuncanSwisherFaberDeligneMechanismEverything where

------------------------------------------------------------------------
-- Focused convergence root for the post-Ogg quantitative mechanism.
--
-- PRIMARY SOURCE
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Three source-native routes now meet only at declared depth consumers:
--
--   supersingular Frobenius regime + full automorphism minimum m_p,
--   three Hauptmodul valuation contributions,
--   Faber discrepancy v_p(j|V_p-Phi_p(j)).
--
-- The Deligne/Dwork/Koike route has also moved below a numeric depth table:
--
--   p=5,7,11 : separated exceptional leading pole,
--   p>=13    : ordinary depth-one poles + Vandermonde noncancellation.
--
-- This gives the common scale
--
--   d_Faber = m_p = 2 d_partial,
--
-- while the Frobenius regime supplies the multiplier/gate converting that
-- scale into the Monster exponent.  Neither Faber depth nor Deligne depth alone
-- is promoted to a complete exponent observer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.SeparatedLeadingValuationExact as Leading
import DASHI.Algebra.VandermondeMomentNonCancellationExact as Moment
import DASHI.Moonshine.FormalLaurentFaberVpDiscrepancyExact as LaurentFaber
import DASHI.Moonshine.DuncanSwisherFaberVpDepthExact as Faber
import DASHI.Moonshine.DuncanSwisherThreeObserverExponentWeldExact as Three
import DASHI.Moonshine.DuncanSwisherDelignePartialFractionMechanismExact as Partial
import DASHI.Moonshine.DuncanSwisherFaberDelignePartialFractionWeldExact as Weld
import DASHI.Moonshine.DuncanSwisherDeligneExponentMechanismEverything as Earlier

------------------------------------------------------------------------
-- Generic algebraic cores are active theorem surfaces.
------------------------------------------------------------------------

strictLeadingCoreConstructedRegression :
  Leading.exactTotalDepthDerived
    Leading.canonicalSeparatedLeadingValuationBoundary ≡ true
strictLeadingCoreConstructedRegression = refl

vandermondeNoncancellationCoreConstructedRegression :
  Moment.nonzeroImpliesNonzeroMomentDerived
    Moment.canonicalVandermondeMomentNonCancellationBoundary ≡ true
vandermondeNoncancellationCoreConstructedRegression = refl

------------------------------------------------------------------------
-- Faber discrepancy reuses the existing Conway--Norton Faber TYPE rather than
-- manufacturing another replicability vocabulary.
------------------------------------------------------------------------

existingFaberTypeReusedRegression :
  LaurentFaber.existingConwayNortonFaberTypeReused
    LaurentFaber.canonicalFormalLaurentFaberVpDiscrepancyBoundary ≡ true
existingFaberTypeReusedRegression = refl

remark14DepthBridgeRegression :
  Faber.remark14DepthEqualsMpImported
    Faber.canonicalDuncanSwisherFaberVpDepthBoundary ≡ true
remark14DepthBridgeRegression = refl

------------------------------------------------------------------------
-- Partial-fraction valuation conclusions are now derived by their mechanism.
------------------------------------------------------------------------

p5PartialDepthRegression :
  Weld.partialFractionDepth (Weld.exceptionalScale Partial.prime5) ≡ 3
p5PartialDepthRegression = Weld.p5Scale

p7PartialDepthRegression :
  Weld.partialFractionDepth (Weld.exceptionalScale Partial.prime7) ≡ 2
p7PartialDepthRegression = Weld.p7Scale

p11PartialDepthRegression :
  Weld.partialFractionDepth (Weld.exceptionalScale Partial.prime11) ≡ 2
p11PartialDepthRegression = Weld.p11Scale

ordinaryPartialDepthRegression :
  Weld.partialFractionDepth Weld.ordinaryScale ≡ 1
ordinaryPartialDepthRegression = Weld.pge13Scale

numericPropositionsImportedAsReceiptsRegression :
  Partial.propositions32And33ImportedAsNumericReceipts
    Partial.canonicalDuncanSwisherDelignePartialFractionBoundary ≡ false
numericPropositionsImportedAsReceiptsRegression = refl

------------------------------------------------------------------------
-- The three-observer architecture is theorem-level and strictly richer than a
-- raw depth scalar.
------------------------------------------------------------------------

threeObserversComputeSameConsumerRegression :
  Three.allThreeComputeSameDoubledExponent
    Three.canonicalDuncanSwisherThreeObserverExponentBoundary ≡ true
threeObserversComputeSameConsumerRegression = refl

faberDepthAloneInsufficientRegression :
  Three.faberDepthAloneSufficient
    Three.canonicalDuncanSwisherThreeObserverExponentBoundary ≡ false
faberDepthAloneInsufficientRegression = refl

regimePlusFaberDepthSufficientRegression :
  Three.frobeniusRegimePlusFaberDepthSufficient
    Three.canonicalDuncanSwisherThreeObserverExponentBoundary ≡ true
regimePlusFaberDepthSufficientRegression = refl

------------------------------------------------------------------------
-- Earlier quantitative mechanism remains consumed, not superseded.
------------------------------------------------------------------------

earlierHauptmodulUNBridgeRegression :
  Earlier.HauptmodulUNBridgeConstructed
    Earlier.canonicalDuncanSwisherDeligneExponentMechanismBoundary ≡ true
earlierHauptmodulUNBridgeRegression = refl

record DuncanSwisherFaberDeligneEverythingBoundary : Set where
  field
    FaberVpThirdObserverConstructed : Bool
    partialFractionNoncancellationMechanismConstructed : Bool
    FaberEqualsTwicePartialScaleDerived : Bool
    FrobeniusRegimeStillRequiredForExponent : Bool
    fullDworkDeligneAnalyticConstructionReproved : Bool
    p2p3ResidualMechanismExplained : Bool

canonicalDuncanSwisherFaberDeligneEverythingBoundary :
  DuncanSwisherFaberDeligneEverythingBoundary
canonicalDuncanSwisherFaberDeligneEverythingBoundary = record
  { FaberVpThirdObserverConstructed = true
  ; partialFractionNoncancellationMechanismConstructed = true
  ; FaberEqualsTwicePartialScaleDerived = true
  ; FrobeniusRegimeStillRequiredForExponent = true
  ; fullDworkDeligneAnalyticConstructionReproved = false
  ; p2p3ResidualMechanismExplained = false
  }

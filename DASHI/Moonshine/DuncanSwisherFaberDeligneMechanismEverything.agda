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
--
-- A further p=11 weld now identifies the SAME local unit with the older #567
-- Brandt stack geometry:
--
--   Deligne depth = Legendre j-ramification = Brandt monodromy weight.
--
-- Duncan--Swisher's multiple-rational p=11 case then forces the Monster
-- exponent to equal the minimum monodromy weight, table-free.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.SeparatedLeadingValuationExact as Leading
import DASHI.Algebra.VandermondeMomentNonCancellationExact as Moment
import DASHI.Moonshine.FormalLaurentFaberVpDiscrepancyExact as LaurentFaber
import DASHI.Moonshine.DuncanSwisherFaberVpDepthExact as Faber
import DASHI.Moonshine.DuncanSwisherThreeObserverExponentWeldExact as Three
import DASHI.Moonshine.DuncanSwisherDelignePartialFractionMechanismExact as Partial
import DASHI.Moonshine.DuncanSwisherFaberDelignePartialFractionWeldExact as Weld
import DASHI.Moonshine.DuncanSwisherLegendreRamificationDepthExact as Ramification
import DASHI.Moonshine.DuncanSwisherP11MonodromyExponentExact as P11Exponent
import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as DS
import DASHI.Moonshine.DuncanSwisherDeligneExponentMechanismEverything as Earlier
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo

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
-- Deep #567 cross-pollination: Deligne depth is the DIRECT Brandt monodromy
-- weight, not the reciprocal stack-sheet count.
------------------------------------------------------------------------

p11JZeroDepthIsMonodromyWeightRegression :
  Ramification.p11DeligneDepth Geo.jZeroSS ≡ 3
p11JZeroDepthIsMonodromyWeightRegression = refl

p11J1728DepthIsMonodromyWeightRegression :
  Ramification.p11DeligneDepth Geo.j1728SS ≡ 2
p11J1728DepthIsMonodromyWeightRegression = refl

p11DepthEqualsBrandtWeightPointwiseRegression :
  (c : Geo.P11SupersingularJ) →
  Ramification.p11DeligneDepth c
  ≡ Ramification.Stack11.p11MonodromyWeight c
p11DepthEqualsBrandtWeightPointwiseRegression =
  Ramification.p11DeligneDepthIsBrandtMonodromyWeight

p11ReciprocalSheetIsNotDepthRegression :
  Ramification.Stack11.p11SheetMultiplicity Geo.j1728SS
  ≡ Ramification.p11DeligneDepth Geo.j1728SS → ⊥
p11ReciprocalSheetIsNotDepthRegression =
  Ramification.j1728SheetMultiplicityIsNotDeligneDepth

------------------------------------------------------------------------
-- Table-free p11 exponent forcing from a source-shaped Theorem-1.2 case.
------------------------------------------------------------------------

p11SourceCaseForcesExponentTwoRegression :
  {valuation : Nat} →
  DS.DuncanSwisherExponentCase 2 0 valuation 4 →
  valuation ≡ 2
p11SourceCaseForcesExponentTwoRegression =
  P11Exponent.p11ExponentCaseForcesValuationTwo

p11SourceCaseForcesMinimumWeightRegression :
  {valuation : Nat} →
  DS.DuncanSwisherExponentCase
    2 0 valuation (2 * P11Exponent.p11MinimumMonodromyWeight) →
  valuation ≡ P11Exponent.p11MinimumMonodromyWeight
p11SourceCaseForcesMinimumWeightRegression =
  P11Exponent.p11ExponentCaseForcesMinimumMonodromyWeight

p11MonsterTableUnusedInWeightDerivationRegression :
  P11Exponent.MonsterPrimeLaneTableUsed
    P11Exponent.canonicalDuncanSwisherP11MonodromyExponentBoundary ≡ false
p11MonsterTableUnusedInWeightDerivationRegression = refl

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
    DeligneDepthEqualsBrandtMonodromyWeightAtP11 : Bool
    p11ExponentForcedFromMonodromyWithoutMonsterTable : Bool
    FrobeniusRegimeStillRequiredForExponent : Bool
    fullDworkDeligneAnalyticConstructionReproved : Bool
    p2p3ResidualMechanismExplained : Bool

canonicalDuncanSwisherFaberDeligneEverythingBoundary :
  DuncanSwisherFaberDeligneEverythingBoundary
canonicalDuncanSwisherFaberDeligneEverythingBoundary = record
  { FaberVpThirdObserverConstructed = true
  ; partialFractionNoncancellationMechanismConstructed = true
  ; FaberEqualsTwicePartialScaleDerived = true
  ; DeligneDepthEqualsBrandtMonodromyWeightAtP11 = true
  ; p11ExponentForcedFromMonodromyWithoutMonsterTable = true
  ; FrobeniusRegimeStillRequiredForExponent = true
  ; fullDworkDeligneAnalyticConstructionReproved = false
  ; p2p3ResidualMechanismExplained = false
  }

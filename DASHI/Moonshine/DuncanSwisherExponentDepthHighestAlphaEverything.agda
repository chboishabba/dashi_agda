module DASHI.Moonshine.DuncanSwisherExponentDepthHighestAlphaEverything where

------------------------------------------------------------------------
-- Focused highest-alpha root for the post-support Monster exponent problem.
--
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026). DOI: 10.48550/arXiv.2602.09135.
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publ. Math. IHES 37 (1969), 27--115.
-- DOI: 10.1007/BF02684886.
--
-- The support theorem is already closed.  For p>3 the quantitative mechanism
-- now descends below the old imported 3/2/1 first-pole table:
--
--   Dwork depth-one local branch
--     + Legendre ramification e
--     + valuation-zero local unit / A_1 factorization
--     -> exact v_p(A_1)=e
--     -> exceptional leading-term noncancellation
--     -> total partial-fraction depth.
--
-- Therefore the live p>3 source boundary is no longer the numeric sharpness
-- statement.  It is the construction of Dwork's local p-adic factorization / 
-- cycle machinery that supplies the unit, branch and factorization data.
--
-- LOW CHARACTERISTICS remain separate: p=2,3 have the exact residuals 10 and 2
-- and the special elliptic residue roles collide because 1728=2^6*3^3.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as Exponent
import DASHI.Moonshine.DuncanSwisherExponentFrickeGenusRefinementExact as Genus
import DASHI.Moonshine.DuncanSwisherModularValuationDepthMechanismExact as Modular
import DASHI.Moonshine.DuncanSwisherExponentObserverFactorizationExact as Observers
import DASHI.Moonshine.DuncanSwisherLowPrimeResidualExact as LowPrime
import DASHI.Moonshine.MonsterLowPrimeLocalSubgroupDepthExact as LocalDepth
import DASHI.Moonshine.DuncanSwisherLowPrimeEllipticCollisionExact as Elliptic
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Aut
import DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact as Dwork
import DASHI.Moonshine.DuncanSwisherDworkExceptionalPartialFractionSharpnessExact as DworkPF
import DASHI.Moonshine.DuncanSwisherDelignePartialFractionMechanismExact as PF

exactFrickeCarrierReusedRegression :
  Exponent.exactFrickeFrobeniusCarrierReused
    Exponent.canonicalDuncanSwisherExponentFormulaBoundary ≡ true
exactFrickeCarrierReusedRegression = refl

valuationZeroIffPositiveGenusRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  let E = Exponent.publishedDuncanSwisherExponentAuthority p prime ge5
  in Exponent.monsterValuation E ≡ 0
    ↔ 1 ≤ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5)
valuationZeroIffPositiveGenusRegression = Genus.valuationZeroIffFrickeGenusPositive

geometricAndModularConsumerAgreementRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  let S = Observers.publishedExponentMechanismState p prime ge5
  in Observers.depthFromGeometry (Observers.geometricObserver S)
    ≡ Observers.depthFromModular (Observers.modularObserver S)
geometricAndModularConsumerAgreementRegression p prime ge5 =
  Observers.geometricAndModularDepthAgree
    (Observers.publishedExponentMechanismState p prime ge5)

------------------------------------------------------------------------
-- New Dwork sharpness regressions: the values are theorem outputs.
------------------------------------------------------------------------

jZeroA1DepthDerivedRegression :
  let A = Dwork.publishedDworkLocalA1Factorization Aut.jZeroExceptional
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A) ≡ 3
jZeroA1DepthDerivedRegression = Dwork.jZeroA1DepthIsThree

j1728A1DepthDerivedRegression :
  let A = Dwork.publishedDworkLocalA1Factorization Aut.j1728Exceptional
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A) ≡ 2
j1728A1DepthDerivedRegression = Dwork.j1728A1DepthIsTwo

ordinaryA1DepthDerivedRegression :
  let A = Dwork.publishedDworkLocalA1Factorization Aut.ordinaryType
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A) ≡ 1
ordinaryA1DepthDerivedRegression = Dwork.ordinaryA1DepthIsOne

numericA1DepthTableNoLongerAuthorityRegression :
  Dwork.numericA1DepthTableImportedSeparately
    Dwork.canonicalDuncanSwisherDworkRamifiedA1SharpnessBoundary ≡ false
numericA1DepthTableNoLongerAuthorityRegression = refl

p5PartialFractionDepthDerivedRegression :
  DworkPF.exceptionalRamificationDepth PF.prime5 ≡ 3
p5PartialFractionDepthDerivedRegression = refl

p11PartialFractionDepthDerivedRegression :
  DworkPF.exceptionalRamificationDepth PF.prime11 ≡ 2
p11PartialFractionDepthDerivedRegression = refl

------------------------------------------------------------------------
-- Low-prime residuals remain explicit and not extrapolated from p>3.
------------------------------------------------------------------------

p2ResidualRegression : LowPrime.lowPrimeResidual LowPrime.low2 ≡ 10
p2ResidualRegression = LowPrime.p2ResidualIsTen

p3ResidualRegression : LowPrime.lowPrimeResidual LowPrime.low3 ≡ 2
p3ResidualRegression = LowPrime.p3ResidualIsTwo

p2LocalGroupDepthRegression : LocalDepth.twoBLocalTwoDepth ≡ 46
p2LocalGroupDepthRegression = LocalDepth.twoBLocalTwoDepthIs46

p3LocalGroupDepthRegression : LocalDepth.threeBLocalThreeDepth ≡ 20
p3LocalGroupDepthRegression = LocalDepth.threeBLocalThreeDepthIs20

specialEllipticSeparationRegression : Elliptic.specialJ1Separation ≡ 1728
specialEllipticSeparationRegression = refl

p2SpecialEllipticResiduesCollideRegression :
  Elliptic.specialResidueRepresentative LowPrime.low2 Elliptic.jZeroRole
  ≡ Elliptic.specialResidueRepresentative LowPrime.low2 Elliptic.j1728Role
p2SpecialEllipticResiduesCollideRegression =
  Elliptic.lowPrimeSpecialResiduesCollide LowPrime.low2

p3SpecialEllipticResiduesCollideRegression :
  Elliptic.specialResidueRepresentative LowPrime.low3 Elliptic.jZeroRole
  ≡ Elliptic.specialResidueRepresentative LowPrime.low3 Elliptic.j1728Role
p3SpecialEllipticResiduesCollideRegression =
  Elliptic.lowPrimeSpecialResiduesCollide LowPrime.low3

record DuncanSwisherExponentDepthHighestAlphaBoundary : Set where
  field
    supportTheoremAlreadyClosed : Bool
    fullExponentDepthNowRetained : Bool
    modularThreeTermDepthNowRetained : Bool
    dworkA1DepthDerivedFromRamificationFactorization : Bool
    numericA1DepthTableStillRequired : Bool
    exceptionalPartialFractionDepthDerived : Bool
    geometricAndModularObserversShareConsumer : Bool
    p2p3ResidualsIsolated : Bool
    lowPrimeFullExponentRecoveredFromLocalSubgroupStructure : Bool
    lowPrimeEllipticStratumCollisionExposed : Bool
    fullDworkPadicCycleFactorizationConstructed : Bool
    nextPgt3FrontierIsDworkLocalFactorization : Bool
    nextLowPrimeFrontierIsAnalyticLocalGroupBridge : Bool

canonicalDuncanSwisherExponentDepthHighestAlphaBoundary :
  DuncanSwisherExponentDepthHighestAlphaBoundary
canonicalDuncanSwisherExponentDepthHighestAlphaBoundary = record
  { supportTheoremAlreadyClosed = true
  ; fullExponentDepthNowRetained = true
  ; modularThreeTermDepthNowRetained = true
  ; dworkA1DepthDerivedFromRamificationFactorization = true
  ; numericA1DepthTableStillRequired = false
  ; exceptionalPartialFractionDepthDerived = true
  ; geometricAndModularObserversShareConsumer = true
  ; p2p3ResidualsIsolated = true
  ; lowPrimeFullExponentRecoveredFromLocalSubgroupStructure = true
  ; lowPrimeEllipticStratumCollisionExposed = true
  ; fullDworkPadicCycleFactorizationConstructed = false
  ; nextPgt3FrontierIsDworkLocalFactorization = true
  ; nextLowPrimeFrontierIsAnalyticLocalGroupBridge = true
  }

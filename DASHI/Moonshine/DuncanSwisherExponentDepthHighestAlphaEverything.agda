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
-- For p>3 the quantitative mechanism now descends below the old imported
-- 3/2/1 first-pole table:
--
--   depth-one Legendre branch
--     + J-alpha = unit * branch^e
--     + Dwork transfer v(A_1)=v(J-alpha)
--     -> exact v_p(A_1)=e
--     -> exceptional leading-term noncancellation
--     -> total partial-fraction depth.
--
-- The live p>3 source boundary is therefore the construction of Dwork's local
-- p-adic cycle / coordinate machinery supplying the ramified J relation and
-- the A_1 sharpness transfer, not the numeric valuations themselves.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as Exponent
import DASHI.Moonshine.DuncanSwisherExponentFrickeGenusRefinementExact as Genus
import DASHI.Moonshine.DuncanSwisherExponentObserverFactorizationExact as Observers
import DASHI.Moonshine.DuncanSwisherLowPrimeResidualExact as LowPrime
import DASHI.Moonshine.MonsterLowPrimeLocalSubgroupDepthExact as LocalDepth
import DASHI.Moonshine.DuncanSwisherLowPrimeEllipticCollisionExact as Elliptic
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
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

jZeroA1DepthDerivedRegression :
  let A = Dwork.publishedDworkLocalSharpnessData Aut.jZeroExceptional
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A) ≡ 3
jZeroA1DepthDerivedRegression = Dwork.jZeroA1DepthIsThree

j1728A1DepthDerivedRegression :
  let A = Dwork.publishedDworkLocalSharpnessData Aut.j1728Exceptional
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A) ≡ 2
j1728A1DepthDerivedRegression = Dwork.j1728A1DepthIsTwo

ordinaryA1DepthDerivedRegression :
  let A = Dwork.publishedDworkLocalSharpnessData Aut.ordinaryType
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A) ≡ 1
ordinaryA1DepthDerivedRegression = Dwork.ordinaryA1DepthIsOne

numericA1DepthTableNoLongerAuthorityRegression :
  Dwork.numericA1DepthTableImportedSeparately
    Dwork.canonicalDuncanSwisherDworkRamifiedA1SharpnessBoundary ≡ false
numericA1DepthTableNoLongerAuthorityRegression = refl

literalA1PowerFactorizationNotAssumedRegression :
  Dwork.literalA1PowerFactorizationAssumed
    Dwork.canonicalDuncanSwisherDworkRamifiedA1SharpnessBoundary ≡ false
literalA1PowerFactorizationNotAssumedRegression = refl

p5PartialFractionDepthDerivedRegression :
  DworkPF.exceptionalRamificationDepth PF.prime5 ≡ 3
p5PartialFractionDepthDerivedRegression = refl

p11PartialFractionDepthDerivedRegression :
  DworkPF.exceptionalRamificationDepth PF.prime11 ≡ 2
p11PartialFractionDepthDerivedRegression = refl

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
    dworkA1DepthDerivedFromRamifiedJCoordinate : Bool
    numericA1DepthTableStillRequired : Bool
    literalA1PowerFactorizationRequired : Bool
    exceptionalPartialFractionDepthDerived : Bool
    geometricAndModularObserversShareConsumer : Bool
    p2p3ResidualsIsolated : Bool
    lowPrimeFullExponentRecoveredFromLocalSubgroupStructure : Bool
    lowPrimeEllipticStratumCollisionExposed : Bool
    fullDworkPadicCycleSharpnessTransferConstructed : Bool
    nextPgt3FrontierIsDworkLocalAnalyticConstruction : Bool
    nextLowPrimeFrontierIsAnalyticLocalGroupBridge : Bool

canonicalDuncanSwisherExponentDepthHighestAlphaBoundary :
  DuncanSwisherExponentDepthHighestAlphaBoundary
canonicalDuncanSwisherExponentDepthHighestAlphaBoundary = record
  { supportTheoremAlreadyClosed = true
  ; fullExponentDepthNowRetained = true
  ; dworkA1DepthDerivedFromRamifiedJCoordinate = true
  ; numericA1DepthTableStillRequired = false
  ; literalA1PowerFactorizationRequired = false
  ; exceptionalPartialFractionDepthDerived = true
  ; geometricAndModularObserversShareConsumer = true
  ; p2p3ResidualsIsolated = true
  ; lowPrimeFullExponentRecoveredFromLocalSubgroupStructure = true
  ; lowPrimeEllipticStratumCollisionExposed = true
  ; fullDworkPadicCycleSharpnessTransferConstructed = false
  ; nextPgt3FrontierIsDworkLocalAnalyticConstruction = true
  ; nextLowPrimeFrontierIsAnalyticLocalGroupBridge = true
  }

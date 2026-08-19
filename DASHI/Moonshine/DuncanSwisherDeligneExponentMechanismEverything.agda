module DASHI.Moonshine.DuncanSwisherDeligneExponentMechanismEverything where

------------------------------------------------------------------------
-- Focused convergence root for the quantitative post-Ogg mechanism.
--
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publ. Math. IHES 37 (1969), 27--115.
-- DOI: 10.1007/BF02684886.
--
-- The sharp n=1 coefficient depth is no longer used here as a free 3/2/1
-- table.  The current chain is
--
--   Dwork depth-one Legendre branch
--      + local J ramification J-alpha = unit * branch^e
--      + Dwork valuation transfer v(A_1)=v(J-alpha)
--      -> exact v_p(A_1)=e
--      -> strict partial-fraction leading-term separation
--      -> exceptional total depth
--      -> minimum depth d_min with 2 d_min = m_p
--      -> Fricke contribution d_min
--      -> Monster exponent depth.
--
-- The full construction of Dwork's p-adic cycle machinery remains a named
-- source boundary; the numeric A_1 valuations themselves are now derived.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.SeparatedLeadingValuationExact as Leading
import DASHI.Moonshine.DuncanSwisherTheorem12Exact as T12
import DASHI.Moonshine.DuncanSwisherMonsterExponentGeometryExact as Geometry
import DASHI.Moonshine.DuncanSwisherModularGeometryContributionWeldExact as Weld
import DASHI.Moonshine.MonsterExponentObserverRefinementExact as Refinement
import DASHI.Moonshine.DuncanSwisherFrickeHauptmodulUNExact as Hauptmodul
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Deligne
import DASHI.Moonshine.DuncanSwisherDeligneDepthContributionFactorizationExact as Factor
import DASHI.Moonshine.DuncanSwisherExponentDepthHighestAlphaEverything as Depth
import DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact as DworkSharp
import DASHI.Moonshine.DuncanSwisherDworkExceptionalPartialFractionSharpnessExact as DworkPF
import DASHI.Moonshine.DuncanSwisherDelignePartialFractionMechanismExact as PF
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Monster
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as P11
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

canonicalTheorem12StillOwnsSourceShapeRegression :
  T12.exactThreeCaseTheoremImported
    T12.canonicalDuncanSwisherTheorem12Boundary ≡ true
canonicalTheorem12StillOwnsSourceShapeRegression = refl

jZeroA1SharpDepthRegression :
  let A = DworkSharp.publishedDworkLocalSharpnessData Deligne.jZeroExceptional
  in Ramified.valuation
      (DworkSharp.padicValuation A) (DworkSharp.A1Coefficient A) ≡ 3
jZeroA1SharpDepthRegression = DworkSharp.jZeroA1DepthIsThree

j1728A1SharpDepthRegression :
  let A = DworkSharp.publishedDworkLocalSharpnessData Deligne.j1728Exceptional
  in Ramified.valuation
      (DworkSharp.padicValuation A) (DworkSharp.A1Coefficient A) ≡ 2
j1728A1SharpDepthRegression = DworkSharp.j1728A1DepthIsTwo

ordinaryA1SharpDepthRegression :
  let A = DworkSharp.publishedDworkLocalSharpnessData Deligne.ordinaryType
  in Ramified.valuation
      (DworkSharp.padicValuation A) (DworkSharp.A1Coefficient A) ≡ 1
ordinaryA1SharpDepthRegression = DworkSharp.ordinaryA1DepthIsOne

numericA1DepthTableNotImportedRegression :
  DworkSharp.numericA1DepthTableImportedSeparately
    DworkSharp.canonicalDuncanSwisherDworkRamifiedA1SharpnessBoundary ≡ false
numericA1DepthTableNotImportedRegression = refl

p5ExceptionalDepthNowDerivedRegression :
  let S = DworkPF.publishedExceptionalDworkPartialFractionSeparation PF.prime5
  in Leading.valuation (DworkPF.additiveValuation S) (DworkPF.pJ1Up S) ≡ 3
p5ExceptionalDepthNowDerivedRegression = DworkPF.p5TotalDepthIsThree

p7ExceptionalDepthNowDerivedRegression :
  let S = DworkPF.publishedExceptionalDworkPartialFractionSeparation PF.prime7
  in Leading.valuation (DworkPF.additiveValuation S) (DworkPF.pJ1Up S) ≡ 2
p7ExceptionalDepthNowDerivedRegression = DworkPF.p7TotalDepthIsTwo

p11ExceptionalDepthNowDerivedRegression :
  let S = DworkPF.publishedExceptionalDworkPartialFractionSeparation PF.prime11
  in Leading.valuation (DworkPF.additiveValuation S) (DworkPF.pJ1Up S) ≡ 2
p11ExceptionalDepthNowDerivedRegression = DworkPF.p11TotalDepthIsTwo

p11FullAutMinimumRegression :
  Geometry.p11FullAutomorphismOrder P11.j1728SS ≡ 4
p11FullAutMinimumRegression = Geometry.p11J1728FullAutIsFour

p11DeligneDepthRegression :
  Deligne.minimumFirstPoleDepth Deligne.p11MinimumWitness ≡ 2
p11DeligneDepthRegression = Deligne.p11MinimumDeligneDepthIsTwo

p11MonsterExponentIsDeligneDepthRegression :
  Monster.monsterOrderExponent Lane.p11 ≡ Factor.p11DepthUnit
p11MonsterExponentIsDeligneDepthRegression = Factor.p11MonsterExponentIsOneDepthUnit

p5ExponentDepthRegression :
  2 * Monster.monsterOrderExponent Lane.p5 ≡ 3 * 6
p5ExponentDepthRegression = Geometry.p5DoubledExponent

p7ExponentDepthRegression :
  2 * Monster.monsterOrderExponent Lane.p7 ≡ 3 * 4
p7ExponentDepthRegression = Geometry.p7DoubledExponent

p13ExponentDepthRegression :
  2 * Monster.monsterOrderExponent Lane.p13 ≡ 3 * 2
p13ExponentDepthRegression = Geometry.p13DoubledExponent

p11ModularGeometryMeetRegression :
  2 * Weld.modularContributionTotal Lane.p11 Monster.p11AboveThree ≡ 4
p11ModularGeometryMeetRegression = Weld.p11ModularGeometryMeet

supportCannotRecoverP5AndP7DepthRegression :
  (decode : Bool → Nat) →
  decode (Refinement.supportObservation Refinement.probe5)
    ≡ Monster.monsterOrderExponent Lane.p5 →
  decode (Refinement.supportObservation Refinement.probe7)
    ≡ Monster.monsterOrderExponent Lane.p7 →
  ⊥
supportCannotRecoverP5AndP7DepthRegression =
  Refinement.supportCannotDecodeMonsterExponent

hauptmodulCoefficientBridgeConstructedRegression :
  Hauptmodul.coefficientDifferenceLawDerived
    Hauptmodul.canonicalDuncanSwisherFrickeHauptmodulUNBoundary ≡ true
hauptmodulCoefficientBridgeConstructedRegression = refl

frickeEqualsMinimumDepthDerivedRegression :
  Factor.frickeContributionEqualsMinimumDepthDerived
    Factor.canonicalDuncanSwisherDeligneDepthContributionBoundary ≡ true
frickeEqualsMinimumDepthDerivedRegression = refl

supportLayerAlreadyClosedRegression :
  Depth.supportTheoremAlreadyClosed
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
supportLayerAlreadyClosedRegression = refl

record DuncanSwisherDeligneExponentMechanismBoundary : Set where
  field
    theorem12SingleOwnerRetained : Bool
    dworkRamifiedA1SharpnessDerived : Bool
    numericA1DepthTableRequired : Bool
    exceptionalPartialFractionDepthDerived : Bool
    p11BrandtToFullAutToDeligneBridgeConstructed : Bool
    HauptmodulUNBridgeConstructed : Bool
    FrickeContributionReexpressedAsDeligneDepth : Bool
    OggSupportProvedStrictlyCoarserThanExponent : Bool
    fullDworkPadicCyclesConstructionReproved : Bool

canonicalDuncanSwisherDeligneExponentMechanismBoundary :
  DuncanSwisherDeligneExponentMechanismBoundary
canonicalDuncanSwisherDeligneExponentMechanismBoundary = record
  { theorem12SingleOwnerRetained = true
  ; dworkRamifiedA1SharpnessDerived = true
  ; numericA1DepthTableRequired = false
  ; exceptionalPartialFractionDepthDerived = true
  ; p11BrandtToFullAutToDeligneBridgeConstructed = true
  ; HauptmodulUNBridgeConstructed = true
  ; FrickeContributionReexpressedAsDeligneDepth = true
  ; OggSupportProvedStrictlyCoarserThanExponent = true
  ; fullDworkPadicCyclesConstructionReproved = false
  }

module DASHI.Moonshine.DuncanSwisherDeligneExponentMechanismEverything where

------------------------------------------------------------------------
-- Focused convergence root for the quantitative post-Ogg mechanism.
--
-- PRIMARY SOURCE
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Chain now exposed:
--
--   supersingular automorphism type
--      -> Deligne n=1 first-pole depth
--      -> minimum depth d_min with 2 d_min = m_p
--      -> Fricke contribution d_min
--      -> singleton residual 2 d_min / multiple residual 0
--      -> Monster exponent depth
--
-- alongside the exact Hauptmodul identity
--
--   J_1 - J_p^+ = p U_p J_p^+
--
-- at signed Laurent-coefficient level.
--
-- Support is retained only as a strict coarse projection: p=5 and p=7 have
-- the same support observation but Monster exponents 9 and 6.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.DuncanSwisherTheorem12Exact as T12
import DASHI.Moonshine.DuncanSwisherMonsterExponentGeometryExact as Geometry
import DASHI.Moonshine.DuncanSwisherModularGeometryContributionWeldExact as Weld
import DASHI.Moonshine.MonsterExponentObserverRefinementExact as Refinement
import DASHI.Moonshine.DuncanSwisherFrickeHauptmodulUNExact as Hauptmodul
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Deligne
import DASHI.Moonshine.DuncanSwisherDeligneDepthContributionFactorizationExact as Factor
import DASHI.Moonshine.DuncanSwisherExponentDepthHighestAlphaEverything as Depth
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Monster
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as P11
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Canonical theorem owner retained.
------------------------------------------------------------------------

canonicalTheorem12StillOwnsSourceShapeRegression :
  T12.exactThreeCaseTheoremImported
    T12.canonicalDuncanSwisherTheorem12Boundary ≡ true
canonicalTheorem12StillOwnsSourceShapeRegression = refl

------------------------------------------------------------------------
-- Concrete exponent geometry / old #567 automorphism bridge.
------------------------------------------------------------------------

p11FullAutMinimumRegression :
  Geometry.p11FullAutomorphismOrder P11.j1728SS ≡ 4
p11FullAutMinimumRegression = Geometry.p11J1728FullAutIsFour

p11DeligneDepthRegression :
  Deligne.minimumFirstPoleDepth Deligne.p11MinimumWitness ≡ 2
p11DeligneDepthRegression = Deligne.p11MinimumDeligneDepthIsTwo

p11MonsterExponentIsDeligneDepthRegression :
  Monster.monsterOrderExponent Lane.p11
  ≡ Factor.p11DepthUnit
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

------------------------------------------------------------------------
-- Modular and geometric decompositions meet on the same exponent owner.
------------------------------------------------------------------------

p11ModularGeometryMeetRegression :
  2 * Weld.modularContributionTotal Lane.p11 Monster.p11AboveThree ≡ 4
p11ModularGeometryMeetRegression = Weld.p11ModularGeometryMeet

p5FrickeContributionRegression :
  Monster.frickeLevel (Monster.modularContribution Lane.p5 Monster.p5AboveThree) ≡ 3
p5FrickeContributionRegression = refl

p5PrimeLevelContributionRegression :
  Monster.primeLevel (Monster.modularContribution Lane.p5 Monster.p5AboveThree) ≡ 5
p5PrimeLevelContributionRegression = refl

p5SquareLevelContributionRegression :
  Monster.squareLevel (Monster.modularContribution Lane.p5 Monster.p5AboveThree) ≡ 1
p5SquareLevelContributionRegression = refl

------------------------------------------------------------------------
-- Strict support-vs-depth refinement.
------------------------------------------------------------------------

supportCannotRecoverP5AndP7DepthRegression :
  (decode : Bool → Nat) →
  decode (Refinement.supportObservation Refinement.probe5)
    ≡ Monster.monsterOrderExponent Lane.p5 →
  decode (Refinement.supportObservation Refinement.probe7)
    ≡ Monster.monsterOrderExponent Lane.p7 →
  ⊥
supportCannotRecoverP5AndP7DepthRegression =
  Refinement.supportCannotDecodeMonsterExponent

------------------------------------------------------------------------
-- The mechanism has moved below theorem-level valuation formulas.
------------------------------------------------------------------------

hauptmodulCoefficientBridgeConstructedRegression :
  Hauptmodul.coefficientDifferenceLawDerived
    Hauptmodul.canonicalDuncanSwisherFrickeHauptmodulUNBoundary ≡ true
hauptmodulCoefficientBridgeConstructedRegression = refl

deligneAutDepthBridgeConstructedRegression :
  Deligne.depthDoublesToFullAutomorphismOrderDerived
    Deligne.canonicalDuncanSwisherDeligneAutomorphismDepthBoundary ≡ true
deligneAutDepthBridgeConstructedRegression = refl

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
    concreteStructuralPrimeControlsConstructed : Bool
    p11BrandtToFullAutToDeligneBridgeConstructed : Bool
    HauptmodulUNBridgeConstructed : Bool
    FrickeContributionReexpressedAsDeligneDepth : Bool
    OggSupportProvedStrictlyCoarserThanExponent : Bool
    fullDelignePartialFractionExpansionReproved : Bool

canonicalDuncanSwisherDeligneExponentMechanismBoundary :
  DuncanSwisherDeligneExponentMechanismBoundary
canonicalDuncanSwisherDeligneExponentMechanismBoundary = record
  { theorem12SingleOwnerRetained = true
  ; concreteStructuralPrimeControlsConstructed = true
  ; p11BrandtToFullAutToDeligneBridgeConstructed = true
  ; HauptmodulUNBridgeConstructed = true
  ; FrickeContributionReexpressedAsDeligneDepth = true
  ; OggSupportProvedStrictlyCoarserThanExponent = true
  ; fullDelignePartialFractionExpansionReproved = false
  }

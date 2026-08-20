module DASHI.Moonshine.DuncanSwisherDworkSharpnessHighestAlphaRegression where

------------------------------------------------------------------------
-- Focused regression for the Dwork / Legendre sharpness dependency reversal.
--
-- The key point is not another 3/2/1 table.  These values are now theorem
-- outputs of
--
--   local J ramification + Dwork A1 valuation transfer.
--
-- The repository's older integer `VpDepth` machinery is now reused only as an
-- executable algebraic shadow of the same strict-minimum valuation interface.
-- It is not identified with Dwork's p-adic analytic carrier.  `VpTrue` also no
-- longer postulates a universal self-fuel adequacy theorem; stabilization is
-- proof-relevant.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.SeparatedLeadingValuationExact as Leading
import DASHI.Arithmetic.VpTrue as VpTrue
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Aut
import DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact as Dwork
import DASHI.Moonshine.DuncanSwisherDworkExceptionalPartialFractionSharpnessExact as PFSharp
import DASHI.Moonshine.DuncanSwisherDworkVpDepthShadowExact as Shadow
import DASHI.Moonshine.DuncanSwisherDelignePartialFractionMechanismExact as PF
import DASHI.Moonshine.DuncanSwisherLegendreRamificationDepthExact as Legendre
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11EichlerDeuringStackUnweightingExact as Stack11

jZeroA1DepthThreeRegression :
  let A = Dwork.publishedDworkLocalSharpnessData Aut.jZeroExceptional
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A) ≡ 3
jZeroA1DepthThreeRegression = Dwork.jZeroA1DepthIsThree

j1728A1DepthTwoRegression :
  let A = Dwork.publishedDworkLocalSharpnessData Aut.j1728Exceptional
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A) ≡ 2
j1728A1DepthTwoRegression = Dwork.j1728A1DepthIsTwo

ordinaryA1DepthOneRegression :
  let A = Dwork.publishedDworkLocalSharpnessData Aut.ordinaryType
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A) ≡ 1
ordinaryA1DepthOneRegression = Dwork.ordinaryA1DepthIsOne

p11JZeroA1EqualsBrandtWeightRegression :
  let A = Dwork.publishedDworkLocalSharpnessData (Legendre.p11AutType Geo.jZeroSS)
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A)
      ≡ Stack11.p11MonodromyWeight Geo.jZeroSS
p11JZeroA1EqualsBrandtWeightRegression =
  Dwork.p11A1DepthIsBrandtMonodromyWeight Geo.jZeroSS

p11J1728A1EqualsBrandtWeightRegression :
  let A = Dwork.publishedDworkLocalSharpnessData (Legendre.p11AutType Geo.j1728SS)
  in Ramified.valuation (Dwork.padicValuation A) (Dwork.A1Coefficient A)
      ≡ Stack11.p11MonodromyWeight Geo.j1728SS
p11J1728A1EqualsBrandtWeightRegression =
  Dwork.p11A1DepthIsBrandtMonodromyWeight Geo.j1728SS

p5TotalPartialFractionDepthThreeRegression :
  let S = PFSharp.publishedExceptionalDworkPartialFractionSeparation PF.prime5
  in Leading.valuation (PFSharp.additiveValuation S) (PFSharp.pJ1Up S) ≡ 3
p5TotalPartialFractionDepthThreeRegression = PFSharp.p5TotalDepthIsThree

p7TotalPartialFractionDepthTwoRegression :
  let S = PFSharp.publishedExceptionalDworkPartialFractionSeparation PF.prime7
  in Leading.valuation (PFSharp.additiveValuation S) (PFSharp.pJ1Up S) ≡ 2
p7TotalPartialFractionDepthTwoRegression = PFSharp.p7TotalDepthIsTwo

p11TotalPartialFractionDepthTwoRegression :
  let S = PFSharp.publishedExceptionalDworkPartialFractionSeparation PF.prime11
  in Leading.valuation (PFSharp.additiveValuation S) (PFSharp.pJ1Up S) ≡ 2
p11TotalPartialFractionDepthTwoRegression = PFSharp.p11TotalDepthIsTwo

------------------------------------------------------------------------
-- Executable integer shadow: same strict-minimum algebra, different carrier.
------------------------------------------------------------------------

p5VpDepthShadowThreeRegression :
  Leading.valuation Shadow.p5Valuation 750 ≡ 3
p5VpDepthShadowThreeRegression = Shadow.p5TotalDepth

p7VpDepthShadowTwoRegression :
  Leading.valuation Shadow.p7Valuation 392 ≡ 2
p7VpDepthShadowTwoRegression = Shadow.p7TotalDepth

p11VpDepthShadowTwoRegression :
  Leading.valuation Shadow.p11Valuation 1452 ≡ 2
p11VpDepthShadowTwoRegression = Shadow.p11TotalDepth

vpTrueNoLongerPostulatesGlobalAdequacyRegression :
  VpTrue.globalFuelAdequacyPostulated VpTrue.canonicalVpTrueBoundary ≡ false
vpTrueNoLongerPostulatesGlobalAdequacyRegression = refl

vpDepthShadowNotPromotedToDworkCarrierRegression :
  Shadow.DworkPadicCarrierConstructedHere
    Shadow.canonicalDuncanSwisherDworkVpDepthShadowBoundary ≡ false
vpDepthShadowNotPromotedToDworkCarrierRegression = refl

numericA1TableNotAuthorityRegression :
  Dwork.numericA1DepthTableImportedSeparately
    Dwork.canonicalDuncanSwisherDworkRamifiedA1SharpnessBoundary ≡ false
numericA1TableNotAuthorityRegression = refl

literalA1PowerFactorizationNotAssumedRegression :
  Dwork.literalA1PowerFactorizationAssumed
    Dwork.canonicalDuncanSwisherDworkRamifiedA1SharpnessBoundary ≡ false
literalA1PowerFactorizationNotAssumedRegression = refl

fullDworkCycleConstructionStillOpenRegression :
  Dwork.fullDworkPadicCyclesConstructionReproved
    Dwork.canonicalDuncanSwisherDworkRamifiedA1SharpnessBoundary ≡ false
fullDworkCycleConstructionStillOpenRegression = refl

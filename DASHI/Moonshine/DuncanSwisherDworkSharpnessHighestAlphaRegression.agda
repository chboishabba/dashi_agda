module DASHI.Moonshine.DuncanSwisherDworkSharpnessHighestAlphaRegression where

------------------------------------------------------------------------
-- Focused regression for the Dwork / Legendre sharpness dependency reversal.
--
-- The key point is not another 3/2/1 table.  These values are now theorem
-- outputs of
--
--   local J ramification + Dwork A1 valuation transfer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.SeparatedLeadingValuationExact as Leading
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Aut
import DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact as Dwork
import DASHI.Moonshine.DuncanSwisherDworkExceptionalPartialFractionSharpnessExact as PFSharp
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

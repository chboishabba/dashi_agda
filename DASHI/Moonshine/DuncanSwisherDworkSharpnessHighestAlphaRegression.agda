module DASHI.Moonshine.DuncanSwisherDworkSharpnessHighestAlphaRegression where

------------------------------------------------------------------------
-- Focused regression for the Dwork / Legendre sharpness dependency reversal.
--
-- Exceptional 3/2 exponents are algebraic outputs of the exact Legendre
-- j-factorization.  Finite residue-unit inputs are explicit for all exceptional
-- p=5,7,11 branches, and the preferred local producer derives both unit depth
-- and branch depth from residue/simple-root data.
--
-- The remaining analytic boundary is therefore split into:
--
--   actual p-adic lift/local-coordinate factorization
--   + Dwork n=1 A1 valuation transfer.
--
-- The repository's older integer `VpDepth` machinery is reused only as an
-- executable algebraic shadow.  It is not identified with Dwork's p-adic
-- analytic carrier; stabilization is proof-relevant.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.SeparatedLeadingValuationExact as Leading
import DASHI.Arithmetic.VpTrue as VpTrue
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Aut
import DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact as Dwork
import DASHI.Moonshine.DuncanSwisherDworkExceptionalPartialFractionSharpnessExact as PFSharp
import DASHI.Moonshine.DuncanSwisherDworkVpDepthShadowExact as Shadow
import DASHI.Moonshine.DuncanSwisherDworkExceptionalAnalyticCutsetExact as AnalyticCut
import DASHI.Moonshine.DuncanSwisherDelignePartialFractionMechanismExact as PF
import DASHI.Moonshine.DuncanSwisherLegendreRamificationDepthExact as Legendre
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as JFactor
import DASHI.Moonshine.LegendreExceptionalBranchSimpleRootExact as SimpleRoot
import DASHI.Moonshine.LegendreJExceptionalLocalValuationCutsetExact as LocalCut
import DASHI.Moonshine.LegendreJExceptionalResidueLocalProducerExact as Preferred
import DASHI.Moonshine.P5LegendreJZeroF25ResidueExact as P5Residue
import DASHI.Moonshine.P7P11LegendreJ1728ResidueCertificatesExact as P7P11Residue
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

------------------------------------------------------------------------
-- Exceptional exponent/residue/local-parameter cutset.
------------------------------------------------------------------------

jZeroExponentAlgebraicRegression :
  JFactor.exceptionalRamificationExponent JFactor.jZeroQuadraticBranch ≡ 3
jZeroExponentAlgebraicRegression = JFactor.jZeroRamificationExponentIsThree

j1728ExponentAlgebraicRegression :
  JFactor.exceptionalRamificationExponent JFactor.j1728LambdaMinusTwo ≡ 2
j1728ExponentAlgebraicRegression = refl

simpleRootResidueUnitStillNotFabricatedRegression :
  SimpleRoot.residueNonzeroImpliesPadicUnitConstructedHere
    SimpleRoot.canonicalLegendreExceptionalBranchSimpleRootBoundary ≡ false
simpleRootResidueUnitStillNotFabricatedRegression = refl

p5FiniteResidueInputsCompleteRegression :
  P5Residue.finiteResidueUnitInputsComplete
    P5Residue.canonicalP5LegendreJZeroF25ResidueBoundary ≡ true
p5FiniteResidueInputsCompleteRegression = refl

p7p11FiniteResidueInputsCompleteRegression :
  P7P11Residue.residueUnitInputsAvailableForP7P11
    P7P11Residue.canonicalP7P11LegendreJ1728ResidueCertificatesBoundary ≡ true
p7p11FiniteResidueInputsCompleteRegression = refl

preferredOuterUnitDepthIsDerivedRegression :
  Preferred.outerUnitDepthPrimitive
    Preferred.canonicalLegendreJExceptionalResidueLocalProducerBoundary ≡ false
preferredOuterUnitDepthIsDerivedRegression = refl

preferredBranchDepthOneIsDerivedRegression :
  Preferred.branchDepthOnePrimitive
    Preferred.canonicalLegendreJExceptionalResidueLocalProducerBoundary ≡ false
preferredBranchDepthOneIsDerivedRegression = refl

freeRamificationExponentRejectedRegression :
  LocalCut.freeNumericRamificationExponentAcceptedFromSource
    LocalCut.canonicalLegendreJExceptionalLocalValuationCutsetBoundary ≡ false
freeRamificationExponentRejectedRegression = refl

A1TransferSeparatedFromGeometryRegression :
  AnalyticCut.A1ValuationTransferAuthoritySeparated
    AnalyticCut.canonicalDuncanSwisherDworkExceptionalAnalyticCutsetBoundary ≡ true
A1TransferSeparatedFromGeometryRegression = refl

numericA1DepthNotSuppliedByNewCutsetRegression :
  AnalyticCut.numericA1DepthSuppliedBySource
    AnalyticCut.canonicalDuncanSwisherDworkExceptionalAnalyticCutsetBoundary ≡ false
numericA1DepthNotSuppliedByNewCutsetRegression = refl

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

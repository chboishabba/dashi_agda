module DASHI.Moonshine.DuncanSwisherDworkPublishedAnalyticCompletionRegression where

------------------------------------------------------------------------
-- Focused regression for the three-object p>3 Dwork/Legendre completion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.LegendreExceptionalCertifiedResiduePointsExact as Residues
import DASHI.Moonshine.LegendreExceptionalPadicHenselConstructionExact as Hensel
import DASHI.Moonshine.DuncanSwisherDworkPublishedCoefficientFamilyExact as Family
import DASHI.Moonshine.DuncanSwisherDworkPublishedFirstPoleSharpnessExact as Sharp
import DASHI.Moonshine.DuncanSwisherDworkPublishedAnalyticCompletionExact as Complete

p5CertifiedResidueAdaptedRegression :
  Residues.p5JZeroPointAdapted
    Residues.canonicalLegendreExceptionalCertifiedResiduePointsBoundary ≡ true
p5CertifiedResidueAdaptedRegression = refl

p7CertifiedResidueAdaptedRegression :
  Residues.p7J1728PointAdapted
    Residues.canonicalLegendreExceptionalCertifiedResiduePointsBoundary ≡ true
p7CertifiedResidueAdaptedRegression = refl

p11CertifiedResidueAdaptedRegression :
  Residues.p11J1728PointAdapted
    Residues.canonicalLegendreExceptionalCertifiedResiduePointsBoundary ≡ true
p11CertifiedResidueAdaptedRegression = refl

henselCentreDefinedFromFiniteCentreRegression :
  Hensel.liftedCentreDefinedFromFiniteCentre
    Hensel.canonicalLegendreExceptionalPadicHenselConstructionBoundary ≡ true
henselCentreDefinedFromFiniteCentreRegression = refl

actualLiftConstructedRegression :
  Hensel.exceptionalPadicLiftRecordConstructed
    Hensel.canonicalLegendreExceptionalPadicHenselConstructionBoundary ≡ true
actualLiftConstructedRegression = refl

lambdaMinusLambda0DerivedRegression :
  Hensel.lambdaMinusLambda0EqualsPiTimesOneDerived
    Hensel.canonicalLegendreExceptionalPadicHenselConstructionBoundary ≡ true
lambdaMinusLambda0DerivedRegression = refl

nearbyResidueDerivedRegression :
  Hensel.nearbyResidueDerivedFromResidueHomomorphism
    Hensel.canonicalLegendreExceptionalPadicHenselConstructionBoundary ≡ true
nearbyResidueDerivedRegression = refl

actualCoefficientFamilyConstructedRegression :
  Family.coefficientFamilyConstructedForEveryPositivePoleOrder
    Family.canonicalDuncanSwisherDworkPublishedCoefficientFamilyBoundary ≡ true
actualCoefficientFamilyConstructedRegression = refl

A1NotStoredSeparatelyRegression :
  Family.A1StoredIndependently
    Family.canonicalDuncanSwisherDworkPublishedCoefficientFamilyBoundary ≡ false
A1NotStoredSeparatelyRegression = refl

deepDworkSharpnessOnActualFamilyRegression :
  Sharp.deepDworkN1SharpnessImportedOnActualFamily
    Sharp.canonicalDuncanSwisherDworkPublishedFirstPoleSharpnessBoundary ≡ true
deepDworkSharpnessOnActualFamilyRegression = refl

targetEqualityNotImportedRegression :
  Sharp.desiredA1EqualsJDepthImported
    Sharp.canonicalDuncanSwisherDworkPublishedFirstPoleSharpnessBoundary ≡ false
targetEqualityNotImportedRegression = refl

targetEqualityDerivedRegression :
  Sharp.A1EqualsLocalJDepthDerived
    Sharp.canonicalDuncanSwisherDworkPublishedFirstPoleSharpnessBoundary ≡ true
targetEqualityDerivedRegression = refl

allThreeRequestedObjectsClosedRegression :
  Complete.threeRequestedObjectsClosedAtPublishedSourceBoundaries
    Complete.canonicalDuncanSwisherDworkPublishedAnalyticCompletionBoundary ≡ true
allThreeRequestedObjectsClosedRegression = refl

fullDworkCyclesNotOverclaimedRegression :
  Complete.fullDworkCyclesReproved
    Complete.canonicalDuncanSwisherDworkPublishedAnalyticCompletionBoundary ≡ false
fullDworkCyclesNotOverclaimedRegression = refl

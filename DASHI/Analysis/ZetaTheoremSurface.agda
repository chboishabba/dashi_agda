module DASHI.Analysis.ZetaTheoremSurface where

-- Canonical public surface for the current zeta lane.
--
-- Exact rational samples and visualisation receipts are exported together
-- with the 3-adic geometric-series distinction, finite prime-counting and
-- prime-power arithmetic, the fail-closed analytic promotion gate, the
-- modular Millennium-level DASHI-to-Weil-square theorem ladder, and the 2026
-- reflection-orbit / Hermitian-defect architecture motivated by Alpöge--Furman.

open import DASHI.Analysis.AbelZeta public
open import DASHI.Analysis.ZetaVisualization public
open import DASHI.Analysis.ThreeAdicGeometricSeries public
open import DASHI.Analysis.RiemannZetaProgramBoundary public
open import DASHI.Analysis.RiemannAnalyticSubstrate public
open import DASHI.Analysis.WeilTestSpace public

open import DASHI.Analysis.RiemannReflectionOrbitDefectExact public
open import DASHI.Analysis.RiemannReflectionPairBlockExact public
open import DASHI.Analysis.RiemannWeilOffLineHyperbolicBlockExact public
  using
    ( HyperbolicPairBlock
    ; multiplicity
    ; positiveIndexBeforePullback
    ; negativeIndexBeforePullback
    ; hyperbolicPairHasOnePositiveDirection
    ; hyperbolicPairHasOneNegativeDirection
    ; sourcePositiveIndexBudget
    ; sourceNegativeIndexBudget
    ; offLineCountIsTwoSourcePositiveBudgets
    ; sourcePositiveAndNegativeBudgetsEqual
    ; sourceSignatureCode
    ; nearFarSourceSignatureCollide
    ; sourceSignatureCannotDetermineSquaredDefect
    ; DistanceSensitiveOffLineAdapter
    ; WeilOffLineHyperbolicBoundary
    ; weilOffLineHyperbolicBoundary
    )
open import DASHI.Analysis.RiemannComplexPoissonPairEnergyExact public
  using
    ( PairEnergyLedger
    ; multiplicityPredecessor
    ; baselineSquareSum
    ; imaginaryChannelEnergy
    ; realChannelEnergy
    ; fullGridHermitianEnergy
    ; criticalHermitianBaseline
    ; pairBlockFrobeniusSquared
    ; criticalBlockFrobeniusSquared
    ; pairBlockFrobeniusExcess
    ; fullGridEnergyDecomposition
    ; pairBlockFrobeniusDecomposition
    ; criticalPairHasZeroFrobeniusExcess
    ; criticalPairRecoversBaselineFrobenius
    ; nearPairEnergy
    ; farPairEnergy
    ; nearPairFrobeniusIsTwenty
    ; farPairFrobeniusIsHundred
    ; nearPairExcessIsSixteen
    ; farPairExcessIsNinetySix
    ; holomorphicBaselineCannotDetermineHermitianEnergy
    ; ComplexPoissonCoercivityAdapter
    ; FiniteCompressionTransferAdapter
    ; HermitianArithmeticTransportAdapter
    ; ComplexPoissonPairEnergyBoundary
    ; complexPoissonPairEnergyBoundary
    )

-- Qualified 2026 frontier modules.  Keeping these qualified avoids projection
-- collisions while making every analytic seam part of the canonical zeta API.
import DASHI.Analysis.RiemannComplexPoissonChannelSplitExact
import DASHI.Analysis.RiemannComplexPoissonFiniteRetentionExact
import DASHI.Analysis.RiemannWeilPairKernelFrobeniusExact
import DASHI.Analysis.RiemannMixedChannelAlmostOrthogonalityExact
import DASHI.Analysis.RiemannPrimeSideExcessNormalizationExact
import DASHI.Analysis.RiemannHermitianDefectAssemblyExact
import DASHI.Analysis.RiemannHermitianDetectabilityGapExact
import DASHI.Analysis.RiemannHermitianExcessDetectabilityAssemblyExact
import DASHI.Analysis.RiemannHermitianPowerAmplificationExact
import DASHI.Analysis.RiemannHermitianLocalizationAmplificationExact
import DASHI.Analysis.RiemannArithmeticUnitarityRigidityBoundary
import DASHI.Analysis.RiemannHermitianEndgameTrichotomyExact
import DASHI.Analysis.RiemannHermitianDreamRouteExact
import DASHI.Analysis.RiemannReflectionC3OrbitShapeBridgeExact

open import DASHI.Analysis.PrimeCountingFunction public
  using
    ( PrimePredicate
    ; primeIndicator
    ; primeCountLE
    ; primeCountLT
    ; primeCountStep
    ; primeCountAtPrime
    ; primeCountAtNonprime
    ; primesUpTo
    ; primeListCountExact
    ; primeCountSymmetricTwice
    ; primeCountSymmetricTwiceDefinition
    ; PrimeCountingFiniteBoundary
    ; primeCountingFiniteBoundary
    )
open import DASHI.Analysis.NatPrimeCountingInstance public
  using
    ( natPrimePredicate
    ; natPrimeIndicator
    ; natPrimeCountLE
    ; natPrimesUpTo
    ; natPrimeCountSymmetricTwice
    ; natPrimeEnumerationCountExact
    )
open import DASHI.Analysis.ChebyshevPrimeCounting public
  using
    ( PrimeLogWeightKernel
    ; chebyshevThetaLE
    ; chebyshevPsiLE
    ; ChebyshevPrimeOwnership
    ; IntegerRootFloor
    ; ChebyshevPrimePowerIdentity
    ; ChebyshevFiniteBoundary
    ; chebyshevFiniteBoundary
    )
open import DASHI.Analysis.RiemannPrimePowerCounting public
  using
    ( PrimePowerOccurrence
    ; PrimePowerCountingScalar
    ; SymmetricPrimePowerEnumeration
    ; PrimePowerEnumerationFamily
    ; riemannPrimePowerCount0
    ; RiemannPrimePowerCountIdentity
    ; MobiusScalarKernel
    ; MobiusPrimeCountInversion
    ; RiemannPrimePowerCountingBoundary
    ; riemannPrimePowerCountingBoundary
    )
open import DASHI.Analysis.RiemannPrimePowerMangoldtIdentity public
  using
    ( MangoldtLogQuotientKernel
    ; mangoldtLogQuotientTerm
    ; mangoldtLogQuotientSumLE
    ; mangoldtPrimePowerCount0
    ; RiemannPrimePowerMangoldtIdentity
    ; RiemannPrimePowerMangoldtBoundary
    ; riemannPrimePowerMangoldtBoundary
    )

open import DASHI.Analysis.RiemannPrimePowerArithmetic public
open import DASHI.Analysis.RiemannFiniteExplicitFormulaBoundary public
open import DASHI.Analysis.WeightedValuationVonMangoldtBoundary public
open import DASHI.Analysis.RiemannExplicitFormula public
open import DASHI.Analysis.RiemannFormulaAnalyticCompatibility public
open import DASHI.Analysis.DashiWeilExactIdentification public
open import DASHI.Analysis.DashiWeilTermwiseBridge public
open import DASHI.Analysis.WeilPositivityCore public
open import DASHI.Analysis.WeilDensityClosure public
open import DASHI.Analysis.RiemannArithmeticCoercivity public
open import DASHI.Analysis.RiemannMillenniumAssembly public
open import DASHI.Analysis.RiemannWeilSquareAssembly public
  using (WeilSquareMillenniumAssembly; weilSquareAssemblyImpliesRH)
open import DASHI.Analysis.DashiWeilSquareBridge public
  using
    ( DashiWeilSquareEncoding
    ; DashiWeilSquareMillenniumAssembly
    ; dashiCoercivityImpliesSquarePositivity
    ; dashiWeilSquareAssemblyImpliesRH
    )
open import DASHI.Analysis.DashiWeightedValuationSquareCoercivity public
  using
    ( WeightedValuationSquareCoercivity
    ; WeightedValuationCoercivityMillenniumAssembly
    ; weightedValuationToArithmeticSquareDecomposition
    ; weightedValuationCoercivityImpliesRH
    )

import DASHI.Analysis.NatPrimeCountingExamples
import DASHI.Analysis.RiemannVonMangoldtSpecification
import DASHI.Analysis.RiemannVonMangoldtPrimeSide
import DASHI.Analysis.RiemannTrackedToVonMangoldtBridge
import DASHI.Analysis.RiemannPrimeExhaustion
import DASHI.Analysis.PrimeCountingAlgorithms
import DASHI.Analysis.PrimeCountingAnalyticBridge
import DASHI.Analysis.PrimeCountingTransforms
import DASHI.Analysis.PrimeCountingEstimateContracts
import DASHI.Analysis.WeilConvolutionSquare
import DASHI.Analysis.BombieriWeilTestBridge
import DASHI.Analysis.RiemannExplicitFormulaComponents
import DASHI.Analysis.RiemannWeilSquareCriterion
import DASHI.Analysis.RiemannWeilSquareCoercivity
import DASHI.Analysis.ZetaModularRegression
import DASHI.Analysis.DashiWeilRiemannBridge

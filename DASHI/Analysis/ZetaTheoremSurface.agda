module DASHI.Analysis.ZetaTheoremSurface where

-- Canonical public surface for the current zeta lane.
--
-- Exact rational samples and visualisation receipts are exported together
-- with the 3-adic geometric-series distinction, finite prime-counting and
-- prime-power arithmetic, the fail-closed analytic promotion gate, the
-- modular Millennium-level DASHI-to-Weil-square theorem ladder, and the 2026
-- reflection-orbit quotient/defect algebra motivated by Alpöge--Furman.

open import DASHI.Analysis.AbelZeta public
open import DASHI.Analysis.ZetaVisualization public
open import DASHI.Analysis.ThreeAdicGeometricSeries public
open import DASHI.Analysis.RiemannZetaProgramBoundary public
open import DASHI.Analysis.RiemannAnalyticSubstrate public
open import DASHI.Analysis.WeilTestSpace public

-- 2026 reflection-orbit / inverse-pair lane.  The first two modules construct
-- exact finite/discrete orbit algebra and residual diagnostics.  The
-- hyperbolic module records the source-native off-line pair signature used by
-- Alpöge--Furman's inertia argument and proves that this bare signature cannot
-- determine transverse squared defect.  None reconstructs the analytic Weil
-- Hermitian compression by itself.
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
    ; RiemannPrimePowerCountIdentity
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

-- Detailed arithmetic, algorithmic, analytic, transform, square-coercivity,
-- reflection/C3 comparison, and regression modules stay qualified here to
-- avoid exporting local helper combinators and overlapping projection names.
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

-- Retained for direct qualified imports by older callers, but not opened here:
-- its monolithic projections overlap names from the modular theorem ladder.
import DASHI.Analysis.DashiWeilRiemannBridge

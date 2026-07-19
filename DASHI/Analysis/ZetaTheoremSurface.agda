module DASHI.Analysis.ZetaTheoremSurface where

-- Canonical public surface for the current zeta lane.
--
-- Exact rational samples and visualisation receipts are exported together
-- with the 3-adic geometric-series distinction, the fail-closed analytic
-- promotion gate, the concrete prime-power/von-Mangoldt arithmetic lane, and
-- the modular Millennium-level DASHI-to-Weil-square theorem ladder.

open import DASHI.Analysis.AbelZeta public
open import DASHI.Analysis.ZetaVisualization public
open import DASHI.Analysis.ThreeAdicGeometricSeries public
open import DASHI.Analysis.RiemannZetaProgramBoundary public
open import DASHI.Analysis.RiemannAnalyticSubstrate public
open import DASHI.Analysis.WeilTestSpace public
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

-- Detailed arithmetic, test-space, square-coercivity, and regression modules
-- stay qualified here to avoid exporting their local helper combinators.
import DASHI.Analysis.RiemannVonMangoldtSpecification
import DASHI.Analysis.RiemannVonMangoldtPrimeSide
import DASHI.Analysis.RiemannTrackedToVonMangoldtBridge
import DASHI.Analysis.RiemannPrimeExhaustion
import DASHI.Analysis.WeilConvolutionSquare
import DASHI.Analysis.BombieriWeilTestBridge
import DASHI.Analysis.RiemannExplicitFormulaComponents
import DASHI.Analysis.RiemannWeilSquareCriterion
import DASHI.Analysis.RiemannWeilSquareCoercivity
import DASHI.Analysis.ZetaModularRegression

-- Retained for direct qualified imports by older callers, but not opened here:
-- its monolithic projections overlap names from the modular theorem ladder.
import DASHI.Analysis.DashiWeilRiemannBridge

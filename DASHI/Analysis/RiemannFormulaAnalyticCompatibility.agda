module DASHI.Analysis.RiemannFormulaAnalyticCompatibility where

-- Exact carrier ownership between the completed-zeta analytic substrate and
-- the Riemann-Weil explicit-formula surface.

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula

record RiemannFormulaAnalyticCompatibility
  (analytic : AnalyticSubstrate)
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space) : Set₁ where
  field
    testCarrierMatchesMellin :
      WeilTestSpace.Test space
      ≡
      GammaMellinLayer.Test
        (AnalyticSubstrate.gammaMellin analytic)

    scalarCarrierMatchesReal :
      WeilTestSpace.Scalar space
      ≡
      ComplexAnalyticCarrier.Real
        (AnalyticSubstrate.carrier analytic)

    PrimePowerTermUsesOwnedEulerProduct : Set
    ArchimedeanTermUsesOwnedGamma : Set
    SpectralFormUsesOwnedXiZeros : Set

    primePowerTermUsesOwnedEulerProduct :
      PrimePowerTermUsesOwnedEulerProduct
    archimedeanTermUsesOwnedGamma :
      ArchimedeanTermUsesOwnedGamma
    spectralFormUsesOwnedXiZeros :
      SpectralFormUsesOwnedXiZeros

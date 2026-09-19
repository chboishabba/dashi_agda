module DASHI.Moonshine.JInvariantBishopLatticeEisensteinAbsoluteConvergenceFrontierExact where

------------------------------------------------------------------------
-- CURRENT PREFERRED FRONTIER FOR CONCRETE BISHOP LATTICE EISENSTEIN
--
-- This ledger is intentionally theorem-structure-aware.  It records the
-- concrete payments now owned on the preferred setoid/punctured route and
-- keeps the remaining absolute-summability/Fourier obligations fail-closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Analysis.BishopComplexReciprocalExact
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact
import DASHI.Moonshine.JInvariantPuncturedLatticeReindexExact
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact
import DASHI.Moonshine.JInvariantBishopLatticeDenominatorCoercivityExact
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact

data BishopLatticeEisensteinResidual : Set where
  missingSquareShellRadiusSquareLowerBound :
    BishopLatticeEisensteinResidual
  missingCoercivityToReciprocalPowerMajorant :
    BishopLatticeEisensteinResidual
  missingFiniteShellAbsoluteFoldDomination :
    BishopLatticeEisensteinResidual
  missingPuncturedAbsoluteSumCompletion :
    BishopLatticeEisensteinResidual
  missingConcreteG4G6Normalization :
    BishopLatticeEisensteinResidual
  missingQSeriesLatticeFourierSameObject :
    BishopLatticeEisensteinResidual

record BishopLatticeEisensteinAbsoluteConvergenceFrontier : Set where
  field
    bishopComplexReciprocalExact : Bool
    literalIntegerEmbeddingExact : Bool
    literalMτPlusNExact : Bool
    literalInversePowerSummandExact : Bool
    upperHalfPlaneDenominatorNonzeroExact : Bool

    sl2zPuncturedLatticeReindexingExact : Bool
    uniqueFiniteSquareCoverExact : Bool
    squareCoverCardinalityExact : Bool
    squareCoverDecoderComplete : Bool
    shellCardinalityBoundBySquareExact : Bool

    twoDimensionalBishopCauchyExact : Bool
    denominatorCoordinateIdentitiesExact : Bool
    divisionFreeLatticeCoercivityExact : Bool

    squareShellRadiusSquareLowerBoundExact : Bool
    reciprocalPowerShellMajorantExact : Bool
    finiteShellAbsoluteFoldDominationExact : Bool
    bishopBaselBackendAlreadyOwned : Bool
    puncturedAbsoluteSumConstructed : Bool

    explicitG4G6NormalizationPaid : Bool
    qSeriesEqualsNormalizedLatticeE4E6 : Bool
    qSeriesModularityCompilerReady : Bool

    firstResidual : BishopLatticeEisensteinResidual

open BishopLatticeEisensteinAbsoluteConvergenceFrontier public

canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier :
  BishopLatticeEisensteinAbsoluteConvergenceFrontier
canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier = record
  { bishopComplexReciprocalExact = true
  ; literalIntegerEmbeddingExact = true
  ; literalMτPlusNExact = true
  ; literalInversePowerSummandExact = true
  ; upperHalfPlaneDenominatorNonzeroExact = true

  ; sl2zPuncturedLatticeReindexingExact = true
  ; uniqueFiniteSquareCoverExact = true
  ; squareCoverCardinalityExact = true
  ; squareCoverDecoderComplete = true
  ; shellCardinalityBoundBySquareExact = true

  ; twoDimensionalBishopCauchyExact = true
  ; denominatorCoordinateIdentitiesExact = true
  ; divisionFreeLatticeCoercivityExact = true

  ; squareShellRadiusSquareLowerBoundExact = false
  ; reciprocalPowerShellMajorantExact = false
  ; finiteShellAbsoluteFoldDominationExact = false
  ; bishopBaselBackendAlreadyOwned = true
  ; puncturedAbsoluteSumConstructed = false

  ; explicitG4G6NormalizationPaid = false
  ; qSeriesEqualsNormalizedLatticeE4E6 = false
  ; qSeriesModularityCompilerReady = true

  ; firstResidual = missingSquareShellRadiusSquareLowerBound
  }

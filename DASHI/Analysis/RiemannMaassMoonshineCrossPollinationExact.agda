module DASHI.Analysis.RiemannMaassMoonshineCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Enrico Bombieri,
-- "Problems of the Millennium: The Riemann Hypothesis",
-- Clay Mathematics Institute problem description.  No DOI assigned.
--
-- Richard E. Borcherds,
-- "Monstrous moonshine and monstrous Lie superalgebras".
-- DOI: 10.1007/BF01232032.
--
-- DASHI CONTRIBUTION
--
-- Cross-pollinate the new zeta/xi surface with the repository's existing Abel
-- special values, Maaß Fourier/residual/enclosure architecture, and graded-VOA
-- moonshine surface.  The module records the exact bridges that would be needed
-- for a Hilbert--Pólya or trace-formula route and proves that a supplied
-- zero/eigenvalue correspondence places represented zeros on the critical line.
--
-- Abel regularised values, a certified Maaß eigenvalue, modular VOA characters,
-- Selberg-type trace formulae and the Riemann zeta explicit formula are kept
-- type-distinct.  None implies RH without the additional bridge fields.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Analysis.AbelZeta as Abel
import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.MaassSpectralCertification as MSC
import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as RX
import DASHI.Mathematics.NumberTheory.RiemannCompletedZetaBoundary as RZ
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA

record MaassRiemannSpectralBridge
    (zetaData : RZ.CompletedZetaData) : Setω where
  field
    maassDatum : MFC.ΓMaass
    maassCandidate : MSC.CandidateMaassForm maassDatum
    maassSpectralEnclosure : Set

    hilbertPolyaCandidate : RX.HilbertPolyaCandidate
    candidateEigenvalueIsMaassOrTransferSpectrum : Set
    candidateZeroIsActualXiZero : ∀ eigenvector →
      RX.isXiZero (RZ.completedZetaZeroSymmetry zetaData)
        (RX.associatedZero hilbertPolyaCandidate eigenvector)

    traceFormulaCarrier : Set
    primeSideMatchesRiemannPrimePowers : Set
    spectralSideMatchesAllNontrivialZeros : Set
    selfAdjointOperatorConstruction : Set
    spectralCompleteness : Set

open MaassRiemannSpectralBridge public

representedSpectralZerosAreCritical :
  ∀ zetaData (bridge : MaassRiemannSpectralBridge zetaData) eigenvector →
  RX.CriticalLine
    (RX.associatedZero (hilbertPolyaCandidate bridge) eigenvector)
representedSpectralZerosAreCritical zetaData bridge eigenvector =
  RX.hilbertPolyaCandidateZerosLieOnCriticalLine
    (hilbertPolyaCandidate bridge) eigenvector

record VOARiemannBridge
    (zetaData : RZ.CompletedZetaData) : Setω where
  field
    Scalar GroupCarrier : Set
    gradedVOAAction : GVOA.VOAWithGroupAction GroupCarrier Scalar
    exactGradedTrace : GVOA.ExactGradedTrace gradedVOAAction
    modularCharacterTheorem : Set
    mellinOrThetaTransform : Set
    transformedSeriesEqualsCompletedZeta : Set
    positivityOrSelfAdjointnessInput : Set
    allNontrivialZerosCaptured : Set

record AbelZetaReuse : Set where
  field
    zetaAtZero : DASHI.Core.Q.ℚ
    zetaAtMinusOne : DASHI.Core.Q.ℚ
    zeroValueReused : zetaAtZero ≡ Abel.zeta0
    minusOneValueReused : zetaAtMinusOne ≡ Abel.zetaMinus1
  where
    open import DASHI.Core.Q

data AnalyticOwner : Set where
  abelRegularisedSpecialValue
  riemannMeromorphicContinuation
  maassLaplacianSpectrum
  selbergTraceFormula
  voaModularCharacter
  riemannPrimeZeroExplicitFormula
  hilbertPolyaSpectrum

abelValueIsNotContinuation :
  abelRegularisedSpecialValue ≡ riemannMeromorphicContinuation → ⊥
abelValueIsNotContinuation ()

maassSpectrumIsNotRiemannZeroSpectrum :
  maassLaplacianSpectrum ≡ hilbertPolyaSpectrum → ⊥
maassSpectrumIsNotRiemannZeroSpectrum ()

voaModularityIsNotRH :
  voaModularCharacter ≡ hilbertPolyaSpectrum → ⊥
voaModularityIsNotRH ()

selbergAndRiemannExplicitFormulaAreDistinct :
  selbergTraceFormula ≡ riemannPrimeZeroExplicitFormula → ⊥
selbergAndRiemannExplicitFormulaAreDistinct ()

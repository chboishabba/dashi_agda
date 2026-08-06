module DASHI.Analysis.SharedFiniteSpectralCertificationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", second edition.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Dennis Hejhal,
-- "The Selberg Trace Formula for PSL(2,R), Volume 2".
-- DOI: 10.1007/BFb0061293.
--
-- DASHI CONTRIBUTION
--
-- Introduce a shared spectral-enclosure certificate and adapt the existing
-- theorem-critical Maaß residual-to-enclosure owner to it without discarding
-- any analytic hypotheses.  The exact 2-by-2 self-adjoint seed is instantiated
-- as a finite Hilbert--Pólya candidate, an exact Hodge-Laplacian mode table and
-- a finite transfer-Hamiltonian mass-gap witness.
--
-- These finite instances certify their own spectra.  They do not identify the
-- Maaß spectrum with Riemann zeros, prove convergence of Hilbert--Pólya
-- approximants, or transfer a finite-volume Yang--Mills gap to the continuum.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)

import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.MaassSpectralCertification as MSC
import DASHI.Analysis.Maass.ValidatedNumericsArtifact as VNA
import DASHI.Analysis.Maass.CuspContinuousSpectrumSeparation as CCS
import DASHI.Analysis.Maass.ResidualToSpectralEnclosureTheorem as Maass
import DASHI.Mathematics.LinearAlgebra.RationalTwoByTwoSelfAdjointSpectralExact as Spectral
import DASHI.Mathematics.LinearAlgebra.RationalThreeWayHodgeDecompositionExact as Hodge
import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as Riemann

record SharedSpectralEnclosure
    (Candidate Genuine Window Radius : Set)
    (inWindow : Genuine → Window → Set)
    (candidateWithin : Candidate → Genuine → Radius → Set) : Set₁ where
  field
    candidate : Candidate
    genuine : Genuine
    window : Window
    radius : Radius
    inclusion : inWindow genuine window ×
      candidateWithin candidate genuine radius
    uniqueness : ∀ first second →
      inWindow first window → inWindow second window → first ≡ second

open SharedSpectralEnclosure public

------------------------------------------------------------------------
-- Exact adapter from the repository's theorem-critical Maaß owner.
------------------------------------------------------------------------

maassTheoremToSharedEnclosure :
  ∀ {Γ : MFC.ΓMaass}
    (candidate : MSC.CandidateMaassForm Γ)
    (GenuineForm SpectralInterval Radius Cusp SpectralParameter ConstantTerm : Set)
    (eigenvalueIn : GenuineForm → SpectralInterval → Set)
    (candidateWithin : MSC.CandidateMaassForm Γ → GenuineForm → Radius → Set)
    (EisensteinFamily : Cusp → SpectralParameter → Set)
    (constantTerm : MSC.CandidateMaassForm Γ → Cusp → ConstantTerm)
    (constantTermIsZero : ConstantTerm → Set)
    (continuousProjectionSmall : MSC.CandidateMaassForm Γ → Set)
    (windowAvoidsResidualSpectrum : SpectralInterval → Set)
    (windowSeparatedFromContinuousSpectrum : SpectralInterval → Set) →
  Maass.MaassSpectralEnclosureTheorem candidate
    GenuineForm SpectralInterval Radius Cusp SpectralParameter ConstantTerm
    eigenvalueIn candidateWithin EisensteinFamily constantTerm
    constantTermIsZero continuousProjectionSmall
    windowAvoidsResidualSpectrum windowSeparatedFromContinuousSpectrum →
  SharedSpectralEnclosure
    (MSC.CandidateMaassForm Γ) GenuineForm SpectralInterval Radius
    eigenvalueIn candidateWithin
maassTheoremToSharedEnclosure candidate
    GenuineForm SpectralInterval Radius Cusp SpectralParameter ConstantTerm
    eigenvalueIn candidateWithin EisensteinFamily constantTerm
    constantTermIsZero continuousProjectionSmall
    windowAvoidsResidualSpectrum windowSeparatedFromContinuousSpectrum theorem =
  record
    { candidate = candidate
    ; genuine = proj₁ (Maass.spectralInclusion theorem)
    ; window = Maass.spectralWindow theorem
    ; radius = Maass.isolationRadius theorem
    ; inclusion = proj₂ (Maass.spectralInclusion theorem)
    ; uniqueness = Maass.uniquenessInWindow theorem
    }

------------------------------------------------------------------------
-- Finite Hilbert--Pólya candidate from the exact two-point spectrum.
------------------------------------------------------------------------

data TwoPointMode : Set where
  modeTwo modeFive : TwoPointMode

twoPointEigenvalue : TwoPointMode → ℚ
twoPointEigenvalue modeTwo = Spectral.two
twoPointEigenvalue modeFive = Spectral.five

twoPointEigenpair :
  (mode : TwoPointMode) → Spectral.ExactEigenpair Spectral.diagonalTwoFive
twoPointEigenpair modeTwo = Spectral.eigenpairTwo
twoPointEigenpair modeFive = Spectral.eigenpairFive

twoPointHilbertPolyaCandidate : Riemann.HilbertPolyaCandidate
twoPointHilbertPolyaCandidate = record
  { Eigenvector = TwoPointMode
  ; eigenvalue = twoPointEigenvalue
  ; selfAdjointRealSpectrum = Spectral.SelfAdjoint Spectral.diagonalTwoFive
  ; associatedZero = λ mode →
      Riemann.complexCoordinate Riemann.half (twoPointEigenvalue mode)
  ; zeroCoordinateLaw = λ mode → refl
  }

finiteHilbertPolyaModesAreCritical :
  ∀ mode →
  Riemann.CriticalLine
    (Riemann.associatedZero twoPointHilbertPolyaCandidate mode)
finiteHilbertPolyaModesAreCritical mode =
  Riemann.hilbertPolyaCandidateZerosLieOnCriticalLine
    twoPointHilbertPolyaCandidate mode

finiteHilbertPolyaResidualsVanish :
  ∀ mode →
  Spectral.residual Spectral.diagonalTwoFive
    (twoPointEigenvalue mode)
    (Spectral.eigenvector (twoPointEigenpair mode))
  ≡ Spectral.zeroVector
finiteHilbertPolyaResidualsVanish mode =
  Spectral.exactEigenpairHasZeroResidual (twoPointEigenpair mode)

------------------------------------------------------------------------
-- Exact finite Hodge-Laplacian spectrum 1,0,1.
------------------------------------------------------------------------

data FiniteHodgeMode : Set where
  exactMode harmonicMode coexactMode : FiniteHodgeMode

hodgeModeVector : FiniteHodgeMode → Hodge.HodgeTriple
hodgeModeVector exactMode = Hodge.hodgeTriple 1ℚ 0ℚ 0ℚ
hodgeModeVector harmonicMode = Hodge.hodgeTriple 0ℚ 1ℚ 0ℚ
hodgeModeVector coexactMode = Hodge.hodgeTriple 0ℚ 0ℚ 1ℚ

hodgeModeEigenvalue : FiniteHodgeMode → ℚ
hodgeModeEigenvalue exactMode = 1ℚ
hodgeModeEigenvalue harmonicMode = 0ℚ
hodgeModeEigenvalue coexactMode = 1ℚ

scaleHodgeMode : ℚ → Hodge.HodgeTriple → Hodge.HodgeTriple
scaleHodgeMode = Hodge.scaleTriple

finiteHodgeModeEigenEquation : ∀ mode →
  Hodge.hodgeLaplacian (hodgeModeVector mode)
  ≡ scaleHodgeMode (hodgeModeEigenvalue mode) (hodgeModeVector mode)
finiteHodgeModeEigenEquation exactMode = refl
finiteHodgeModeEigenEquation harmonicMode = refl
finiteHodgeModeEigenEquation coexactMode = refl

finiteHodgeHarmonicKernel :
  Hodge.hodgeLaplacian (hodgeModeVector harmonicMode)
  ≡ Hodge.zeroTriple
finiteHodgeHarmonicKernel = refl

------------------------------------------------------------------------
-- Finite-volume transfer Hamiltonian witness.
------------------------------------------------------------------------

record FiniteTransferHamiltonianGap : Set₁ where
  field
    transferHamiltonian : Spectral.Matrix2
    selfAdjoint : Spectral.SelfAdjoint transferHamiltonian
    vacuumEigenpair : Spectral.ExactEigenpair transferHamiltonian
    firstExcitedEigenpair : Spectral.ExactEigenpair transferHamiltonian
    vacuumEnergy : ℚ
    firstExcitedEnergy : ℚ
    energyGap : ℚ
    gapEquation : firstExcitedEnergy ≡ vacuumEnergy + energyGap
    finiteVolumePositivity : Set
    volumeUniformityBoundary : Set
    continuumTransferBoundary : Set

canonicalFiniteTransferHamiltonianGap : FiniteTransferHamiltonianGap
canonicalFiniteTransferHamiltonianGap = record
  { transferHamiltonian = Spectral.diagonalTwoFive
  ; selfAdjoint = Spectral.diagonalTwoFiveSelfAdjoint
  ; vacuumEigenpair = Spectral.eigenpairTwo
  ; firstExcitedEigenpair = Spectral.eigenpairFive
  ; vacuumEnergy = Spectral.two
  ; firstExcitedEnergy = Spectral.five
  ; energyGap = Spectral.three
  ; gapEquation = Spectral.spectralDifference
  ; finiteVolumePositivity = ⊤
  ; volumeUniformityBoundary = ⊤
  ; continuumTransferBoundary = ⊤
  }

data SpectralPromotionLayer : Set where
  exactFiniteSpectrum
  certifiedMaassEnclosure
  finiteHilbertPolyaApproximant
  finiteYangMillsTransferGap
  continuumSpectrum

finiteAgreementIsNotContinuumCompletion :
  finiteHilbertPolyaApproximant ≡ continuumSpectrum →
  Data.Empty.⊥
finiteAgreementIsNotContinuumCompletion ()

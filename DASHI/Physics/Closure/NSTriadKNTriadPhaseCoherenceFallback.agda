module DASHI.Physics.Closure.NSTriadKNTriadPhaseCoherenceFallback where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Lucio M. Milanese; Nuno F. Loureiro; Stanislav Boldyrev.
-- Title: "Dynamic Phase Alignment in Navier-Stokes Turbulence".
-- Venue/year: Physical Review Letters 127 (2021), 274501.
-- DOI: 10.1103/PhysRevLett.127.274501.
-- arXiv: 2104.13518.
-- Uses: evidence that velocity-vorticity phase alignment carries information
-- not exhausted by helicity magnitude, with cos(alpha_k) scaling like k^-1
-- in the reported inertial-range simulations.
-- Relationship: numerical/statistical evidence only; no deterministic
-- arbitrary-state coercive inequality is imported.
--
-- Authors: Di Kang; Bartosz Protas; Miguel D. Bustamante.
-- Title: "Alignments of Triad Phases in 1D Burgers and 3D Navier-Stokes
-- Flows".
-- Venue/year: arXiv preprint, 2021.
-- DOI: 10.48550/arXiv.2105.09425.
-- Uses: evidence that a small subset of helical triads can carry the forward
-- flux in extreme three-dimensional Navier-Stokes computations.
-- Relationship: motivates retaining ordered triad phase amplitudes; it is not
-- promoted to a universal favourable-sign theorem.
--
-- Authors: DASHI repository contributors.
-- Title: "Triad-phase coherence fallback after scalar localized-helicity
-- falsification".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; the operator programme is DASHI-original.
-- Relationship: corrects a tempting but invalid diagnostic. Because curl is
-- Hermitian on the transverse fibre, <u_k, i k cross u_k> is real, so its
-- argument is only 0, pi, or undefined at zero. The phase-retaining object is
-- instead the complex ordered helical triad transfer amplitude before taking
-- its real part.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_<_)
open import Data.Product using (_×_)

import DASHI.Physics.Closure.NSTriadKNLocalizedHelicityExactReconnaissance as Exact
import DASHI.Physics.Closure.NSTriadKNLocalizedHelicityCommutatorProgram as Helical

record ComplexPhaseCarrier {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    zero : Scalar
    real imaginary : Scalar → Scalar
    conjugate : Scalar → Scalar
    Nonzero : Scalar → Set s

open ComplexPhaseCarrier public

record TriadPhaseCoherenceProgram
    {m v s : Level} : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    Mode : Set m
    Vector : Set v
    Scalar : Set s
    phaseCarrier : ComplexPhaseCarrier {s}

    projectHelical :
      Helical.HelicitySign → Mode → Vector → Vector
    orderedProjectedNonlinearity :
      Helical.HelicityTriple → Mode → Mode → Mode →
      Vector → Vector → Vector
    hermitianPairing : Vector → Vector → Scalar

    orderedTriadTransferAmplitude :
      Helical.HelicityTriple → Mode → Mode → Mode →
      Vector → Vector → Vector → Scalar

    orderedTriadTransferDefinition :
      ∀ signs p q k up uq uk →
      orderedTriadTransferAmplitude signs p q k up uq uk
      ≡ hermitianPairing
          (projectHelical (Helical.HelicityTriple.output signs) k uk)
          (orderedProjectedNonlinearity signs p q k up uq)

    energyTransfer : Scalar → Scalar
    helicityTransfer :
      Helical.HelicitySign → Mode → Scalar → Scalar

    retainComplexPhaseBeforeRealPart :
      ∀ signs p q k up uq uk → Scalar

    MatrixSymbol : Set s
    matrixSymbolActs : MatrixSymbol → Mode → Vector → Vector
    matrixSymbolHermitian : MatrixSymbol → Set s
    matrixSymbolRealityCompatible : MatrixSymbol → Set s
    matrixSymbolRotationEquivariant : MatrixSymbol → Set s
    physicalOperatorBasisFree : Set s

    CoherenceChart : Set s
    selectChart : Vector → CoherenceChart
    chartSymbol : CoherenceChart → MatrixSymbol
    chartSelectionEquivariant : Set s

    quadraticCorrection : CoherenceChart → Vector → Scalar
    literalCorrectionDerivative : CoherenceChart → Vector → Scalar
    chainRuleTriadIdentification : Set s
    viscousCorrectionIdentity : Set s
    symmetrisedOrbitIdentity : Set s

open TriadPhaseCoherenceProgram public

record TriadPhaseUniformAnalyticCutset
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff Chart State : Set c
    Scalar : Set s
    add : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s

    coerciveQuadraticReserve quarticReserve cubicMagnitude :
      Chart → Cutoff → State → Scalar

    rowSchurBound columnSchurBound : Chart → Cutoff → Scalar
    cutoffUniformRowSchur : ∀ chart cutoff → Set s
    cutoffUniformColumnSchur : ∀ chart cutoff → Set s
    lowHighCommutatorGain : ∀ chart cutoff state → Set s
    highLowCommutatorGain : ∀ chart cutoff state → Set s
    farLowRadiusGain : ∀ chart cutoff state → Set s
    farHighTailGain : ∀ chart cutoff state → Set s
    transitionBound : ∀ chart cutoff state → Set s

    signedClassContribution :
      Helical.GeometricClass → Helical.HelicityTriple →
      Chart → Cutoff → State → Scalar

    sameHelicitySignedBound : ∀ chart cutoff state → Set s
    mixedHelicitySignedBound : ∀ chart cutoff state → Set s
    pairedClassCancellation : ∀ chart cutoff state → Set s
    adverseRemainderSummable : ∀ chart cutoff state → Set s

    uniformQuarticBoundaryDomination :
      ∀ chart cutoff state →
      _≤_ (cubicMagnitude chart cutoff state)
           (add
             (coerciveQuadraticReserve chart cutoff state)
             (quarticReserve chart cutoff state))

open TriadPhaseUniformAnalyticCutset public

record PhaseFallbackFiniteEvidence : Set where
  constructor phase-evidence
  field
    resolvedRows : Exact.resolvedContributionCount ≡ 96
    retainedImaginaryCoefficient : 0 < 429

phaseFallbackFiniteEvidence : PhaseFallbackFiniteEvidence
phaseFallbackFiniteEvidence =
  phase-evidence
    Exact.resolvedContributionCountIsNinetySix
    Exact.firstNearPPPImaginarySqrt10NumeratorPositive

module DASHI.Physics.YangMills.YangMillsFiniteConstructiveLadderExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions I".
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II".
-- DOI: 10.1007/BF01608978.
--
-- Roman Kotecky and David Preiss,
-- "Cluster expansion for abstract polymer models".
-- DOI: 10.1007/BF01211762.
--
-- DASHI CONTRIBUTION
--
-- Assemble the proved finite OS2, OS4, polymer-budget and spectral-gap models
-- into one constructive ladder.  The independent toy family has reflection
-- positivity as a sum of squares, exact product clustering, a checked finite
-- KP budget and a volume-indexed spectral gap equal to 3.
--
-- Model tags prove that this finite family is not the interacting nonabelian
-- lattice gauge measure or its continuum limit.  The module supplies reusable
-- proof patterns without promoting them to Yang--Mills OS2/OS4/KP or a Clay
-- mass-gap theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Constructive.FiniteReflectionPositivityExact as OS2
import DASHI.Physics.Constructive.FiniteProductClusteringDenominatorClearedExact as OS4
import DASHI.Physics.Constructive.FinitePolymerKPBudgetExact as KP
import DASHI.Analysis.SharedFiniteSpectralCertificationExact as Shared
import DASHI.Mathematics.LinearAlgebra.RationalTwoByTwoSelfAdjointSpectralExact as Matrix
import DASHI.Physics.YangMills.YangMillsHodgeCoercivityFrontierExact as Frontier
import DASHI.Physics.YangMills.YangMillsStrongCouplingAlternativeGateExact as Existing

record FiniteReflectionCertificate : Set where
  field
    everyObservableSumOfSquares : ∀ observable →
      OS2.SumOfTwoSquares
        (OS2.kernelQuadratic OS2.canonicalKernel observable)
    reflectionSquaredIdentity : ∀ pair →
      OS2.reflection (OS2.reflection pair) ≡ pair

canonicalFiniteReflectionCertificate : FiniteReflectionCertificate
canonicalFiniteReflectionCertificate = record
  { everyObservableSumOfSquares = OS2.canonicalKernelReflectionPositive
  ; reflectionSquaredIdentity = OS2.reflectionInvolutive
  }

record FiniteConstructiveLadderCertificate : Set₁ where
  field
    reflectionPositiveModel : FiniteReflectionCertificate
    exactlyClusteredProductModel : OS4.FiniteProductClusteringCertificate
    finitePolymerBudget : KP.FiniteKPBudgetCertificate
    finiteTransferGap : Shared.FiniteTransferHamiltonianGap

canonicalFiniteConstructiveLadderCertificate :
  FiniteConstructiveLadderCertificate
canonicalFiniteConstructiveLadderCertificate = record
  { reflectionPositiveModel = canonicalFiniteReflectionCertificate
  ; exactlyClusteredProductModel =
      OS4.canonicalFiniteProductClusteringCertificate
  ; finitePolymerBudget = KP.canonicalFiniteKPBudgetCertificate
  ; finiteTransferGap = Shared.canonicalFiniteTransferHamiltonianGap
  }

Volume : Set
Volume = Nat

volumeIndexedGap : Volume → ℚ
volumeIndexedGap volume = Matrix.three

volumeIndexedGapIsThree : ∀ volume →
  volumeIndexedGap volume ≡ Matrix.three
volumeIndexedGapIsThree volume = refl

volumeIndexedGapIsUniform : ∀ firstVolume secondVolume →
  volumeIndexedGap firstVolume ≡ volumeIndexedGap secondVolume
volumeIndexedGapIsUniform firstVolume secondVolume = refl

data MeasureModelTag : Set where
  independentFiniteToyModel
  interactingNonabelianLatticeYangMills
  continuumYangMillsMeasure : MeasureModelTag

finiteToyIsNotInteractingYangMills :
  independentFiniteToyModel ≡ interactingNonabelianLatticeYangMills → ⊥
finiteToyIsNotInteractingYangMills ()

finiteToyIsNotContinuumYangMills :
  independentFiniteToyModel ≡ continuumYangMillsMeasure → ⊥
finiteToyIsNotContinuumYangMills ()

frontierLocalCoercivityStillAvailable :
  Frontier.localCoercivityStageNowInhabited
  ≡ Existing.localFiniteCoercivity
frontierLocalCoercivityStillAvailable = refl

record InteractingYangMillsPromotionBoundary : Set₁ where
  field
    actualGaugeMeasure : Set
    actualReflectionMap : Set
    os2ForGaugeMeasure : Set
    connectedGaugeCorrelators : Set
    os4UniformClustering : Set
    actualPolymerActivities : Set
    kpLargeFieldEstimate : Set
    spacingUniformGap : Set
    continuumMeasureConstruction : Set
    osReconstructedHamiltonian : Set
    continuumMassGap : Set

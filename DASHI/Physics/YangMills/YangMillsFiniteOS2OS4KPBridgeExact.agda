module DASHI.Physics.YangMills.YangMillsFiniteOS2OS4KPBridgeExact where

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
-- Assemble the exact finite OS2, OS4, polymer-budget and spectral-gap models
-- into one constructive ladder.  The toy family has reflection positivity as
-- a sum of squares, exact product clustering, a checked finite KP budget and a
-- volume-indexed gap equal to 3 at every volume.
--
-- A separate model tag prevents these facts from being identified with the
-- interacting nonabelian Yang--Mills measure.  The bridge therefore supplies
-- finite proof patterns for the existing frontier without closing OS2/OS4/KP
-- or the continuum mass gap for Yang--Mills.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Physics.Constructive.FiniteReflectionPositivityExact as OS2
import DASHI.Physics.Constructive.FiniteProductClusteringDenominatorClearedExact as OS4
import DASHI.Physics.Constructive.FinitePolymerKPBudgetExact as KP
import DASHI.Analysis.SharedFiniteSpectralCertificationExact as Spectral
import DASHI.Physics.YangMills.YangMillsHodgeCoercivityFrontierExact as Frontier

record FiniteConstructiveOSKPModel : Set₁ where
  field
    reflectionPositive : OS2.FiniteReflectionPositivityCertificate
    exactlyClustered : OS4.FiniteProductClusteringCertificate
    polymerBudget : KP.FiniteKPBudgetCertificate
    transferGap : Spectral.FiniteTransferHamiltonianGap

------------------------------------------------------------------------
-- Add a compact named OS2 certificate to the exact reflection model.
------------------------------------------------------------------------

record ReflectionCertificateAlias : Set where
  field
    everyObservableSumOfSquares : ∀ observable →
      OS2.SumOfTwoSquares (OS2.kernelQuadratic OS2.canonicalKernel observable)
    reflectionSquaredIdentity : ∀ pair →
      OS2.reflection (OS2.reflection pair) ≡ pair

canonicalReflectionCertificateAlias : ReflectionCertificateAlias
canonicalReflectionCertificateAlias = record
  { everyObservableSumOfSquares = OS2.canonicalKernelReflectionPositive
  ; reflectionSquaredIdentity = OS2.reflectionInvolutive
  }

record FiniteConstructiveCertificate : Set₁ where
  field
    reflection : ReflectionCertificateAlias
    clustering : OS4.FiniteProductClusteringCertificate
    kp : KP.FiniteKPBudgetCertificate
    finiteGap : Spectral.FiniteTransferHamiltonianGap

canonicalFiniteConstructiveCertificate : FiniteConstructiveCertificate
canonicalFiniteConstructiveCertificate = record
  { reflection = canonicalReflectionCertificateAlias
  ; clustering = OS4.canonicalFiniteProductClusteringCertificate
  ; kp = KP.canonicalFiniteKPBudgetCertificate
  ; finiteGap = Spectral.canonicalFiniteTransferHamiltonianGap
  }

Volume : Set
Volume = Nat

volumeIndexedGap : Volume → Data.Rational.Base.ℚ
volumeIndexedGap volume = Spectral.Spectral.three

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
  ≡ DASHI.Physics.YangMills.YangMillsStrongCouplingAlternativeGateExact.localFiniteCoercivity
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

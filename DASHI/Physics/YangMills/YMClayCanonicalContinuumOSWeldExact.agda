module DASHI.Physics.YangMills.YMClayCanonicalContinuumOSWeldExact where

------------------------------------------------------------------------
-- CANONICAL CONTINUUM / OS ENDGAME FOR THE YM CLAY PARITY LANE
--
-- The first #987 parity pass deliberately exposed a generic
-- `CommonContinuumOSRoute`.  This owner replaces its two generic arrows by
-- theorem-bearing objects that already exist in the Yang--Mills tree:
--
--   finite uniform vacuum gap + recovery geometry
--     -> BalabanVacuumOrthogonalMoscoRecoveryExact
--     -> physical continuum vacuum form gap;
--
--   reconstructed physical mass-gap Hamiltonian + Kato physical Hamiltonian
--     -> BalabanClayDirectTerminalConsumerCutRound308Exact
--     -> explicit same-Hamiltonian dynamics witness.
--
-- The only endpoint consequence not independently implemented in Agda is the
-- full vacuum-sector resolvent existence/uniqueness theorem.  Lean YMClay owns
-- that compiler.  It remains an explicit proof field here rather than being
-- hidden behind a generic continuum function.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _≤_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as Recovery
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.BalabanMassGapSurvival as Survival
import DASHI.Physics.YangMills.BalabanPhysicalMassGapRoutes as Routes
import DASHI.Physics.YangMills.YMKatoClosedFormHamiltonianExact as Kato
import DASHI.Physics.YangMills.BalabanClayDirectTerminalConsumerCutRound308Exact as R308
import DASHI.Physics.YangMills.YMClayMassGapAssemblyParityExact as Assembly

------------------------------------------------------------------------
-- Canonical cutoff -> continuum compiler.
------------------------------------------------------------------------

canonicalRecoveryContinuumGap :
  (system : Recovery.VacuumOrthogonalRecoverySystem) →
  Recovery.PhysicalVacuumGapAfterRecovery system
canonicalRecoveryContinuumGap = Recovery.physicalVacuumGapAfterRecovery

canonicalRecoveryLimitGap :
  (system : Recovery.VacuumOrthogonalRecoverySystem) →
  (limit : Recovery.LimitVector system) →
  Recovery.limitVacuumOrthogonal system limit →
  Recovery.gapConstant system * Recovery.limitNormSq system limit
  ≤ Recovery.limitEnergy system limit
canonicalRecoveryLimitGap = Recovery.vacuumOrthogonalRecoveryTransfersUniformGap

------------------------------------------------------------------------
-- Canonical continuum spectral-gap producers already present in DASHI.
------------------------------------------------------------------------

canonicalClusteringMassGapCertificate :
  ∀ {Observable Time Scalar Bound Hamiltonian}
    (dataSet : Routes.ExponentialTimeClusteringData
      Observable Time Scalar Bound Hamiltonian) →
  Routes.ExponentialClusteringSpectrumAuthority dataSet →
  OSGap.PhysicalMassGapCertificate Hamiltonian Bound
canonicalClusteringMassGapCertificate =
  Routes.exponentialTimeClusteringImpliesSpectrumGap

canonicalStrongResolventMassGapCertificate :
  ∀ {Cutoff Hamiltonian Bound}
    (dataSet : Survival.UniformCutoffGapData Cutoff Hamiltonian Bound) →
  (convergence : Routes.StrongResolventConvergenceData dataSet) →
  Routes.StrongResolventGapSurvivalAuthority dataSet convergence →
  OSGap.PhysicalMassGapCertificate Hamiltonian Bound
canonicalStrongResolventMassGapCertificate = Routes.gapSurvivesTheLimit

------------------------------------------------------------------------
-- Preferred physical endgame.
--
-- `terminal` is not an arbitrary OS map.  It is the existing Round308 object
-- carrying the reconstructed physical mass-gap Hamiltonian, the Kato physical
-- Hamiltonian and their same-dynamics witness.  `recoverySystem` is the actual
-- Mosco/recovery object carrying the continuum vacuum-form inequality.
--
-- The gap equality prevents mixing a recovery estimate at one threshold with a
-- spectral certificate at another.
------------------------------------------------------------------------

record CanonicalPhysicalMassGapEndgame
    (Hilbert Scalar Hamiltonian Vacuum ContinuumTheory : Set) : Set₁ where
  field
    recoverySystem : Recovery.VacuumOrthogonalRecoverySystem
    terminal : R308.DirectTerminalClayConsumers
      Hilbert Scalar Hamiltonian ℚ ContinuumTheory
    vacuum : Vacuum

    sameGap :
      OSGap.gap (R308.massGap terminal)
      ≡ Recovery.gapConstant recoverySystem

    VacuumSectorResolvent : Set
    vacuumSectorResolvent : VacuumSectorResolvent

open CanonicalPhysicalMassGapEndgame public

canonicalContinuumFormGap :
  ∀ {Hilbert Scalar Hamiltonian Vacuum ContinuumTheory}
    (endgame : CanonicalPhysicalMassGapEndgame
      Hilbert Scalar Hamiltonian Vacuum ContinuumTheory) →
  Recovery.PhysicalVacuumGapAfterRecovery (recoverySystem endgame)
canonicalContinuumFormGap endgame =
  Recovery.physicalVacuumGapAfterRecovery (recoverySystem endgame)

canonicalPhysicalSameHamiltonianDynamics :
  ∀ {Hilbert Scalar Hamiltonian Vacuum ContinuumTheory}
    (endgame : CanonicalPhysicalMassGapEndgame
      Hilbert Scalar Hamiltonian Vacuum ContinuumTheory) →
  R308.SameHamiltonianDynamics (terminal endgame)
    (OSGap.hamiltonian (R308.massGap (terminal endgame)))
    (Kato.hamiltonian (R308.physicalKatoPackage (terminal endgame)))
canonicalPhysicalSameHamiltonianDynamics endgame =
  R308.sameHamiltonianDynamics (terminal endgame)

canonicalPhysicalMassGapConclusion :
  ∀ {Hilbert Scalar Hamiltonian Vacuum ContinuumTheory}
    (endgame : CanonicalPhysicalMassGapEndgame
      Hilbert Scalar Hamiltonian Vacuum ContinuumTheory) →
  Assembly.MassGapConclusion Hamiltonian Vacuum ℚ
canonicalPhysicalMassGapConclusion endgame = record
  { Assembly.MassGapConclusion.hamiltonian =
      OSGap.hamiltonian (R308.massGap (terminal endgame))
  ; Assembly.MassGapConclusion.vacuum = vacuum endgame
  ; Assembly.MassGapConclusion.gap =
      OSGap.gap (R308.massGap (terminal endgame))
  ; Assembly.MassGapConclusion.GapPositive =
      OSGap.Positive (R308.massGap (terminal endgame))
        (OSGap.gap (R308.massGap (terminal endgame)))
  ; Assembly.MassGapConclusion.gapPositive =
      OSGap.gapPositive (R308.massGap (terminal endgame))
  ; Assembly.MassGapConclusion.VacuumFormGap =
      Recovery.PhysicalVacuumGapAfterRecovery (recoverySystem endgame)
  ; Assembly.MassGapConclusion.vacuumFormGap =
      canonicalContinuumFormGap endgame
  ; Assembly.MassGapConclusion.NoPositiveSubgapMode =
      OSGap.SpectrumAboveVacuumGap (R308.massGap (terminal endgame))
  ; Assembly.MassGapConclusion.noPositiveSubgapMode =
      OSGap.spectrumAboveVacuumGap (R308.massGap (terminal endgame))
  ; Assembly.MassGapConclusion.VacuumSectorResolvent =
      VacuumSectorResolvent endgame
  ; Assembly.MassGapConclusion.vacuumSectorResolvent =
      vacuumSectorResolvent endgame
  }

------------------------------------------------------------------------
-- Validation sentinels.
------------------------------------------------------------------------

data RecoveryContinuumCompilerPresent : Set where
  recoveryContinuumCompilerPresent : RecoveryContinuumCompilerPresent

data PhysicalMassGapEndgamePresent : Set where
  physicalMassGapEndgamePresent : PhysicalMassGapEndgamePresent

canonicalRecoveryContinuumCompilerLevel : ProofLevel
canonicalRecoveryContinuumCompilerLevel = machineChecked

canonicalClusteringMassGapCompilerLevel : ProofLevel
canonicalClusteringMassGapCompilerLevel = Routes.physicalMassGapRouteAssemblyLevel

canonicalStrongResolventMassGapCompilerLevel : ProofLevel
canonicalStrongResolventMassGapCompilerLevel = Routes.physicalMassGapRouteAssemblyLevel

canonicalPhysicalEndgameAssemblyLevel : ProofLevel
canonicalPhysicalEndgameAssemblyLevel = machineChecked

-- This is the one generic consequence still only implemented in the retained
-- Lean YMClay tranche, not proved independently by an Agda theorem term.
agdaVacuumSectorResolventCompilerLevel : ProofLevel
agdaVacuumSectorResolventCompilerLevel = conditional

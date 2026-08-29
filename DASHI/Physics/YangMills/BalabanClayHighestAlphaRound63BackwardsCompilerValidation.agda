module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound63BackwardsCompilerValidation where

------------------------------------------------------------------------
-- ROUND63: MAKE THE HYPOTHETICAL FINISHED PROOF THE DEVELOPMENT ROOT
--
-- Round62 corrected the physical producer cutset to thirteen leaves.  Round63
-- changes the workflow: the authoritative object is now the complete backwards
-- compiler
--
--   SU2PhysicalProducers -> SU2ClayConclusion,
--
-- not a hand-maintained list.  The list is retained only as executable
-- arithmetic and documentation.
--
-- This validation root also imports the two endpoint implications that are
-- already theorem-level mathematics:
--
--   strict continuum fourth cumulant -> non-Gaussian witness,
--   OS exponential clustering       -> positive Hamiltonian/transfer gap.
--
-- They must therefore be compiler edges, never additional physical producer
-- fields.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound62ProducerCutsetValidation as Round62
import DASHI.Physics.YangMills.BalabanSU2ClayBackwardsCompilerExact as Backwards

-- Exact G2 signed compiler: two physical enclosures, not three norm bounds.
import DASHI.Physics.YangMills.BalabanChargeRelativeCorrelatedD1G2ClosureExact

-- One-loop reduction: four orbit representatives, not 240 independent cells.
import DASHI.Physics.YangMills.BalabanCMP109WalshFiniteModeFourRepresentativeLowerExact
import DASHI.Physics.YangMills.BalabanSU2OneLoopNormalizationSanityExact

-- Literal transfer theorem interfaces.
import DASHI.Physics.YangMills.BalabanWilsonTransferIntertwinerExact
import DASHI.Physics.YangMills.BalabanTransferKernelTraceNaturalityExact
import DASHI.Physics.YangMills.BalabanDirectTransferSchurGapWeldExact
import DASHI.Physics.YangMills.BalabanTerminalTransferKatoGapStabilityExact

-- Continuum endpoint carriers.
import DASHI.Physics.YangMills.BalabanContinuumProkhorovSubsequenceExact
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

-- Already-proved endpoint implications.  These are deliberately not physical
-- producer slots in Backwards.SU2PhysicalProducerTypes.
import DASHI.Physics.YangMills.YangMillsContinuumFourthCumulantNonGaussianExact as NonGaussian
import DASHI.Physics.YangMills.BalabanOSExponentialClusteringImpliesHamiltonianGapExact as OSGap
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

-- Typed submission-facing continuum and OS/Wightman packages.
import DASHI.Physics.YangMills.YangMillsSubmissionTypedLimitEndpointExact
import DASHI.Physics.YangMills.BalabanConstructiveCompletionSpine

------------------------------------------------------------------------
-- The old count and the new compiler count coincide definitionally.
------------------------------------------------------------------------

round63PhysicalProducerCount : Nat
round63PhysicalProducerCount = Backwards.backwardsCompilerPhysicalProducerCount

round63PhysicalProducerCountExact : round63PhysicalProducerCount ≡ 13
round63PhysicalProducerCountExact = Backwards.backwardsCompilerPhysicalProducerCountExact

round62AndRound63CountsAgree :
  Round62.liveSU2HardProducerCount ≡ round63PhysicalProducerCount
round62AndRound63CountsAgree = refl

------------------------------------------------------------------------
-- Endpoint weld 1: a strict fourth-cumulant witness already refutes Gaussian
-- Wick factorization.  The hard producer is obtaining the strict witness from
-- the ACTUAL continuum Schwinger family, not this implication.
------------------------------------------------------------------------

continuumFourthCumulantLowerBoundImpliesNonGaussian :
  (witness : NonGaussian.ContinuumGaugeInvariantFourthCumulantWitness) →
  NonGaussian.GaussianWickFour (NonGaussian.moments witness) → ⊥
continuumFourthCumulantLowerBoundImpliesNonGaussian =
  NonGaussian.continuumFourthCumulantWitnessIsNonGaussian

------------------------------------------------------------------------
-- Endpoint weld 2: once the SAME continuum OS closure supplies physical
-- exponential clustering, the existing spectral theorem gives the positive
-- gap.  The hard producer is clustering plus the concrete OS spectral
-- interpretation, not a second independent mass-gap estimate.
------------------------------------------------------------------------

osClusteringImpliesPositiveGap :
  ∀ {Measure Schwinger Observable Energy Bound}
    {closure : Limit.FiniteToContinuumOSClosure Measure Schwinger}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  Gap.OS4SpectralInterpretation closure spectrum →
  Limit.Clustered closure
    (Limit.schwinger closure (Limit.continuumMeasure closure)) →
  Gap.PositiveTransferGap spectrum
osClusteringImpliesPositiveGap =
  OSGap.OSExponentialClusteringImpliesHamiltonianGap

------------------------------------------------------------------------
-- Proof-level audit.
--
-- The compiler definition and the two endpoint implications are theorem-level
-- infrastructure.  What is intentionally still conditional is the CONCRETE
-- instantiation of Backwards.SU2PhysicalProducerTypes and
-- Backwards.SU2BackwardsTheoremGraph on the literal Round61/62 physical
-- carriers.  That instantiation is now the next authoritative typechecking
-- target; every mismatch it exposes supersedes the prose cutset.
------------------------------------------------------------------------

round63BackwardsCompilerDefinitionLevel : ProofLevel
round63BackwardsCompilerDefinitionLevel = machineChecked

round63FourthCumulantToNonGaussianLevel : ProofLevel
round63FourthCumulantToNonGaussianLevel = machineChecked

round63ClusteringToSpectralGapLevel : ProofLevel
round63ClusteringToSpectralGapLevel = machineChecked

round63ConcretePhysicalGraphInstantiationLevel : ProofLevel
round63ConcretePhysicalGraphInstantiationLevel = conditional

round63PhysicalProducerWitnessesLevel : ProofLevel
round63PhysicalProducerWitnessesLevel = conditional

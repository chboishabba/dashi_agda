module DASHI.Physics.YangMills.YangMillsHurwitzHopfStructuralGateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John C. Baez,
-- "The Octonions".
-- DOI: 10.1090/S0273-0979-01-00934-X.
--
-- Heinz Hopf,
-- "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche".
-- DOI: 10.1007/BF01457962.
--
-- A. A. Belavin, A. M. Polyakov, A. S. Schwartz and Yu. S. Tyupkin,
-- "Pseudoparticle Solutions of the Yang--Mills Equations",
-- Physics Letters B 59 (1975), 85--87.
-- DOI: 10.1016/0370-2693(75)90163-X.
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang--Mills Theory", official Clay Mathematics Institute problem
-- description.  No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Make the quaternion cross-pollination literal.  The carrier used for the
-- exact Cayley--Dickson and Hopf identities is definitionally the same
-- rational quaternion carrier already used by the Wilson-Hessian and SU(2)
-- action-normalization development.  The identity element has the expected
-- fundamental real trace, and the polynomial Hopf radius theorem is reused
-- directly.
--
-- Principal-bundle local triviality, the BPST connection, self-duality,
-- finite action, second-Chern integrality, the interacting Euclidean measure,
-- Osterwalder--Schrader reconstruction and the positive Hamiltonian mass gap
-- remain distinct typed stages.  No topological identity is promoted into an
-- analytic or quantum result.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Mathematics.Algebra.HurwitzFrobeniusLawProfileExact as HF
import DASHI.Mathematics.Topology.QuaternionHopfRadiusExact as H
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanStrongCouplingSU2ActionNormalizationExact as SU2
import DASHI.Physics.YangMills.YangMillsStrongCouplingAlternativeGateExact as ExistingGate

sharedQuaternionCarrier : H.QuaternionCarrier ≡ Q.RationalQuaternion
sharedQuaternionCarrier = refl

su2IdentityFundamentalRealTraceExact :
  SU2.su2FundamentalRealTrace Q.oneQ ≡ + 2 / 1
su2IdentityFundamentalRealTraceExact = solve []

quaternionProductNormReused : ∀ left right →
  CD.quaternionNormSq (Q._*q_ left right)
  ≡ CD.quaternionNormSq left * CD.quaternionNormSq right
quaternionProductNormReused = CD.quaternionNormMultiplicative

quaternionHopfRadiusIdentityReused : ∀ a b →
  H.hopfTargetNormSq a b
  ≡ (CD.quaternionNormSq a + CD.quaternionNormSq b)
    * (CD.quaternionNormSq a + CD.quaternionNormSq b)
quaternionHopfRadiusIdentityReused = H.quaternionHopfRadiusIdentity

quaternionIsFrobeniusAndHurwitzCandidate :
  HF.frobeniusCandidate HF.quaternion ≡ Agda.Builtin.Bool.true
  × HF.hurwitzCandidate HF.quaternion ≡ Agda.Builtin.Bool.true
quaternionIsFrobeniusAndHurwitzCandidate =
  HF.quaternionIsBothCandidates

data YangMillsQuaternionHopfStage : Set where
  rationalQuaternionRing : YangMillsQuaternionHopfStage
  su2TraceNormalization : YangMillsQuaternionHopfStage
  quaternionHopfRadiusIdentity : YangMillsQuaternionHopfStage
  principalSU2BundleOverS4 : YangMillsQuaternionHopfStage
  bpstSelfDualConnection : YangMillsQuaternionHopfStage
  integralSecondChernSector : YangMillsQuaternionHopfStage
  interactingEuclideanGaugeMeasure : YangMillsQuaternionHopfStage
  continuumOSReconstruction : YangMillsQuaternionHopfStage
  positiveHamiltonianMassGap : YangMillsQuaternionHopfStage

hopfRadiusIsNotPrincipalBundleProof :
  quaternionHopfRadiusIdentity ≡ principalSU2BundleOverS4 → ⊥
hopfRadiusIsNotPrincipalBundleProof ()

principalBundleIsNotInstantonConstruction :
  principalSU2BundleOverS4 ≡ bpstSelfDualConnection → ⊥
principalBundleIsNotInstantonConstruction ()

instantonIsNotInteractingMeasure :
  bpstSelfDualConnection ≡ interactingEuclideanGaugeMeasure → ⊥
instantonIsNotInteractingMeasure ()

osReconstructionIsNotPositiveGapByDefinition :
  continuumOSReconstruction ≡ positiveHamiltonianMassGap → ⊥
osReconstructionIsNotPositiveGapByDefinition ()

fixedLatticeClusteringStillNotContinuumGap :
  ExistingGate.fixedLatticeExponentialClustering
  ≡ ExistingGate.reconstructedContinuumHamiltonianGap → ⊥
fixedLatticeClusteringStillNotContinuumGap =
  ExistingGate.strongCouplingGapIsNotHamiltonianGap

record QuaternionicInstantonBridge : Set₁ where
  field
    unitQuaternionLieGroupIdentification : Set
    smoothQuaternionicHopfBundle : Set
    localConnectionForms : Set
    curvatureTwoForm : Set
    selfDualityEquation : Set
    finiteYangMillsAction : Set
    secondChernNumberIntegrality : Set

record InstantonToQuantumMassGapBridge : Set₁ where
  field
    interactingMeasureConstruction : Set
    reflectionPositivity : Set
    thermodynamicAndContinuumLimits : Set
    nontrivialOSReconstruction : Set
    HamiltonianConstruction : Set
    vacuumSectorIsolation : Set
    positiveSpectralGap : Set

record HurwitzHopfYangMillsRoute : Set₁ where
  field
    exactQuaternionAlgebra : Set
    quaternionicInstantonBridge : QuaternionicInstantonBridge
    instantonToQuantumBridge : InstantonToQuantumMassGapBridge

-- There is intentionally no constructor from the exact rational quaternion
-- identities alone to either of the two analytic/geometric bridge records.

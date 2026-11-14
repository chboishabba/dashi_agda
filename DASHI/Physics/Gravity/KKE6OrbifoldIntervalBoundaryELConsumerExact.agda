module DASHI.Physics.Gravity.KKE6OrbifoldIntervalBoundaryELConsumerExact where

------------------------------------------------------------------------
-- Source-faithful E6-trinification S1/Z2 bulk/brane RECONCILIATION
-- 2026-10-25.
--
-- Existing E6 PR #1106 OWNS the first-Tits 27, E32/E33 gauge Higgs,
-- and original 6-invariant V6. Physical KK #1241 OWNS the chosen
-- orbifold source, Chi E21 boundary Higgs and 18-even Hessian labels.
--
-- CORRECTION: ∇(V_bulk + 2W_boundary)=0 for spatially CONSTANT
-- four-dimensional scalar zero modes DOES NOT imply the separate
-- 5D interior Euler-Lagrange equations and Robin boundary conditions.
--
-- At the old fixed t=.0246 stationary zero-mode truncation:
-- ∂_t V_bulk=t(6-13t²)=+0.147406469832 is NONZERO;
-- 2W'(t)=-t(6-13t²) cancels ONLY after integration.
--
-- The selected new comparison action on dimensionless interval [0,1]
-- uses scalar source E=∫[1/2|φ'|²+V6]dy + W(0)+W(1)
-- with Φ=a(y)E32, Χ=b(y)E33+t(y)E21. A nonconstant profile solves
-- the actual three bulk ODEs and Robin BCs numerically, with
-- all other 36-real scalar bulk gradients and 16 gauge currents
-- checked independently. The three-field FEM Hessian is locally
-- positive in that submanifold; the FULL 18-real interval functional
-- Hessian is OPEN. NO physical radius/5D source/gauge/CS is implied.
--
-- Original boundary Higgs theory and rigorous boundary requirements:
-- Leng/Moreau/Nortier PRD 103 (2021) 075010;
-- Barcelo/Mitra/Moreau EPJC 75 (2015) 527.
--
-- The Agda theorems below are FINITE status/non-transport witnesses.
-- They do not kernel prove nonlinear BVP existence or its spectrum.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_+_; _*_)
import DASHI.Physics.Gravity.KKE6OrbifoldBoundaryHiggsConsumerExact as Earlier
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

-- IMPORTANT: the original E6V six-invariant theorem owner is on
-- UNMERGED PR #1106 and is NOT present on this KK #1241 branch.
-- Its formula is independently re-evaluated in the Python source,
-- but no unmerged cross-branch Agda module is imported here.

originalHiggsEvenRealZeroModes : 2 * (4 + 5) ≡ 18
originalHiggsEvenRealZeroModes = refl

selectedBulkPlusTwoEndpointFields : 3 + 2 ≡ 5
selectedBulkPlusTwoEndpointFields = refl

data PhysicalHiggsCandidate : Set where
  oldConstantHomogeneousZeroModeExtremum
  correctedNonconstantRobinIntervalSource : PhysicalHiggsCandidate

sameParityEvenZeroModeDimension : PhysicalHiggsCandidate → Nat
sameParityEvenZeroModeDimension _ = 18

homogeneousEffectivePotentialStationarityAvailable :
  PhysicalHiggsCandidate → Bool
homogeneousEffectivePotentialStationarityAvailable
  oldConstantHomogeneousZeroModeExtremum = true
homogeneousEffectivePotentialStationarityAvailable
  correctedNonconstantRobinIntervalSource = false

-- These are numeric source-script OUTCOME LABELS. In particular,
-- the later candidate solves a NEW nonconstant comparison BVP,
-- not the already-declared old physical b0=10^-24m KK model.
separateBulkAndRobinBoundaryEquationsPassInSelectedModel :
  PhysicalHiggsCandidate → Bool
separateBulkAndRobinBoundaryEquationsPassInSelectedModel
  oldConstantHomogeneousZeroModeExtremum = false
separateBulkAndRobinBoundaryEquationsPassInSelectedModel
  correctedNonconstantRobinIntervalSource = true

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

sameEvenCarrierDoesNotDetermineFiveDVacuum :
  Transport.ClaimNonTransportWitness
    sameParityEvenZeroModeDimension
    separateBulkAndRobinBoundaryEquationsPassInSelectedModel
sameEvenCarrierDoesNotDetermineFiveDVacuum =
  Descent.consumerNonDescentWitness
    oldConstantHomogeneousZeroModeExtremum
    correctedNonconstantRobinIntervalSource
    refl falseNotTrue

noFiveDVacuumPromotionFromParityEvenDimension :
  Transport.ClaimTransport
    sameParityEvenZeroModeDimension
    separateBulkAndRobinBoundaryEquationsPassInSelectedModel → ⊥
noFiveDVacuumPromotionFromParityEvenDimension =
  Transport.claimNonTransportWitnessBlocksTransport
    sameEvenCarrierDoesNotDetermineFiveDVacuum

sourceRepairMustTrackInteriorAndBoundary :
  (refine : PhysicalHiggsCandidate → Bool) →
  Repair.RefinementRepairs
    sameParityEvenZeroModeDimension refine
    separateBulkAndRobinBoundaryEquationsPassInSelectedModel →
  refine oldConstantHomogeneousZeroModeExtremum
    ≡ refine correctedNonconstantRobinIntervalSource → ⊥
sourceRepairMustTrackInteriorAndBoundary refine adequate same =
  Repair.refinementRepairSeparatesWitness
    sameEvenCarrierDoesNotDetermineFiveDVacuum adequate same

data CertificationLevel : Set where
  integratedZeroModeHessianOnly
  selectedDimensionlessNonconstantBVP
  fullEighteenScalarIntervalOperator
  globallyAnomalyFreeDimensionfulFiveDGravity : CertificationLevel

selectedCertification : CertificationLevel
selectedCertification = selectedDimensionlessNonconstantBVP

data OutstandingConsumer : Set where
  fullOrbifoldEvenFunctionalHessian
  oddGaugeAndScalarKKTower
  fiveDimensionalSourceDimensionsAndBoundaryJunctions
  originalE6FermionMassAndLocalGlobalCS
  fullyRegulatedSameMetricRadionEffectiveAction
  selectedEmpiricalGravityObservable : OutstandingConsumer


------------------------------------------------------------------------
-- 2026-10-25 all 18 parity-EVEN field FUNCTIONAL Hessian BIDI.
-- Previous 7+11 labels described spatially homogeneous Hessian;
-- the NEW selected test includes 1D scalar gradient stiffness and
-- endpoint W'' along the NONCONSTANT Robin classical source.
-- Two-grid generalized FEM eigenproblem N=32 and N=64 sees
-- seven near-zero gauge directions (~h² convergence) and the
-- first positive eigenvalue near +2.08. Source script:
-- check_kk_e6_orbifold_interval_even_hessian.py
-- The continuum operator, renormalized QFT and physical kinetic
-- source are NOT proved in the Agda kernel.
------------------------------------------------------------------------

data IntervalHessianConsumer : Set where
  oldHomogeneousEighteenMatrix
  selectedNonconstantEighteenFunctionalFEM : IntervalHessianConsumer

evenSourceFieldCount : IntervalHessianConsumer → Nat
evenSourceFieldCount _ = 18

physicalNonconstantGradientAndEndpointHessianIncluded :
  IntervalHessianConsumer → Bool
physicalNonconstantGradientAndEndpointHessianIncluded
  oldHomogeneousEighteenMatrix = false
physicalNonconstantGradientAndEndpointHessianIncluded
  selectedNonconstantEighteenFunctionalFEM = true

sameScalarCountNotSameDifferentialOperator :
  Transport.ClaimNonTransportWitness
    evenSourceFieldCount
    physicalNonconstantGradientAndEndpointHessianIncluded
sameScalarCountNotSameDifferentialOperator =
  Descent.consumerNonDescentWitness
    oldHomogeneousEighteenMatrix
    selectedNonconstantEighteenFunctionalFEM
    refl falseNotTrue

selectedNumericalLowEigenSpectrumNonnegative : Bool
selectedNumericalLowEigenSpectrumNonnegative = true

selectedContinuumSpectralGapKernelCertified : Bool
selectedContinuumSpectralGapKernelCertified = false

selectedPhysicalFiveDimensionalGaugeQuantumVacuumCertified : Bool
selectedPhysicalFiveDimensionalGaugeQuantumVacuumCertified = false

twoMeshSelectedZeroAndPositiveModes : 7 + 11 ≡ 18
twoMeshSelectedZeroAndPositiveModes = refl

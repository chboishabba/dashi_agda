module DASHI.Physics.YangMills.YangMillsPaperClaimAuditCarrierExact where

------------------------------------------------------------------------
-- SOURCES AND PURPOSE
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay Mathematics Institute problem
-- description, in The Millennium Prize Problems.  No DOI assigned.
--
-- This module separates bibliographic status from mathematical content.  A
-- source may be peer reviewed, self archived, retracted, superseded, or merely
-- numerical; none of those labels supplies a theorem.  Every claim must expose
-- its theory, target operator, assumptions, bridge obligations and first open
-- dependency before it can feed the Clay-facing proof graph.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (length)

data VenueStatus : Set where
  peerReviewedArticle : VenueStatus
  academicPreprint : VenueStatus
  repositoryDeposit : VenueStatus
  selfArchivedManuscript : VenueStatus
  workingPaper : VenueStatus
  supersededSource : VenueStatus
  retractedSource : VenueStatus
  officialProblemStatement : VenueStatus

data TheorySignature : Set where
  pureFourDimensionalYangMills : TheorySignature
  latticeYangMillsFixedSpacing : TheorySignature
  fiveDimensionalOrbifoldGaugeTheory : TheorySignature
  yangMillsWithAdditionalScalar : TheorySignature
  einsteinCartanYangMillsTheory : TheorySignature
  celestialConformalConstruction : TheorySignature
  topologicalHopfFibrationTheory : TheorySignature
  nonlocalHolonomyGaugeTheory : TheorySignature
  effectivePolyakovLoopDynamics : TheorySignature
  noncommutativeOrMatrixGaugeModel : TheorySignature

data OperatorSignature : Set where
  physicalReconstructedHamiltonian : OperatorSignature
  latticeTransferOperator : OperatorSignature
  boundarySlabTransferKernel : OperatorSignature
  auxiliaryBoundaryLangevinGenerator : OperatorSignature
  stochasticLangevinGenerator : OperatorSignature
  beltramiOperator : OperatorSignature
  sturmLiouvilleRegulatorOperator : OperatorSignature
  conformalWeightOperator : OperatorSignature
  functionalRGLinearization : OperatorSignature
  periodDoublingReturnMap : OperatorSignature

data EvidenceKind : Set where
  formalKernelProof : EvidenceKind
  completePublishedProofWithHypotheses : EvidenceKind
  conditionalDerivation : EvidenceKind
  proofSketch : EvidenceKind
  numericalResidual : EvidenceKind
  latticeAgreement : EvidenceKind
  rhetoricalChecklist : EvidenceKind
  citationOnly : EvidenceKind

data AuditOutcome : Set where
  checkedTheorem : AuditOutcome
  conditionalTheorem : AuditOutcome
  counterexampleToInference : AuditOutcome
  differentTheoryStatement : AuditOutcome
  firstDependencyOpen : AuditOutcome
  withdrawnClaim : AuditOutcome

data BridgeObligation : Set where
  sameTheoryEquivalence : BridgeObligation
  sameOperatorIntertwining : BridgeObligation
  measureConstructionAndPositivity : BridgeObligation
  reflectionPositivity : BridgeObligation
  continuumCutoffRemoval : BridgeObligation
  physicalGapScaleCompatibility : BridgeObligation
  noCircularGapInput : BridgeObligation
  gaugeSliceOrQuotientControl : BridgeObligation
  allCompactSimpleGroupCoverage : BridgeObligation
  localOperatorAndOPEConstruction : BridgeObligation

record PaperClaimAudit : Set₁ where
  field
    Source : Set
    Claim : Set
    Assumption : Set
    MissingBridge : Set

    sourceStatus : VenueStatus
    sourceTheory : TheorySignature
    claimedOperator : OperatorSignature
    evidence : EvidenceKind
    outcome : AuditOutcome

    assumptions : List Assumption
    requiredBridges : List BridgeObligation
    firstOpenDependency : MissingBridge

open PaperClaimAudit public

------------------------------------------------------------------------
-- Fail-closed promotion rules.
------------------------------------------------------------------------

bibliographicStatusIsNotEvidence :
  VenueStatus ≡ EvidenceKind → ⊥
bibliographicStatusIsNotEvidence ()

theorySignatureIsNotOperatorSignature :
  TheorySignature ≡ OperatorSignature → ⊥
theorySignatureIsNotOperatorSignature ()

numericalEvidenceIsNotFormalProof :
  numericalResidual ≡ formalKernelProof → ⊥
numericalEvidenceIsNotFormalProof ()

latticeAgreementIsNotFormalProof :
  latticeAgreement ≡ formalKernelProof → ⊥
latticeAgreementIsNotFormalProof ()

checklistIsNotFormalProof :
  rhetoricalChecklist ≡ formalKernelProof → ⊥
checklistIsNotFormalProof ()

fixedSpacingTheoryIsNotContinuumTheory :
  latticeYangMillsFixedSpacing ≡ pureFourDimensionalYangMills → ⊥
fixedSpacingTheoryIsNotContinuumTheory ()

einsteinCartanYangMillsIsNotDefinitionallyPureYangMills :
  einsteinCartanYangMillsTheory ≡ pureFourDimensionalYangMills → ⊥
einsteinCartanYangMillsIsNotDefinitionallyPureYangMills ()

beltramiOperatorIsNotPhysicalHamiltonian :
  beltramiOperator ≡ physicalReconstructedHamiltonian → ⊥
beltramiOperatorIsNotPhysicalHamiltonian ()

conformalWeightIsNotPhysicalHamiltonian :
  conformalWeightOperator ≡ physicalReconstructedHamiltonian → ⊥
conformalWeightIsNotPhysicalHamiltonian ()

stochasticGeneratorIsNotPhysicalHamiltonian :
  stochasticLangevinGenerator ≡ physicalReconstructedHamiltonian → ⊥
stochasticGeneratorIsNotPhysicalHamiltonian ()

auxiliaryBoundaryLangevinIsNotSlabTransferKernel :
  auxiliaryBoundaryLangevinGenerator ≡ boundarySlabTransferKernel → ⊥
auxiliaryBoundaryLangevinIsNotSlabTransferKernel ()

boundarySlabTransferKernelIsNotPhysicalHamiltonian :
  boundarySlabTransferKernel ≡ physicalReconstructedHamiltonian → ⊥
boundarySlabTransferKernelIsNotPhysicalHamiltonian ()

requiredPromotionBridges : List BridgeObligation
requiredPromotionBridges =
  sameTheoryEquivalence
  ∷ sameOperatorIntertwining
  ∷ measureConstructionAndPositivity
  ∷ reflectionPositivity
  ∷ continuumCutoffRemoval
  ∷ physicalGapScaleCompatibility
  ∷ noCircularGapInput
  ∷ gaugeSliceOrQuotientControl
  ∷ allCompactSimpleGroupCoverage
  ∷ localOperatorAndOPEConstruction
  ∷ []

requiredPromotionBridgeCountExact :
  length requiredPromotionBridges ≡ 10
requiredPromotionBridgeCountExact = refl

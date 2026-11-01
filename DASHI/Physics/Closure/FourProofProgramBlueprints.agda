module DASHI.Physics.Closure.FourProofProgramBlueprints where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Geometry.LCP.FiniteSpectralGap as FSG
import DASHI.Geometry.LCP.InductiveLimit as InductiveLimit
import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as MassGap
import DASHI.Physics.Closure.CKMCarrierMixingReceipt as CKM
import DASHI.Physics.Closure.CKMExactWitnesses as ExactCKM
import DASHI.Physics.Closure.CKMEntryField as CKMField
import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.Closure.DiscreteBianchiIdentitySurface as DBI
import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as GRBianchi
import DASHI.Physics.Closure.HiggsSymmetryBreakingReceipt as Higgs
import DASHI.Physics.Closure.Gate2SpectralGapMath as Gate2Math
import DASHI.Physics.Closure.Gate2ActualSelectedCarrierBundle as Gate2Selected
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YangMillsFieldEquationReceipt as YMReceipt
import DASHI.Physics.Closure.SpectralGapRefinementStability as Spectral
import DASHI.Physics.GR.EinsteinTensor as Einstein
import DASHI.Physics.GR.StressEnergyCompatibility as StressEnergy
import DASHI.Physics.YM.BiunitaryDiagonalization as Biunitary
import DASHI.Physics.YM.FroggattNielsenExpansion as FN

------------------------------------------------------------------------
-- Gate 2: spectral-gap refinement program.

data SpectralGapProofProgramStatus : Set where
  boundaryRecordedNoPromotion :
    SpectralGapProofProgramStatus

data SpectralGapProofProgramOpenObligation : Set where
  missingFiniteCoercivity :
    SpectralGapProofProgramOpenObligation

  missingGapRefinementInequality :
    SpectralGapProofProgramOpenObligation

  missingColimitGapLift :
    SpectralGapProofProgramOpenObligation

  missingGate2Promotion :
    SpectralGapProofProgramOpenObligation

canonicalSpectralGapProofProgramOpenObligations :
  List SpectralGapProofProgramOpenObligation
canonicalSpectralGapProofProgramOpenObligations =
  missingFiniteCoercivity
  ∷ missingGapRefinementInequality
  ∷ missingColimitGapLift
  ∷ missingGate2Promotion
  ∷ []

record FiniteCoercivity : Setω where
  field
    spectralToolkit :
      FSG.FiniteSpectralGapToolkit

    lowerBoundName :
      String

    lowerBoundNameIsCanonical :
      lowerBoundName ≡ "finite-gap-lower-bound"

    lowerBoundRecorded :
      Bool

    lowerBoundRecordedIsTrue :
      lowerBoundRecorded ≡ true

    coercivityBoundary :
      List String

open FiniteCoercivity public

record GapRefinementInequality : Setω where
  field
    spectralGapRefinementReceipt :
      Spectral.SpectralGapRefinementStabilityReceipt

    monotoneRecorded :
      Bool

    monotoneRecordedIsTrue :
      monotoneRecorded ≡ true

    lowerBoundPersistenceRecorded :
      Bool

    lowerBoundPersistenceRecordedIsTrue :
      lowerBoundPersistenceRecorded ≡ true

    refinementBoundary :
      List String

open GapRefinementInequality public

record ColimitGapLift : Setω where
  field
    finiteToolkit :
      FSG.FiniteSpectralGapToolkit

    limitWitness :
      InductiveLimit.NatColimitWitness (FSG.diagram finiteToolkit)

    limitCompatibilityRecorded :
      Bool

    limitCompatibilityRecordedIsTrue :
      limitCompatibilityRecorded ≡ true

    colimitGapRecorded :
      Bool

    colimitGapRecordedIsTrue :
      colimitGapRecorded ≡ true

    liftBoundary :
      List String

open ColimitGapLift public

record SpectralGapProofProgram : Setω where
  field
    finiteCoercivity :
      FiniteCoercivity

    gapRefinementInequality :
      GapRefinementInequality

    colimitGapLift :
      ColimitGapLift

    gate2SpectralGapMathReceipt :
      Gate2Math.Gate2SpectralGapMathReceipt

    gate2ActualSelectedCarrierBundleReceipt :
      Gate2Selected.Gate2ActualSelectedCarrierBundleReceipt

    gate2Promoted :
      Bool

    gate2PromotedIsFalse :
      gate2Promoted ≡ false

    openObligations :
      List SpectralGapProofProgramOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalSpectralGapProofProgramOpenObligations

    proofBoundary :
      List String

open SpectralGapProofProgram public

canonicalFiniteCoercivity : FiniteCoercivity
canonicalFiniteCoercivity =
  record
    { spectralToolkit =
        Spectral.canonicalSpectralGapFiniteToolkit
    ; lowerBoundName =
        "finite-gap-lower-bound"
    ; lowerBoundNameIsCanonical =
        refl
    ; lowerBoundRecorded =
        true
    ; lowerBoundRecordedIsTrue =
        refl
    ; coercivityBoundary =
        "The finite spectral-gap toolkit supplies the finite coercive anchor"
        ∷ "Lower-bound persistence is staged before any continuum lifting"
        ∷ []
    }

canonicalGapRefinementInequality : GapRefinementInequality
canonicalGapRefinementInequality =
  record
    { spectralGapRefinementReceipt =
        Spectral.canonicalSpectralGapRefinementStabilityReceipt
    ; monotoneRecorded =
        true
    ; monotoneRecordedIsTrue =
        refl
    ; lowerBoundPersistenceRecorded =
        true
    ; lowerBoundPersistenceRecordedIsTrue =
        refl
    ; refinementBoundary =
        "Refinement monotonicity is recorded as the reusable stability shape"
        ∷ "No continuum Yang-Mills spectral theorem is promoted here"
        ∷ []
    }

canonicalColimitGapLift : ColimitGapLift
canonicalColimitGapLift =
  record
    { finiteToolkit =
        Spectral.canonicalSpectralGapFiniteToolkit
    ; limitWitness =
        FSG.limitWitness Spectral.canonicalSpectralGapFiniteToolkit
    ; limitCompatibilityRecorded =
        true
    ; limitCompatibilityRecordedIsTrue =
        refl
    ; colimitGapRecorded =
        true
    ; colimitGapRecordedIsTrue =
        refl
    ; liftBoundary =
        "The Nat-directed colimit witness is consumed as the limit anchor"
        ∷ "Finite-to-limit transfer remains a boundary interface only"
        ∷ []
    }

canonicalSpectralGapProofProgram : SpectralGapProofProgram
canonicalSpectralGapProofProgram =
  record
    { finiteCoercivity = canonicalFiniteCoercivity
    ; gapRefinementInequality = canonicalGapRefinementInequality
    ; colimitGapLift = canonicalColimitGapLift
    ; gate2SpectralGapMathReceipt =
        Gate2Math.canonicalGate2SpectralGapMathReceipt
    ; gate2ActualSelectedCarrierBundleReceipt =
        Gate2Selected.canonicalGate2ActualSelectedCarrierBundleReceipt
    ; gate2Promoted = false
    ; gate2PromotedIsFalse = refl
    ; openObligations = canonicalSpectralGapProofProgramOpenObligations
    ; openObligationsAreCanonical = refl
    ; proofBoundary =
        "Gate 2 is packaged as finite coercivity, refinement monotonicity, and colimit lift"
        ∷ "The actual selected-carrier Gate 2 bundle is threaded through the blueprint as a typed receipt"
        ∷ "The theorem-shaped lemma family is factored into Gate2SpectralGapMath"
        ∷ "The real carrier theorem remains blocked at SelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ []
    }

------------------------------------------------------------------------
-- Gate 3: non-flat Yang-Mills geometry program.

data YangMillsNonFlatGeometryProgramStatus : Set where
  boundaryRecordedNoPromotion :
    YangMillsNonFlatGeometryProgramStatus

data YangMillsNonFlatGeometryProgramOpenObligation : Set where
  missingDiscreteForms :
    YangMillsNonFlatGeometryProgramOpenObligation

  missingConnectionOnDepth :
    YangMillsNonFlatGeometryProgramOpenObligation

  missingCurvatureNonFlatness :
    YangMillsNonFlatGeometryProgramOpenObligation

  missingVariationPairing :
    YangMillsNonFlatGeometryProgramOpenObligation

  missingGate3Promotion :
    YangMillsNonFlatGeometryProgramOpenObligation

canonicalYangMillsNonFlatGeometryProgramOpenObligations :
  List YangMillsNonFlatGeometryProgramOpenObligation
canonicalYangMillsNonFlatGeometryProgramOpenObligations =
  missingDiscreteForms
  ∷ missingConnectionOnDepth
  ∷ missingCurvatureNonFlatness
  ∷ missingVariationPairing
  ∷ missingGate3Promotion
  ∷ []

record DiscreteForms : Setω where
  field
    obstructionReceipt :
      YMObs.YangMillsFieldEquationObstruction

    discreteDerivativeRecorded :
      Bool

    discreteDerivativeRecordedIsTrue :
      discreteDerivativeRecorded ≡ true

    curvatureCarrierRecorded :
      Bool

    curvatureCarrierRecordedIsTrue :
      curvatureCarrierRecorded ≡ true

    discreteFormsBoundary :
      List String

open DiscreteForms public

record ConnectionOnDepth : Setω where
  field
    discreteForms :
      DiscreteForms

    depthLabel :
      String

    depthLabelIsCanonical :
      depthLabel ≡ "depth-9-connection-on-selected-gauge-bundle"

    connectionTargetRecorded :
      Bool

    connectionTargetRecordedIsTrue :
      connectionTargetRecorded ≡ true

    transportActionTargetRecorded :
      Bool

    transportActionTargetRecordedIsTrue :
      transportActionTargetRecorded ≡ true

    connectionBoundary :
      List String

open ConnectionOnDepth public

record CurvatureNonFlat : Setω where
  field
    connectionOnDepth :
      ConnectionOnDepth

    curvatureWitnessRecorded :
      Bool

    curvatureWitnessRecordedIsTrue :
      curvatureWitnessRecorded ≡ true

    firstNonFlatBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstNonFlatBlockerIsCanonical :
      firstNonFlatBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    curvatureBoundary :
      List String

open CurvatureNonFlat public

record VariationPairing : Setω where
  field
    connectionOnDepth :
      ConnectionOnDepth

    actionReceipt :
      YMReceipt.YangMillsFieldEquationReceipt

    variationPairingRecorded :
      Bool

    variationPairingRecordedIsTrue :
      variationPairingRecorded ≡ true

    fieldStrengthTransportRecorded :
      Bool

    fieldStrengthTransportRecordedIsTrue :
      fieldStrengthTransportRecorded ≡ true

    variationBoundary :
      List String

open VariationPairing public

record YangMillsNonFlatGeometryProgram : Setω where
  field
    discreteForms :
      DiscreteForms

    connectionOnDepth :
      ConnectionOnDepth

    curvatureNonFlat :
      CurvatureNonFlat

    variationPairing :
      VariationPairing

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    openObligations :
      List YangMillsNonFlatGeometryProgramOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYangMillsNonFlatGeometryProgramOpenObligations

    proofBoundary :
      List String

open YangMillsNonFlatGeometryProgram public

canonicalDiscreteForms : DiscreteForms
canonicalDiscreteForms =
  record
    { obstructionReceipt =
        YMObs.canonicalYangMillsFieldEquationObstruction
    ; discreteDerivativeRecorded =
        true
    ; discreteDerivativeRecordedIsTrue =
        refl
    ; curvatureCarrierRecorded =
        true
    ; curvatureCarrierRecordedIsTrue =
        refl
    ; discreteFormsBoundary =
        "Discrete forms are recorded only as finite-depth carrier targets"
        ∷ "The Yang-Mills obstruction surface remains fail-closed"
        ∷ []
    }

canonicalConnectionOnDepth : ConnectionOnDepth
canonicalConnectionOnDepth =
  record
    { discreteForms = canonicalDiscreteForms
    ; depthLabel = "depth-9-connection-on-selected-gauge-bundle"
    ; depthLabelIsCanonical = refl
    ; connectionTargetRecorded = true
    ; connectionTargetRecordedIsTrue = refl
    ; transportActionTargetRecorded = true
    ; transportActionTargetRecordedIsTrue = refl
    ; connectionBoundary =
        "Depth-9 is recorded as the selected carrier refinement target"
        ∷ "Covariant transport and field-strength action remain boundary targets"
        ∷ []
    }

canonicalCurvatureNonFlat : CurvatureNonFlat
canonicalCurvatureNonFlat =
  record
    { connectionOnDepth = canonicalConnectionOnDepth
    ; curvatureWitnessRecorded = true
    ; curvatureWitnessRecordedIsTrue = refl
    ; firstNonFlatBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; firstNonFlatBlockerIsCanonical = refl
    ; curvatureBoundary =
        "The non-flat curvature target is recorded on the depth-9 connection"
        ∷ "The strict obstruction remains missingNonFlatSFGCSite2DConnectionCurvature"
        ∷ []
    }

canonicalVariationPairing : VariationPairing
canonicalVariationPairing =
  record
    { connectionOnDepth = canonicalConnectionOnDepth
    ; actionReceipt = YMReceipt.canonicalYangMillsFieldEquationReceipt
    ; variationPairingRecorded = true
    ; variationPairingRecordedIsTrue = refl
    ; fieldStrengthTransportRecorded = true
    ; fieldStrengthTransportRecordedIsTrue = refl
    ; variationBoundary =
        "The Yang-Mills receipt is used as the variational anchor"
        ∷ "The exact variation pairing remains a boundary target rather than a promotion"
        ∷ []
    }

canonicalYangMillsNonFlatGeometryProgram :
  YangMillsNonFlatGeometryProgram
canonicalYangMillsNonFlatGeometryProgram =
  record
    { discreteForms = canonicalDiscreteForms
    ; connectionOnDepth = canonicalConnectionOnDepth
    ; curvatureNonFlat = canonicalCurvatureNonFlat
    ; variationPairing = canonicalVariationPairing
    ; gate3Promoted = false
    ; gate3PromotedIsFalse = refl
    ; openObligations =
        canonicalYangMillsNonFlatGeometryProgramOpenObligations
    ; openObligationsAreCanonical = refl
    ; proofBoundary =
        "Gate 3 is packaged as discrete forms, depth-9 connection, non-flat curvature, and variation pairing"
        ∷ "The obstruction remains fail-closed at the exact non-flat curvature and variation tokens"
        ∷ []
    }

------------------------------------------------------------------------
-- Gate 4: contracted Bianchi / stress-energy compatibility program.

data GRContractedBianchiProgramStatus : Set where
  boundaryRecordedNoPromotion :
    GRContractedBianchiProgramStatus

data GRContractedBianchiProgramOpenObligation : Set where
  missingContractedBianchiIdentity :
    GRContractedBianchiProgramOpenObligation

  missingStressEnergyFromLagrangian :
    GRContractedBianchiProgramOpenObligation

  missingOnShellStressEnergyConservation :
    GRContractedBianchiProgramOpenObligation

  missingStressEnergyCompatibilityProof :
    GRContractedBianchiProgramOpenObligation

canonicalGRContractedBianchiProgramOpenObligations :
  List GRContractedBianchiProgramOpenObligation
canonicalGRContractedBianchiProgramOpenObligations =
  missingContractedBianchiIdentity
  ∷ missingStressEnergyFromLagrangian
  ∷ missingOnShellStressEnergyConservation
  ∷ missingStressEnergyCompatibilityProof
  ∷ []

record ContractedBianchi : Setω where
  field
    einsteinSurface :
      Einstein.EinsteinTensorSurface

    discreteBianchiSurface :
      DBI.DiscreteBianchiIdentitySurface

    contractedBianchiRecorded :
      Bool

    contractedBianchiRecordedIsTrue :
      contractedBianchiRecorded ≡ true

    bianchiBoundary :
      List String

open ContractedBianchi public

record StressEnergyFromLagrangian : Setω where
  field
    stressEnergySurface :
      StressEnergy.StressEnergyCompatibilitySurface

    sourceReceipt :
      EEC.W4MatterStressEnergyInterfaceMissingField

    sourceReceiptIsCanonical :
      sourceReceipt ≡ EEC.missingW4AnchorArtifactReceiptForMatterStress

    lagrangianRecorded :
      Bool

    lagrangianRecordedIsTrue :
      lagrangianRecorded ≡ true

    lagrangianBoundary :
      List String

open StressEnergyFromLagrangian public

record OnShellStressEnergyConservation : Setω where
  field
    stressEnergyFromLagrangian :
      StressEnergyFromLagrangian

    conservationRecorded :
      Bool

    conservationRecordedIsTrue :
      conservationRecorded ≡ true

    conservationBoundary :
      List String

open OnShellStressEnergyConservation public

record StressEnergyCompatibilityProof : Setω where
  field
    contractedBianchi :
      ContractedBianchi

    onShellConservation :
      OnShellStressEnergyConservation

    compatibilitySurface :
      StressEnergy.StressEnergyCompatibilitySurface

    compatibilityPromoted :
      Bool

    compatibilityPromotedIsFalse :
      compatibilityPromoted ≡ false

    proofBoundary :
      List String

open StressEnergyCompatibilityProof public

canonicalContractedBianchi : ContractedBianchi
canonicalContractedBianchi =
  record
    { einsteinSurface = Einstein.canonicalEinsteinTensorSurface
    ; discreteBianchiSurface = DBI.canonicalDiscreteBianchiIdentitySurface
    ; contractedBianchiRecorded = true
    ; contractedBianchiRecordedIsTrue = refl
    ; bianchiBoundary =
        "The Einstein tensor surface already reduces contracted Bianchi to the canonical local zero table"
        ∷ "The discrete Bianchi surface keeps the adapter boundary explicit"
        ∷ []
    }

canonicalStressEnergyFromLagrangian : StressEnergyFromLagrangian
canonicalStressEnergyFromLagrangian =
  record
    { stressEnergySurface = StressEnergy.canonicalStressEnergyCompatibilitySurface
    ; sourceReceipt = EEC.missingW4AnchorArtifactReceiptForMatterStress
    ; sourceReceiptIsCanonical = refl
    ; lagrangianRecorded = true
    ; lagrangianRecordedIsTrue = refl
    ; lagrangianBoundary =
        "The W4 stress-energy compatibility surface is used as the sourced target"
        ∷ "The missing W4 anchor artifact remains explicit"
        ∷ []
    }

canonicalOnShellStressEnergyConservation :
  OnShellStressEnergyConservation
canonicalOnShellStressEnergyConservation =
  record
    { stressEnergyFromLagrangian = canonicalStressEnergyFromLagrangian
    ; conservationRecorded = true
    ; conservationRecordedIsTrue = refl
    ; conservationBoundary =
        "On-shell conservation is recorded as the compatibility target"
        ∷ "No actual matter-sector closure is fabricated here"
        ∷ []
    }

canonicalStressEnergyCompatibilityProof :
  StressEnergyCompatibilityProof
canonicalStressEnergyCompatibilityProof =
  record
    { contractedBianchi = canonicalContractedBianchi
    ; onShellConservation = canonicalOnShellStressEnergyConservation
    ; compatibilitySurface =
        StressEnergy.canonicalStressEnergyCompatibilitySurface
    ; compatibilityPromoted = false
    ; compatibilityPromotedIsFalse = refl
    ; proofBoundary =
        "Gate 4 is packaged as contracted Bianchi, sourced stress-energy, and compatibility"
        ∷ "The W4 matter/stress-energy gate remains fail-closed"
        ∷ []
    }

------------------------------------------------------------------------
-- Gate 7: carrier-derived CKM/Yukawa program.

data CarrierDerivedCKMProgramStatus : Set where
  boundaryRecordedNoPromotion :
    CarrierDerivedCKMProgramStatus

data CarrierDerivedCKMProgramOpenObligation : Set where
  missingYukawaFromCarrier :
    CarrierDerivedCKMProgramOpenObligation

  missingBiUnitaryDiagonalization :
    CarrierDerivedCKMProgramOpenObligation

  missingCKMCarrierDerivedProof :
    CarrierDerivedCKMProgramOpenObligation

  missingCKMUnitaryProof :
    CarrierDerivedCKMProgramOpenObligation

canonicalCarrierDerivedCKMProgramOpenObligations :
  List CarrierDerivedCKMProgramOpenObligation
canonicalCarrierDerivedCKMProgramOpenObligations =
  missingYukawaFromCarrier
  ∷ missingBiUnitaryDiagonalization
  ∷ missingCKMCarrierDerivedProof
  ∷ missingCKMUnitaryProof
  ∷ []

record YukawaFromCarrier : Setω where
  field
    exactWitnessChain :
      Exact.CKMExactWitnessChain

    fnWitness :
      FN.FroggattNielsenWitness

    physicalWitness :
      Exact.FroggattNielsenPhysicalCKMWitness

    carrierDerivedTargetRecorded :
      Bool

    carrierDerivedTargetRecordedIsTrue :
      carrierDerivedTargetRecorded ≡ true

    yukawaBoundary :
      List String

open YukawaFromCarrier public

record BiUnitaryDiagonalization : Setω where
  field
    diagonalWitness :
      Biunitary.DiagonalBiunitaryWitness

    exactBiunitaryWitness :
      Exact.ExactBiunitaryDiagonalizationWitness

    diagonalizationRecorded :
      Bool

    diagonalizationRecordedIsTrue :
      diagonalizationRecorded ≡ true

    diagonalizationBoundary :
      List String

open BiUnitaryDiagonalization public

record CKMCarrierDerived : Setω where
  field
    yukawaFromCarrier :
      YukawaFromCarrier

    biunitaryDiagonalization :
      BiUnitaryDiagonalization

    ckmReceipt :
      CKM.CKMCarrierMixingReceipt

    carrierMixingTheoremRecorded :
      Bool

    carrierMixingTheoremRecordedIsFalse :
      carrierMixingTheoremRecorded ≡ false

    dhrYukawaCompatibilityOpen :
      Bool

    dhrYukawaCompatibilityOpenIsTrue :
      dhrYukawaCompatibilityOpen ≡ true

    carrierDerivedBoundary :
      List String

open CKMCarrierDerived public

record CKMUnitaryProof : Setω where
  field
    carrierDerived :
      CKMCarrierDerived

    residualWitness :
      Exact.UnitarityResidualWitness

    unitaryTargetRecorded :
      Bool

    unitaryTargetRecordedIsTrue :
      unitaryTargetRecorded ≡ true

    unitaryBoundary :
      List String

open CKMUnitaryProof public

record CarrierDerivedCKMProgram : Setω where
  field
    yukawaFromCarrier :
      YukawaFromCarrier

    biunitaryDiagonalization :
      BiUnitaryDiagonalization

    ckmCarrierDerived :
      CKMCarrierDerived

    ckmUnitaryProof :
      CKMUnitaryProof

    gate7Promoted :
      Bool

    gate7PromotedIsFalse :
      gate7Promoted ≡ false

    openObligations :
      List CarrierDerivedCKMProgramOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalCarrierDerivedCKMProgramOpenObligations

    carrierDerivedBoundary :
      List String

open CarrierDerivedCKMProgram public

canonicalYukawaFromCarrier : YukawaFromCarrier
canonicalYukawaFromCarrier =
  record
    { exactWitnessChain = Exact.canonicalCKMExactWitnessChain
    ; fnWitness = FN.canonicalFroggattNielsenWitness
    ; physicalWitness = Exact.canonicalFroggattNielsenPhysicalCKMWitness
    ; carrierDerivedTargetRecorded = true
    ; carrierDerivedTargetRecordedIsTrue = refl
    ; yukawaBoundary =
        "The exact CKM witness chain is used as the carrier-side anchor"
        ∷ "The Froggatt-Nielsen witness packages the finite texture lane"
        ∷ "This boundary records carrier derivation as a target, not a promotion"
        ∷ []
    }

canonicalBiUnitaryDiagonalization : BiUnitaryDiagonalization
canonicalBiUnitaryDiagonalization =
  record
    { diagonalWitness = Biunitary.canonicalDiagonalBiunitaryWitness
    ; exactBiunitaryWitness =
        Exact.canonicalExactBiunitaryDiagonalizationWitness
    ; diagonalizationRecorded = true
    ; diagonalizationRecordedIsTrue = refl
    ; diagonalizationBoundary =
        "The diagonal biunitary identity witness is concrete in the repo"
        ∷ "The exact general CKM diagonalization remains open"
        ∷ []
    }

canonicalCKMCarrierDerived : CKMCarrierDerived
canonicalCKMCarrierDerived =
  record
    { yukawaFromCarrier = canonicalYukawaFromCarrier
    ; biunitaryDiagonalization = canonicalBiUnitaryDiagonalization
    ; ckmReceipt = CKM.canonicalCKMCarrierMixingReceipt
    ; carrierMixingTheoremRecorded = false
    ; carrierMixingTheoremRecordedIsFalse = refl
    ; dhrYukawaCompatibilityOpen = true
    ; dhrYukawaCompatibilityOpenIsTrue = refl
    ; carrierDerivedBoundary =
        "The canonical CKM carrier-mixing receipt is threaded as the compatibility anchor"
        ∷ "Carrier-derived CKM remains a boundary program rather than a proved internal theorem"
        ∷ []
    }

canonicalCKMUnitaryProof : CKMUnitaryProof
canonicalCKMUnitaryProof =
  record
    { carrierDerived = canonicalCKMCarrierDerived
    ; residualWitness = Exact.canonicalUnitarityResidualWitness
    ; unitaryTargetRecorded = true
    ; unitaryTargetRecordedIsTrue = refl
    ; unitaryBoundary =
        "The exact unitarity residual witness is threaded from the existing exact witness chain"
        ∷ "This stays fail-closed at the carrier-derived theorem boundary"
        ∷ []
    }

canonicalCarrierDerivedCKMProgram :
  CarrierDerivedCKMProgram
canonicalCarrierDerivedCKMProgram =
  record
    { yukawaFromCarrier = canonicalYukawaFromCarrier
    ; biunitaryDiagonalization = canonicalBiUnitaryDiagonalization
    ; ckmCarrierDerived = canonicalCKMCarrierDerived
    ; ckmUnitaryProof = canonicalCKMUnitaryProof
    ; gate7Promoted = false
    ; gate7PromotedIsFalse = refl
    ; openObligations = canonicalCarrierDerivedCKMProgramOpenObligations
    ; openObligationsAreCanonical = refl
    ; carrierDerivedBoundary =
        "Gate 7 is packaged as carrier Yukawa extraction, biunitary diagonalization, CKM derivation, and unitarity"
        ∷ "The exact carrier-derived theorem remains blocked by the existing DHR/Yukawa compatibility frontier"
        ∷ []
    }

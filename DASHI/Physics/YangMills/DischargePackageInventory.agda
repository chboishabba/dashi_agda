module DASHI.Physics.YangMills.DischargePackageInventory where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
import DASHI.Physics.YangMills.LocalLatticeDischargePipeline as LocalLattice
import DASHI.Physics.YangMills.YangMillsDischargeClosure as Closure

-- ── DischargeStatus ──────────────────────────────────────────────────
-- Requisite status vocabulary for honest audit of proof status:
--   • provedInternalReducer: all inputs explicit, no hidden source leaves
--   • mixedReducer: some proof-bearing structure, but still consumes source/model leaves
--   • conditionalPackage: typed assumption package, not discharged
--   • sourceImport: paper/import-facing leaf
--   • conditionalPipeline: composes packages into downstream theorem, not a proof of leaves
data DischargeStatus : Set where
  provedInternalReducer : DischargeStatus
  mixedReducer          : DischargeStatus
  conditionalPackage    : DischargeStatus
  sourceImport          : DischargeStatus
  conditionalPipeline   : DischargeStatus
  standardArithmeticAdapter : DischargeStatus

-- ── DischargePackageRow ──────────────────────────────────────────────
record DischargePackageRow : Set where
  field
    packageName         : String
    status              : DischargeStatus
    sourceLeaves        : List String
    constructedReducers : String
    downstreamConsumer  : String
    promotesClay        : Bool

-- ── Package Rows ─────────────────────────────────────────────────────

stepVSourceAnalyticInputsRow : DischargePackageRow
stepVSourceAnalyticInputsRow = record
  { packageName         = "StepVSourceAnalyticInputs"
  ; status              = conditionalPackage
  ; sourceLeaves        = "P06 animal counting" ∷ "P10 large-field activity" ∷ "P11 absorption condition" ∷ "P33a uniform link ellipticity" ∷ []
  ; constructedReducers = "None (pure inputs)"
  ; downstreamConsumer  = "StepVSpatialKPCertificate"
  ; promotesClay        = false
  }

stepVInternalReducersRow : DischargePackageRow
stepVInternalReducersRow = record
  { packageName         = "StepVInternalReducers"
  ; status              = provedInternalReducer
  ; sourceLeaves        = []
  ; constructedReducers = "lemmaV-1 (diameter compatibility), lemmaV-2 (all-diameter KP), StepVMarginFromP33bAndArithmetic"
  ; downstreamConsumer  = "StepVSpatialKPCertificate"
  ; promotesClay        = false
  }

stepVToRGDischargePackageRow : DischargePackageRow
stepVToRGDischargePackageRow = record
  { packageName         = "StepVToRGDischargePackage"
  ; status              = mixedReducer
  ; sourceLeaves        = "StepVSpatialKPCertificate" ∷ []
  ; constructedReducers = "stepVToDLRSmallness, stepVToA2, a2ToB6Influence, b6ToRGCauchy, dlrSmallnessAndCrossScaleToUniformLSI"
  ; downstreamConsumer  = "RGFromStepVDischargePackage"
  ; promotesClay        = false
  }

fixedLatticeMassGapPackageRow : DischargePackageRow
fixedLatticeMassGapPackageRow = record
  { packageName         = "FixedLatticeMassGapPackage"
  ; status              = conditionalPackage
  ; sourceLeaves        = "P15 lattice spectral gap" ∷ []
  ; constructedReducers = "FixedLatticeMassGapFromStepV (converts uniform LSI and spectral gap)"
  ; downstreamConsumer  = "ThermodynamicLimitPackage"
  ; promotesClay        = false
  }

thermodynamicLimitPackageRow : DischargePackageRow
thermodynamicLimitPackageRow = record
  { packageName         = "ThermodynamicLimitPackage"
  ; status              = conditionalPackage
  ; sourceLeaves        = "P27 thermodynamic limit uniqueness" ∷ "tightness" ∷ "preservation of clustering and spectral gap" ∷ []
  ; constructedReducers = "currentThermodynamicLimitPackage"
  ; downstreamConsumer  = "ContinuumLimitPackage"
  ; promotesClay        = false
  }

continuumLimitPackageRow : DischargePackageRow
continuumLimitPackageRow = record
  { packageName         = "ContinuumLimitPackage"
  ; status              = conditionalPackage
  ; sourceLeaves        = "LatticeSpacingTendsToZero" ∷ "ContinuumTightness" ∷ "InfiniteVolumeMassGapToContinuumSubsequence" ∷ "MassGapSurvivesCutoffRemoval" ∷ "OSReflectionPositivityPreserved" ∷ "EuclideanCovarianceRestored" ∷ []
  ; constructedReducers = "currentContinuumLimitPackage, ContinuumMassGapFromThermodynamicMassGap = MassGapSurvivesCutoffRemoval ∘ InfiniteVolumeMassGapToContinuumSubsequence, ContinuumLimitFromInfiniteVolume"
  ; downstreamConsumer  = "OSWightmanEndpointPackage"
  ; promotesClay        = false
  }

osWightmanEndpointPackageRow : DischargePackageRow
osWightmanEndpointPackageRow = record
  { packageName         = "OSWightmanEndpointPackage"
  ; status              = conditionalPackage
  ; sourceLeaves        = "OSInputsFromContinuumLimit" ∷ "WightmanTheoryFromOS" ∷ "PhysicalMassGapFromContinuumMassGap" ∷ []
  ; constructedReducers = "currentOSWightmanEndpointPackage, YangMillsEndpointFromContinuum"
  ; downstreamConsumer  = "ConditionalYangMillsPipelineFromDischargePackages"
  ; promotesClay        = false
  }

conditionalYangMillsPipelineRow : DischargePackageRow
conditionalYangMillsPipelineRow = record
  { packageName         = "ConditionalYangMillsPipelineFromDischargePackages"
  ; status              = conditionalPipeline
  ; sourceLeaves        = "All antecedent package leaves combined" ∷ []
  ; constructedReducers = "Full typed pipeline mapping from Step V through Wightman endpoints"
  ; downstreamConsumer  = "YangMillsQuantumFieldTheory × PhysicalMassGap (terminal endpoint)"
  ; promotesClay        = false
  }

fromNatRow : DischargePackageRow
fromNatRow = record
  { packageName         = "fromNat"
  ; status              = standardArithmeticAdapter
  ; sourceLeaves        = []
  ; constructedReducers = "Postulated namespace decoupling bridge"
  ; downstreamConsumer  = "BalabanLargeFieldSuppression and other numeric layers"
  ; promotesClay        = false
  }

natPowerDecayMonotoneRow : DischargePackageRow
natPowerDecayMonotoneRow = record
  { packageName         = "natPowerDecayMonotone"
  ; status              = standardArithmeticAdapter
  ; sourceLeaves        = []
  ; constructedReducers = "Numeric monotonicity proof"
  ; downstreamConsumer  = "BalabanLargeFieldSuppression"
  ; promotesClay        = false
  }

p10AnalyticLeavesRow : DischargePackageRow
p10AnalyticLeavesRow = record
  { packageName         = "P10AnalyticLeaves"
  ; status              = conditionalPackage
  ; sourceLeaves        = "LargeFieldCoercivityLeaf" ∷ "LargeFieldActivitySuppressionLeaf" ∷ []
  ; constructedReducers = "P10FromAnalyticLeavesAndArithmetic, LargeFieldDecayByComplexityFromCoercivity, LargeFieldDecayByDiameterFromComplexity"
  ; downstreamConsumer  = "P10LargeFieldSuppressionPackage / StepVFromDischargePackages"
  ; promotesClay        = false
  }

localLatticeAnalyticDischargePackageRow : DischargePackageRow
localLatticeAnalyticDischargePackageRow = record
  { packageName         = "LocalLatticeAnalyticDischargePackage"
  ; status              = conditionalPackage
  ; sourceLeaves        = "P06 counting, P10 large-field suppression, P33 small-field ellipticity, P07/P09 KP summability margin, P08/P11 positivity and absorption" ∷ []
  ; constructedReducers = "OwnedLocalLatticeLemmaStack exposes the local lattice chain into LocalLatticeAnalyticDischargePackage, then LocalLatticeStepVFromAnalyticDischarge and YangMillsEndpointFromLocalLatticeAndTransferPackages consume it."
  ; downstreamConsumer  = "StepVSpatialKPCertificate / YangMillsQuantumFieldTheory × PhysicalMassGap"
  ; promotesClay        = false
  }

downstreamAnalyticTransferPackageRow : DischargePackageRow
downstreamAnalyticTransferPackageRow = record
  { packageName         = "DownstreamAnalyticTransferPackage"
  ; status              = conditionalPackage
  ; sourceLeaves        = "RG transfer, fixed-lattice gap, thermodynamic, continuum, OS/Wightman endpoint" ∷ []
  ; constructedReducers = "DownstreamEndpointFromTransferPackage"
  ; downstreamConsumer  = "YangMillsFullDischargePackage"
  ; promotesClay        = false
  }

yangMillsFullDischargePackageRow : DischargePackageRow
yangMillsFullDischargePackageRow = record
  { packageName         = "YangMillsFullDischargePackage"
  ; status              = conditionalPipeline
  ; sourceLeaves        = "LocalLatticeAnalyticDischargePackage, DownstreamAnalyticTransferPackage" ∷ []
  ; constructedReducers = "YangMillsEndpointFromFullDischargePackage now concretely composes YangMillsEndpointFromLocalLatticeAndTransferPackages with extracted downstream transfer fields."
  ; downstreamConsumer  = "YangMillsQuantumFieldTheory × PhysicalMassGap"
  ; promotesClay        = false
  }

p01P33CoverageLedgerRow : DischargePackageRow
p01P33CoverageLedgerRow = record
  { packageName         = "P01P33CoverageLedger"
  ; status              = provedInternalReducer
  ; sourceLeaves        = []
  ; constructedReducers = "AllPTheoremCoverageRowsNoClayPromotion"
  ; downstreamConsumer  = "Self-contained metadata audit ledger"
  ; promotesClay        = false
  }

-- ── Inventory ────────────────────────────────────────────────────────

dischargePackageInventory : List DischargePackageRow
dischargePackageInventory =
  stepVSourceAnalyticInputsRow ∷
  stepVInternalReducersRow ∷
  stepVToRGDischargePackageRow ∷
  fixedLatticeMassGapPackageRow ∷
  thermodynamicLimitPackageRow ∷
  continuumLimitPackageRow ∷
  osWightmanEndpointPackageRow ∷
  conditionalYangMillsPipelineRow ∷
  fromNatRow ∷
  natPowerDecayMonotoneRow ∷
  p10AnalyticLeavesRow ∷
  localLatticeAnalyticDischargePackageRow ∷
  downstreamAnalyticTransferPackageRow ∷
  yangMillsFullDischargePackageRow ∷
  p01P33CoverageLedgerRow ∷ []

-- ── List Membership ──────────────────────────────────────────────────

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

-- ── Helpers ──────────────────────────────────────────────────────────

isEmpty : {A : Set} → List A → Bool
isEmpty []       = true
isEmpty (_ ∷ _)  = false

not : Bool → Bool
not true  = false
not false = true

HasSourceLeaves : DischargePackageRow → Bool
HasSourceLeaves row = not (isEmpty (DischargePackageRow.sourceLeaves row))

-- ── Governance Theorems ──────────────────────────────────────────────

ProvedInternalReducerHasNoSourceLeaves :
  (row : DischargePackageRow) →
  row ∈ dischargePackageInventory →
  DischargePackageRow.status row ≡ provedInternalReducer →
  HasSourceLeaves row ≡ false
ProvedInternalReducerHasNoSourceLeaves .stepVSourceAnalyticInputsRow here ()
ProvedInternalReducerHasNoSourceLeaves .stepVInternalReducersRow (there here) refl = refl
ProvedInternalReducerHasNoSourceLeaves .stepVToRGDischargePackageRow (there (there here)) ()
ProvedInternalReducerHasNoSourceLeaves .fixedLatticeMassGapPackageRow (there (there (there here))) ()
ProvedInternalReducerHasNoSourceLeaves .thermodynamicLimitPackageRow (there (there (there (there here)))) ()
ProvedInternalReducerHasNoSourceLeaves .continuumLimitPackageRow (there (there (there (there (there here))))) ()
ProvedInternalReducerHasNoSourceLeaves .osWightmanEndpointPackageRow (there (there (there (there (there (there here)))))) ()
ProvedInternalReducerHasNoSourceLeaves .conditionalYangMillsPipelineRow (there (there (there (there (there (there (there here))))))) ()
ProvedInternalReducerHasNoSourceLeaves .fromNatRow (there (there (there (there (there (there (there (there here)))))))) ()
ProvedInternalReducerHasNoSourceLeaves .natPowerDecayMonotoneRow (there (there (there (there (there (there (there (there (there here))))))))) ()
ProvedInternalReducerHasNoSourceLeaves .p10AnalyticLeavesRow (there (there (there (there (there (there (there (there (there (there here)))))))))) ()
ProvedInternalReducerHasNoSourceLeaves .localLatticeAnalyticDischargePackageRow (there (there (there (there (there (there (there (there (there (there (there here))))))))))) ()
ProvedInternalReducerHasNoSourceLeaves .downstreamAnalyticTransferPackageRow (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) ()
ProvedInternalReducerHasNoSourceLeaves .yangMillsFullDischargePackageRow (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) ()
ProvedInternalReducerHasNoSourceLeaves .p01P33CoverageLedgerRow (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))) refl = refl

ConditionalPackageDoesNotPromoteClay :
  (row : DischargePackageRow) →
  row ∈ dischargePackageInventory →
  DischargePackageRow.status row ≡ conditionalPackage →
  DischargePackageRow.promotesClay row ≡ false
ConditionalPackageDoesNotPromoteClay .stepVSourceAnalyticInputsRow here refl = refl
ConditionalPackageDoesNotPromoteClay .stepVInternalReducersRow (there here) ()
ConditionalPackageDoesNotPromoteClay .stepVToRGDischargePackageRow (there (there here)) ()
ConditionalPackageDoesNotPromoteClay .fixedLatticeMassGapPackageRow (there (there (there here))) refl = refl
ConditionalPackageDoesNotPromoteClay .thermodynamicLimitPackageRow (there (there (there (there here)))) refl = refl
ConditionalPackageDoesNotPromoteClay .continuumLimitPackageRow (there (there (there (there (there here))))) refl = refl
ConditionalPackageDoesNotPromoteClay .osWightmanEndpointPackageRow (there (there (there (there (there (there here)))))) refl = refl
ConditionalPackageDoesNotPromoteClay .conditionalYangMillsPipelineRow (there (there (there (there (there (there (there here))))))) ()
ConditionalPackageDoesNotPromoteClay .fromNatRow (there (there (there (there (there (there (there (there here)))))))) ()
ConditionalPackageDoesNotPromoteClay .natPowerDecayMonotoneRow (there (there (there (there (there (there (there (there (there here))))))))) ()
ConditionalPackageDoesNotPromoteClay .p10AnalyticLeavesRow (there (there (there (there (there (there (there (there (there (there here)))))))))) refl = refl
ConditionalPackageDoesNotPromoteClay .localLatticeAnalyticDischargePackageRow (there (there (there (there (there (there (there (there (there (there (there here))))))))))) refl = refl
ConditionalPackageDoesNotPromoteClay .downstreamAnalyticTransferPackageRow (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) refl = refl
ConditionalPackageDoesNotPromoteClay .yangMillsFullDischargePackageRow (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) ()
ConditionalPackageDoesNotPromoteClay .p01P33CoverageLedgerRow (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))) ()

MixedReducerDoesNotPromoteClay :
  (row : DischargePackageRow) →
  row ∈ dischargePackageInventory →
  DischargePackageRow.status row ≡ mixedReducer →
  DischargePackageRow.promotesClay row ≡ false
MixedReducerDoesNotPromoteClay .stepVSourceAnalyticInputsRow here ()
MixedReducerDoesNotPromoteClay .stepVInternalReducersRow (there here) ()
MixedReducerDoesNotPromoteClay .stepVToRGDischargePackageRow (there (there here)) refl = refl
MixedReducerDoesNotPromoteClay .fixedLatticeMassGapPackageRow (there (there (there here))) ()
MixedReducerDoesNotPromoteClay .thermodynamicLimitPackageRow (there (there (there (there here)))) ()
MixedReducerDoesNotPromoteClay .continuumLimitPackageRow (there (there (there (there (there here))))) ()
MixedReducerDoesNotPromoteClay .osWightmanEndpointPackageRow (there (there (there (there (there (there here)))))) ()
MixedReducerDoesNotPromoteClay .conditionalYangMillsPipelineRow (there (there (there (there (there (there (there here))))))) ()
MixedReducerDoesNotPromoteClay .fromNatRow (there (there (there (there (there (there (there (there here)))))))) ()
MixedReducerDoesNotPromoteClay .natPowerDecayMonotoneRow (there (there (there (there (there (there (there (there (there here))))))))) ()
MixedReducerDoesNotPromoteClay .p10AnalyticLeavesRow (there (there (there (there (there (there (there (there (there (there here)))))))))) ()
MixedReducerDoesNotPromoteClay .localLatticeAnalyticDischargePackageRow (there (there (there (there (there (there (there (there (there (there (there here))))))))))) ()
MixedReducerDoesNotPromoteClay .downstreamAnalyticTransferPackageRow (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) ()
MixedReducerDoesNotPromoteClay .yangMillsFullDischargePackageRow (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) ()
MixedReducerDoesNotPromoteClay .p01P33CoverageLedgerRow (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))) ()

ConditionalPipelineDoesNotDischargePackages :
  (row : DischargePackageRow) →
  row ∈ dischargePackageInventory →
  DischargePackageRow.status row ≡ conditionalPipeline →
  HasSourceLeaves row ≡ true →
  DischargePackageRow.promotesClay row ≡ false
ConditionalPipelineDoesNotDischargePackages .stepVSourceAnalyticInputsRow here () _
ConditionalPipelineDoesNotDischargePackages .stepVInternalReducersRow (there here) () _
ConditionalPipelineDoesNotDischargePackages .stepVToRGDischargePackageRow (there (there here)) () _
ConditionalPipelineDoesNotDischargePackages .fixedLatticeMassGapPackageRow (there (there (there here))) () _
ConditionalPipelineDoesNotDischargePackages .thermodynamicLimitPackageRow (there (there (there (there here)))) () _
ConditionalPipelineDoesNotDischargePackages .continuumLimitPackageRow (there (there (there (there (there here))))) () _
ConditionalPipelineDoesNotDischargePackages .osWightmanEndpointPackageRow (there (there (there (there (there (there here)))))) () _
ConditionalPipelineDoesNotDischargePackages .conditionalYangMillsPipelineRow (there (there (there (there (there (there (there here))))))) refl _ = refl
ConditionalPipelineDoesNotDischargePackages .fromNatRow (there (there (there (there (there (there (there (there here)))))))) () _
ConditionalPipelineDoesNotDischargePackages .natPowerDecayMonotoneRow (there (there (there (there (there (there (there (there (there here))))))))) () _
ConditionalPipelineDoesNotDischargePackages .p10AnalyticLeavesRow (there (there (there (there (there (there (there (there (there (there here)))))))))) () _
ConditionalPipelineDoesNotDischargePackages .localLatticeAnalyticDischargePackageRow (there (there (there (there (there (there (there (there (there (there (there here))))))))))) () _
ConditionalPipelineDoesNotDischargePackages .downstreamAnalyticTransferPackageRow (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) () _
ConditionalPipelineDoesNotDischargePackages .yangMillsFullDischargePackageRow (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) refl _ = refl
ConditionalPipelineDoesNotDischargePackages .p01P33CoverageLedgerRow (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))) () _

AllDischargeRowsNoClayPromotion :
  (row : DischargePackageRow) →
  row ∈ dischargePackageInventory →
  DischargePackageRow.promotesClay row ≡ false
AllDischargeRowsNoClayPromotion .stepVSourceAnalyticInputsRow here = refl
AllDischargeRowsNoClayPromotion .stepVInternalReducersRow (there here) = refl
AllDischargeRowsNoClayPromotion .stepVToRGDischargePackageRow (there (there here)) = refl
AllDischargeRowsNoClayPromotion .fixedLatticeMassGapPackageRow (there (there (there here))) = refl
AllDischargeRowsNoClayPromotion .thermodynamicLimitPackageRow (there (there (there (there here)))) = refl
AllDischargeRowsNoClayPromotion .continuumLimitPackageRow (there (there (there (there (there here))))) = refl
AllDischargeRowsNoClayPromotion .osWightmanEndpointPackageRow (there (there (there (there (there (there here)))))) = refl
AllDischargeRowsNoClayPromotion .conditionalYangMillsPipelineRow (there (there (there (there (there (there (there here))))))) = refl
AllDischargeRowsNoClayPromotion .fromNatRow (there (there (there (there (there (there (there (there here)))))))) = refl
AllDischargeRowsNoClayPromotion .natPowerDecayMonotoneRow (there (there (there (there (there (there (there (there (there here))))))))) = refl
AllDischargeRowsNoClayPromotion .p10AnalyticLeavesRow (there (there (there (there (there (there (there (there (there (there here)))))))))) = refl
AllDischargeRowsNoClayPromotion .localLatticeAnalyticDischargePackageRow (there (there (there (there (there (there (there (there (there (there (there here))))))))))) = refl
AllDischargeRowsNoClayPromotion .downstreamAnalyticTransferPackageRow (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) = refl
AllDischargeRowsNoClayPromotion .yangMillsFullDischargePackageRow (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) = refl
AllDischargeRowsNoClayPromotion .p01P33CoverageLedgerRow (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))) = refl

-- ── Leaf Sorting Buckets ─────────────────────────────────────────────

finiteCombinatoricsLeaves : String
finiteCombinatoricsLeaves =
  "P01, P02, P03 (Diestel graph/tree path/distance properties), P06 (reduced skeleton complexity, decoration multiplicity, polymer decomposition animal counting)"

constantArithmeticLeaves : String
constantArithmeticLeaves =
  "P04, P05 (kappa strictly positive, normalized to one), P07 (KP summability bound), P09 (entropy beaten by full decay)"

latticeRGAnalysisLeaves : String
latticeRGAnalysisLeaves =
  "P08 (p0 positive), P10 (large-field activity bound), P11 (absorption condition), P12-P15 (DLR-LSI branch: polymer decay, cross scale, uniform LSI, lattice spectral gap), P16-P18 (RG-Cauchy branch: A2 oscillation, B6 influence, RG-Cauchy summability), P19 (coupling control), P21 (anisotropy coeff quadratic bound), P23-P24 (terminal KP bound, assembly map complete), P25-P26 (uniform LSI, volume uniform mass gap), P33 (field regularity, small-field perturbation stability, positive link weights)"

continuumOSAnalysisLeaves : String
continuumOSAnalysisLeaves =
  "P20 (anisotropic subspace classification), P22 (insertion integrability bound), P27 (thermodynamic limit unique), P28 (rotational Ward identity), P29 (symanzik breaking decomposition), P30 (OS1 Euclidean covariance), P31 (Wightman reconstruction with mass gap), P32 (triangular mixing preventive lock)"

-- ── Local P10 Governance Audit Lemmas ────────────────────────────────
P10AnalyticLeavesAreConditional :
  DischargePackageRow.status p10AnalyticLeavesRow ≡ conditionalPackage
P10AnalyticLeavesAreConditional = refl

P10AnalyticLeavesVisible :
  DischargePackageRow.sourceLeaves p10AnalyticLeavesRow
    ≡ "LargeFieldCoercivityLeaf" ∷
      "LargeFieldActivitySuppressionLeaf" ∷
      []
P10AnalyticLeavesVisible = refl

P10AnalyticLeavesDoNotPromoteClay :
  DischargePackageRow.promotesClay p10AnalyticLeavesRow ≡ false
P10AnalyticLeavesDoNotPromoteClay = refl

LocalLatticeAnalyticLeavesAreConditional :
  DischargePackageRow.status localLatticeAnalyticDischargePackageRow ≡ conditionalPackage
LocalLatticeAnalyticLeavesAreConditional = refl

LocalLatticeAnalyticLeavesDoNotPromoteClay :
  DischargePackageRow.promotesClay localLatticeAnalyticDischargePackageRow ≡ false
LocalLatticeAnalyticLeavesDoNotPromoteClay = refl

DownstreamAnalyticTransferPackageIsConditional :
  DischargePackageRow.status downstreamAnalyticTransferPackageRow ≡ conditionalPackage
DownstreamAnalyticTransferPackageIsConditional = refl

DownstreamAnalyticTransferPackageDoesNotPromoteClay :
  DischargePackageRow.promotesClay downstreamAnalyticTransferPackageRow ≡ false
DownstreamAnalyticTransferPackageDoesNotPromoteClay = refl

YangMillsFullDischargePackageIsConditionalPipeline :
  DischargePackageRow.status yangMillsFullDischargePackageRow ≡ conditionalPipeline
YangMillsFullDischargePackageIsConditionalPipeline = refl

YangMillsFullDischargePackageDoesNotPromoteClay :
  DischargePackageRow.promotesClay yangMillsFullDischargePackageRow ≡ false
YangMillsFullDischargePackageDoesNotPromoteClay = refl

P01P33CoverageLedgerIsProved :
  DischargePackageRow.status p01P33CoverageLedgerRow ≡ provedInternalReducer
P01P33CoverageLedgerIsProved = refl

P01P33CoverageLedgerDoesNotPromoteClay :
  DischargePackageRow.promotesClay p01P33CoverageLedgerRow ≡ false
P01P33CoverageLedgerDoesNotPromoteClay = refl

module DASHI.Physics.YangMills.YangMillsDischargeClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import DASHI.Core.Prelude using (_×_)
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

import DASHI.Physics.YangMills.StepVAssemblyLemmaQueue as Assembly
import DASHI.Physics.YangMills.LocalLatticeDischargePipeline as LocalLattice

-- Downstream transfer mega-package
record DownstreamAnalyticTransferPackage : Set₁ where
  field
    rgTransfer : Assembly.P12P19RGTransferPackage
    fixedLatticeGap : Assembly.FixedLatticeGapDischargePackage
    thermodynamicLimit : Assembly.ThermodynamicLimitPackage
    continuumLimit : Assembly.ContinuumLimitPackage
    osWightmanEndpoint : Assembly.OSWightmanEndpointPackage
    noClayPromotion : clayYangMillsPromoted ≡ false

postulate
  postulatedDownstreamEndpointFromTransferPackage :
    Assembly.StepVSpatialKPCertificate
    → DownstreamAnalyticTransferPackage
    → Assembly.YangMillsQuantumFieldTheory × Assembly.PhysicalMassGap

DownstreamEndpointFromTransferPackage :
  Assembly.StepVSpatialKPCertificate
  → DownstreamAnalyticTransferPackage
  → Assembly.YangMillsQuantumFieldTheory × Assembly.PhysicalMassGap
DownstreamEndpointFromTransferPackage cert pkg =
  postulatedDownstreamEndpointFromTransferPackage cert pkg

-- Full YM discharge package
record YangMillsFullDischargePackage : Set₁ where
  field
    localLattice : LocalLattice.LocalLatticeAnalyticDischargePackage
    downstreamTransfer : DownstreamAnalyticTransferPackage
    noClayPromotion : clayYangMillsPromoted ≡ false

postulate
  postulatedYangMillsEndpointFromFullDischargePackage :
    YangMillsFullDischargePackage
    → Assembly.YangMillsQuantumFieldTheory × Assembly.PhysicalMassGap

YangMillsEndpointFromFullDischargePackage :
  YangMillsFullDischargePackage
  → Assembly.YangMillsQuantumFieldTheory × Assembly.PhysicalMassGap
YangMillsEndpointFromFullDischargePackage pkg =
  postulatedYangMillsEndpointFromFullDischargePackage pkg

-- ── P01–P33 Coverage Ledger ──────────────────────────────────────────

data PCoverageStatus : Set where
  internallyReduced    : PCoverageStatus
  packageReduced       : PCoverageStatus
  mixedReduced         : PCoverageStatus
  analyticLeaf         : PCoverageStatus
  continuumLeaf        : PCoverageStatus
  endpointLeaf         : PCoverageStatus

record PTheoremCoverageRow : Set where
  field
    theoremName : String
    theoremNumber : String
    coverageStatus : PCoverageStatus
    reducerOrLeaf : String
    consumedBy : String
    promotesClay : Bool

-- List membership definition for the coverage ledger
data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

p01p03Row : PTheoremCoverageRow
p01p03Row = record
  { theoremName = "TreePathAndGraphDistance"
  ; theoremNumber = "P01-P03"
  ; coverageStatus = packageReduced
  ; reducerOrLeaf = "Diestel graph/tree path/distance properties"
  ; consumedBy = "BalabanTreeDistanceDiameterCompatibility"
  ; promotesClay = false
  }

p04p05Row : PTheoremCoverageRow
p04p05Row = record
  { theoremName = "KappaStrictlyPositiveAndNormalized"
  ; theoremNumber = "P04-P05"
  ; coverageStatus = packageReduced
  ; reducerOrLeaf = "kappa positive / normalized"
  ; consumedBy = "BalabanSpatialLinkWeightLowerBound"
  ; promotesClay = false
  }

p06Row : PTheoremCoverageRow
p06Row = record
  { theoremName = "PolymerAnimalCountingBound"
  ; theoremNumber = "P06"
  ; coverageStatus = mixedReduced
  ; reducerOrLeaf = "P06ModelLeafDischargePackage"
  ; consumedBy = "BalabanPolymerDiameterEntropy"
  ; promotesClay = false
  }

p07Row : PTheoremCoverageRow
p07Row = record
  { theoremName = "KPSummabilityBound"
  ; theoremNumber = "P07"
  ; coverageStatus = packageReduced
  ; reducerOrLeaf = "P07P09FromP06P10AndMargin"
  ; consumedBy = "BalabanPolymerDiameterEntropy"
  ; promotesClay = false
  }

p08Row : PTheoremCoverageRow
p08Row = record
  { theoremName = "PZeroPositive"
  ; theoremNumber = "P08"
  ; coverageStatus = packageReduced
  ; reducerOrLeaf = "Real analysis leaf positivity wrapper"
  ; consumedBy = "BalabanPolymerDiameterEntropy"
  ; promotesClay = false
  }

p09Row : PTheoremCoverageRow
p09Row = record
  { theoremName = "EntropyBeatenByFullDecay"
  ; theoremNumber = "P09"
  ; coverageStatus = packageReduced
  ; reducerOrLeaf = "Entropy margin from diameter decay"
  ; consumedBy = "BalabanPolymerDiameterEntropy"
  ; promotesClay = false
  }

p10Row : PTheoremCoverageRow
p10Row = record
  { theoremName = "LargeFieldActivityBound"
  ; theoremNumber = "P10"
  ; coverageStatus = mixedReduced
  ; reducerOrLeaf = "P10AnalyticLeaves"
  ; consumedBy = "BalabanLargeFieldSuppression"
  ; promotesClay = false
  }

p11Row : PTheoremCoverageRow
p11Row = record
  { theoremName = "AbsorptionCondition"
  ; theoremNumber = "P11"
  ; coverageStatus = packageReduced
  ; reducerOrLeaf = "P08P11AbsorptionPackage"
  ; consumedBy = "BalabanLargeFieldSuppression"
  ; promotesClay = false
  }

p12p19Row : PTheoremCoverageRow
p12p19Row = record
  { theoremName = "RGTransferPackage"
  ; theoremNumber = "P12-P19"
  ; coverageStatus = mixedReduced
  ; reducerOrLeaf = "P12P19RGTransferPackage"
  ; consumedBy = "BalabanRGStepVLane"
  ; promotesClay = false
  }

p20p22Row : PTheoremCoverageRow
p20p22Row = record
  { theoremName = "AnisotropicClassificationAndInsertionIntegrability"
  ; theoremNumber = "P20, P22"
  ; coverageStatus = analyticLeaf
  ; reducerOrLeaf = "Subspace classification and insert bound"
  ; consumedBy = "O4CovarianceRestorationGate"
  ; promotesClay = false
  }

p21p23p26Row : PTheoremCoverageRow
p21p23p26Row = record
  { theoremName = "FixedLatticeGapPackage"
  ; theoremNumber = "P21, P23-P26"
  ; coverageStatus = mixedReduced
  ; reducerOrLeaf = "FixedLatticeGapDischargePackage"
  ; consumedBy = "StepVAssemblyLemmaQueue"
  ; promotesClay = false
  }

p27p30Row : PTheoremCoverageRow
p27p30Row = record
  { theoremName = "ThermodynamicAndContinuumLimits"
  ; theoremNumber = "P27-P30"
  ; coverageStatus = continuumLeaf
  ; reducerOrLeaf = "Thermodynamic limit uniqueness and Ward identity"
  ; consumedBy = "BalabanContinuumStabilityGate"
  ; promotesClay = false
  }

p31p32Row : PTheoremCoverageRow
p31p32Row = record
  { theoremName = "OSReconstructionAndTriangularLock"
  ; theoremNumber = "P31-P32"
  ; coverageStatus = endpointLeaf
  ; reducerOrLeaf = "OS/Wightman reconstruction and triangular lock"
  ; consumedBy = "ClayPromotionAuthorityGate"
  ; promotesClay = false
  }

p33Row : PTheoremCoverageRow
p33Row = record
  { theoremName = "FieldRegularityAndStability"
  ; theoremNumber = "P33"
  ; coverageStatus = mixedReduced
  ; reducerOrLeaf = "P33a1AnalyticDischargePackage"
  ; consumedBy = "BalabanTreeDistanceDiameterCompatibility"
  ; promotesClay = false
  }

pTheoremCoverageLedger : List PTheoremCoverageRow
pTheoremCoverageLedger =
  p01p03Row ∷
  p04p05Row ∷
  p06Row ∷
  p07Row ∷
  p08Row ∷
  p09Row ∷
  p10Row ∷
  p11Row ∷
  p12p19Row ∷
  p20p22Row ∷
  p21p23p26Row ∷
  p27p30Row ∷
  p31p32Row ∷
  p33Row ∷ []

AllPTheoremCoverageRowsNoClayPromotion :
  (row : PTheoremCoverageRow) →
  row ∈ pTheoremCoverageLedger →
  PTheoremCoverageRow.promotesClay row ≡ false
AllPTheoremCoverageRowsNoClayPromotion .p01p03Row here = refl
AllPTheoremCoverageRowsNoClayPromotion .p04p05Row (there here) = refl
AllPTheoremCoverageRowsNoClayPromotion .p06Row (there (there here)) = refl
AllPTheoremCoverageRowsNoClayPromotion .p07Row (there (there (there here))) = refl
AllPTheoremCoverageRowsNoClayPromotion .p08Row (there (there (there (there here)))) = refl
AllPTheoremCoverageRowsNoClayPromotion .p09Row (there (there (there (there (there here))))) = refl
AllPTheoremCoverageRowsNoClayPromotion .p10Row (there (there (there (there (there (there here)))))) = refl
AllPTheoremCoverageRowsNoClayPromotion .p11Row (there (there (there (there (there (there (there here))))))) = refl
AllPTheoremCoverageRowsNoClayPromotion .p12p19Row (there (there (there (there (there (there (there (there here)))))))) = refl
AllPTheoremCoverageRowsNoClayPromotion .p20p22Row (there (there (there (there (there (there (there (there (there here))))))))) = refl
AllPTheoremCoverageRowsNoClayPromotion .p21p23p26Row (there (there (there (there (there (there (there (there (there (there here)))))))))) = refl
AllPTheoremCoverageRowsNoClayPromotion .p27p30Row (there (there (there (there (there (there (there (there (there (there (there here))))))))))) = refl
AllPTheoremCoverageRowsNoClayPromotion .p31p32Row (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) = refl
AllPTheoremCoverageRowsNoClayPromotion .p33Row (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) = refl
AllPTheoremCoverageRowsNoClayPromotion row (there (there (there (there (there (there (there (there (there (there (there (there (there (there ())))))))))))))

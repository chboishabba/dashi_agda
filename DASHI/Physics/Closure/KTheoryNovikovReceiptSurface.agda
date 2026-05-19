module DASHI.Physics.Closure.KTheoryNovikovReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- K-theory / Novikov target surfaces for the GR/QFT roadmap.
--
-- This module records typed receipt targets only.  It does not prove the
-- Novikov conjecture, construct an assembly map, classify physical charges,
-- prove a six-term exact sequence, construct DHR sectors, solve mass gap,
-- calibrate Lambda, or promote a GRQFT / TOE receipt.

data KTheoryNovikovSurfaceStatus : Set where
  targetSurfaceOnlyNoPromotion :
    KTheoryNovikovSurfaceStatus

data KTheoryNovikovPromotionAuthorityToken : Set where

data AssemblyMapTarget : Set where
  coarseBaumConnesAssembly :
    AssemblyMapTarget

  novikovRationalInjectivity :
    AssemblyMapTarget

  analyticAssemblyForDASHICarrier :
    AssemblyMapTarget

canonicalAssemblyMapTargets :
  List AssemblyMapTarget
canonicalAssemblyMapTargets =
  coarseBaumConnesAssembly
  ∷ novikovRationalInjectivity
  ∷ analyticAssemblyForDASHICarrier
  ∷ []

data ChargeClassificationTarget : Set where
  kTheoryChargeGroup :
    ChargeClassificationTarget

  dhrSectorToKClassAdapter :
    ChargeClassificationTarget

  twistedKTheoryBackgroundAdapter :
    ChargeClassificationTarget

canonicalChargeClassificationTargets :
  List ChargeClassificationTarget
canonicalChargeClassificationTargets =
  kTheoryChargeGroup
  ∷ dhrSectorToKClassAdapter
  ∷ twistedKTheoryBackgroundAdapter
  ∷ []

data BulkBoundaryExactSequenceTarget : Set where
  sixTermExactSequence :
    BulkBoundaryExactSequenceTarget

  boundaryMapBulkToEdge :
    BulkBoundaryExactSequenceTarget

  exactnessWitnessForCarrierExtension :
    BulkBoundaryExactSequenceTarget

canonicalBulkBoundaryTargets :
  List BulkBoundaryExactSequenceTarget
canonicalBulkBoundaryTargets =
  sixTermExactSequence
  ∷ boundaryMapBulkToEdge
  ∷ exactnessWitnessForCarrierExtension
  ∷ []

data KTheoreticTimeSliceTarget : Set where
  aqftTimeSliceToKEquivalence :
    KTheoreticTimeSliceTarget

  causalPropagationFunctorialKClass :
    KTheoreticTimeSliceTarget

  timeSliceStabilityForCarrierAlgebra :
    KTheoreticTimeSliceTarget

canonicalKTheoreticTimeSliceTargets :
  List KTheoreticTimeSliceTarget
canonicalKTheoreticTimeSliceTargets =
  aqftTimeSliceToKEquivalence
  ∷ causalPropagationFunctorialKClass
  ∷ timeSliceStabilityForCarrierAlgebra
  ∷ []

data BaumConnesReceiptTarget : Set where
  reducedGroupCStarAssemblyTarget :
    BaumConnesReceiptTarget

  gammaElementOrDiracDualDiracTarget :
    BaumConnesReceiptTarget

  coefficientAlgebraForAQFTCarrierTarget :
    BaumConnesReceiptTarget

canonicalBaumConnesReceiptTargets :
  List BaumConnesReceiptTarget
canonicalBaumConnesReceiptTargets =
  reducedGroupCStarAssemblyTarget
  ∷ gammaElementOrDiracDualDiracTarget
  ∷ coefficientAlgebraForAQFTCarrierTarget
  ∷ []

data AlgebraicKTheoryTowerTarget : Set where
  k0GroupCompletionStage :
    AlgebraicKTheoryTowerTarget

  k1LoopGroupStage :
    AlgebraicKTheoryTowerTarget

  higherKTheorySpectrumStage :
    AlgebraicKTheoryTowerTarget

  comparisonToTopologicalKTheoryStage :
    AlgebraicKTheoryTowerTarget

canonicalAlgebraicKTheoryTowerTargets :
  List AlgebraicKTheoryTowerTarget
canonicalAlgebraicKTheoryTowerTargets =
  k0GroupCompletionStage
  ∷ k1LoopGroupStage
  ∷ higherKTheorySpectrumStage
  ∷ comparisonToTopologicalKTheoryStage
  ∷ []

data AnomalyCancellationClassTarget : Set where
  gaugeAnomalyKClass :
    AnomalyCancellationClassTarget

  mixedGaugeGravityAnomalyKClass :
    AnomalyCancellationClassTarget

  globalAnomalyEtaInvariantTarget :
    AnomalyCancellationClassTarget

  standardModelAnomalyCancellationTarget :
    AnomalyCancellationClassTarget

canonicalAnomalyCancellationClassTargets :
  List AnomalyCancellationClassTarget
canonicalAnomalyCancellationClassTargets =
  gaugeAnomalyKClass
  ∷ mixedGaugeGravityAnomalyKClass
  ∷ globalAnomalyEtaInvariantTarget
  ∷ standardModelAnomalyCancellationTarget
  ∷ []

data StandardModelCompactGroupStatus : Set where
  compactGroupTargetOnly :
    StandardModelCompactGroupStatus

  su3su2u1QuotientGlobalFormUnselected :
    StandardModelCompactGroupStatus

  hyperchargeEmbeddingUnproved :
    StandardModelCompactGroupStatus

record NovikovAssemblyMapReceiptSurface : Setω where
  field
    status :
      KTheoryNovikovSurfaceStatus

    assemblyTargets :
      List AssemblyMapTarget

    assemblyTargetsAreCanonical :
      assemblyTargets
      ≡
      canonicalAssemblyMapTargets

    carrierSource :
      String

    assemblyMapShape :
      String

    rationalInjectivityClaimed :
      Bool

    rationalInjectivityClaimedIsFalse :
      rationalInjectivityClaimed ≡ false

    assemblyMapConstructed :
      Bool

    assemblyMapConstructedIsFalse :
      assemblyMapConstructed ≡ false

    noPromotionWithoutAuthority :
      KTheoryNovikovPromotionAuthorityToken →
      ⊥

    boundary :
      List String

open NovikovAssemblyMapReceiptSurface public

canonicalNovikovAssemblyMapReceiptSurface :
  NovikovAssemblyMapReceiptSurface
canonicalNovikovAssemblyMapReceiptSurface =
  record
    { status =
        targetSurfaceOnlyNoPromotion
    ; assemblyTargets =
        canonicalAssemblyMapTargets
    ; assemblyTargetsAreCanonical =
        refl
    ; carrierSource =
        "DASHI B0/AQFT carrier target after formal-D-space and local-algebra receipts"
    ; assemblyMapShape =
        "K-homology or geometric-cycle data -> operator K-theory of the DASHI/AQFT carrier algebra"
    ; rationalInjectivityClaimed =
        false
    ; rationalInjectivityClaimedIsFalse =
        refl
    ; assemblyMapConstructed =
        false
    ; assemblyMapConstructedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "Novikov/assembly map is recorded as a target shape only"
        ∷ "no Baum-Connes or Novikov injectivity theorem is proved or imported here"
        ∷ "no assembly map for a concrete DASHI carrier C*-algebra is constructed here"
        ∷ "no GRQFT, Standard Model, charge classification, or TOE claim is promoted"
        ∷ []
    }

record KTheoryChargeClassificationReceiptSurface : Setω where
  field
    status :
      KTheoryNovikovSurfaceStatus

    chargeTargets :
      List ChargeClassificationTarget

    chargeTargetsAreCanonical :
      chargeTargets
      ≡
      canonicalChargeClassificationTargets

    classificationShape :
      String

    dhrDependency :
      String

    kTheoryChargeClassified :
      Bool

    kTheoryChargeClassifiedIsFalse :
      kTheoryChargeClassified ≡ false

    noPromotionWithoutAuthority :
      KTheoryNovikovPromotionAuthorityToken →
      ⊥

    boundary :
      List String

open KTheoryChargeClassificationReceiptSurface public

canonicalKTheoryChargeClassificationReceiptSurface :
  KTheoryChargeClassificationReceiptSurface
canonicalKTheoryChargeClassificationReceiptSurface =
  record
    { status =
        targetSurfaceOnlyNoPromotion
    ; chargeTargets =
        canonicalChargeClassificationTargets
    ; chargeTargetsAreCanonical =
        refl
    ; classificationShape =
        "physical superselection/charge sectors -> K0/K1 or twisted K-theory class after AQFT and DHR adapters"
    ; dhrDependency =
        "DHR superselection sectors must be constructed for the AQFT net before charge-to-K-class promotion"
    ; kTheoryChargeClassified =
        false
    ; kTheoryChargeClassifiedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "K-theory charge classification is a future target, not a current classification theorem"
        ∷ "DHR sectors, representation category, statistics, and vacuum/GNS adapters remain open"
        ∷ "twists, background fields, and normalization conventions are not selected here"
        ∷ "no Standard Model charge table or physical calibration receipt is constructed"
        ∷ []
    }

record SixTermBulkBoundaryReceiptSurface : Setω where
  field
    status :
      KTheoryNovikovSurfaceStatus

    exactSequenceTargets :
      List BulkBoundaryExactSequenceTarget

    exactSequenceTargetsAreCanonical :
      exactSequenceTargets
      ≡
      canonicalBulkBoundaryTargets

    extensionShape :
      String

    boundaryMapShape :
      String

    exactSequenceProved :
      Bool

    exactSequenceProvedIsFalse :
      exactSequenceProved ≡ false

    bulkBoundaryReceiptPromoted :
      Bool

    bulkBoundaryReceiptPromotedIsFalse :
      bulkBoundaryReceiptPromoted ≡ false

    noPromotionWithoutAuthority :
      KTheoryNovikovPromotionAuthorityToken →
      ⊥

    boundary :
      List String

open SixTermBulkBoundaryReceiptSurface public

canonicalSixTermBulkBoundaryReceiptSurface :
  SixTermBulkBoundaryReceiptSurface
canonicalSixTermBulkBoundaryReceiptSurface =
  record
    { status =
        targetSurfaceOnlyNoPromotion
    ; exactSequenceTargets =
        canonicalBulkBoundaryTargets
    ; exactSequenceTargetsAreCanonical =
        refl
    ; extensionShape =
        "0 -> boundary/edge ideal -> bulk-plus-boundary algebra -> bulk quotient -> 0"
    ; boundaryMapShape =
        "six-term connecting map from bulk K-class to boundary anomaly/edge receipt"
    ; exactSequenceProved =
        false
    ; exactSequenceProvedIsFalse =
        refl
    ; bulkBoundaryReceiptPromoted =
        false
    ; bulkBoundaryReceiptPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "six-term exact sequence is a bulk-boundary theorem target only"
        ∷ "no C*-extension, exactness proof, connecting map, or anomaly inflow theorem is constructed"
        ∷ "bulk-boundary language does not promote charge classification or AQFT completion"
        ∷ []
    }

record KTheoryBCStandardModelTargetReceiptSurface : Setω where
  field
    status :
      KTheoryNovikovSurfaceStatus

    timeSliceTargets :
      List KTheoreticTimeSliceTarget

    timeSliceTargetsAreCanonical :
      timeSliceTargets
      ≡
      canonicalKTheoreticTimeSliceTargets

    baumConnesTargets :
      List BaumConnesReceiptTarget

    baumConnesTargetsAreCanonical :
      baumConnesTargets
      ≡
      canonicalBaumConnesReceiptTargets

    algebraicKTheoryTowerTargets :
      List AlgebraicKTheoryTowerTarget

    algebraicKTheoryTowerTargetsAreCanonical :
      algebraicKTheoryTowerTargets
      ≡
      canonicalAlgebraicKTheoryTowerTargets

    anomalyCancellationClassTargets :
      List AnomalyCancellationClassTarget

    anomalyCancellationClassTargetsAreCanonical :
      anomalyCancellationClassTargets
      ≡
      canonicalAnomalyCancellationClassTargets

    standardModelCompactGroupStatus :
      StandardModelCompactGroupStatus

    timeSliceTheoremProved :
      Bool

    timeSliceTheoremProvedIsFalse :
      timeSliceTheoremProved ≡ false

    baumConnesReceiptPromoted :
      Bool

    baumConnesReceiptPromotedIsFalse :
      baumConnesReceiptPromoted ≡ false

    algebraicKTheoryTowerConstructed :
      Bool

    algebraicKTheoryTowerConstructedIsFalse :
      algebraicKTheoryTowerConstructed ≡ false

    anomalyCancellationProved :
      Bool

    anomalyCancellationProvedIsFalse :
      anomalyCancellationProved ≡ false

    standardModelCompactGroupConstructed :
      Bool

    standardModelCompactGroupConstructedIsFalse :
      standardModelCompactGroupConstructed ≡ false

    standardModelGlobalFormBoundary :
      String

    noPromotionWithoutAuthority :
      KTheoryNovikovPromotionAuthorityToken →
      ⊥

    boundary :
      List String

open KTheoryBCStandardModelTargetReceiptSurface public

canonicalKTheoryBCStandardModelTargetReceiptSurface :
  KTheoryBCStandardModelTargetReceiptSurface
canonicalKTheoryBCStandardModelTargetReceiptSurface =
  record
    { status =
        targetSurfaceOnlyNoPromotion
    ; timeSliceTargets =
        canonicalKTheoreticTimeSliceTargets
    ; timeSliceTargetsAreCanonical =
        refl
    ; baumConnesTargets =
        canonicalBaumConnesReceiptTargets
    ; baumConnesTargetsAreCanonical =
        refl
    ; algebraicKTheoryTowerTargets =
        canonicalAlgebraicKTheoryTowerTargets
    ; algebraicKTheoryTowerTargetsAreCanonical =
        refl
    ; anomalyCancellationClassTargets =
        canonicalAnomalyCancellationClassTargets
    ; anomalyCancellationClassTargetsAreCanonical =
        refl
    ; standardModelCompactGroupStatus =
        su3su2u1QuotientGlobalFormUnselected
    ; timeSliceTheoremProved =
        false
    ; timeSliceTheoremProvedIsFalse =
        refl
    ; baumConnesReceiptPromoted =
        false
    ; baumConnesReceiptPromotedIsFalse =
        refl
    ; algebraicKTheoryTowerConstructed =
        false
    ; algebraicKTheoryTowerConstructedIsFalse =
        refl
    ; anomalyCancellationProved =
        false
    ; anomalyCancellationProvedIsFalse =
        refl
    ; standardModelCompactGroupConstructed =
        false
    ; standardModelCompactGroupConstructedIsFalse =
        refl
    ; standardModelGlobalFormBoundary =
        "SM compact group is a target status only: SU(3)xSU(2)xU(1) quotient/global form and hypercharge embedding are not selected or proved here"
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "K-theoretic time-slice is a theorem target connecting AQFT time-slice data to stable K-classes"
        ∷ "Baum-Connes data is recorded as a receipt target only; no assembly isomorphism or gamma-element proof is supplied"
        ∷ "algebraic K-theory tower stages are placeholders for K0, K1, higher K-theory, and comparison maps"
        ∷ "anomaly-cancellation classes are target classes; no Standard Model anomaly cancellation theorem is proved"
        ∷ "Standard Model compact group status remains target-only with quotient/global form and hypercharge embedding unresolved"
        ∷ "no K-theoretic time-slice theorem, Baum-Connes theorem, anomaly cancellation, Standard Model, GRQFT, or TOE claim is promoted"
        ∷ []
    }

data GRQFTDependencyNode : Set where
  b0FormalGeometry :
    GRQFTDependencyNode

  aqftLocalAlgebra :
    GRQFTDependencyNode

  dhrSuperselection :
    GRQFTDependencyNode

  kTheoryChargeClassification :
    GRQFTDependencyNode

  novikovAssemblyMap :
    GRQFTDependencyNode

  sixTermBulkBoundary :
    GRQFTDependencyNode

  massGapSpectralTarget :
    GRQFTDependencyNode

  lambdaVacuumCalibrationTarget :
    GRQFTDependencyNode

canonicalGRQFTDependencyNodes :
  List GRQFTDependencyNode
canonicalGRQFTDependencyNodes =
  b0FormalGeometry
  ∷ aqftLocalAlgebra
  ∷ dhrSuperselection
  ∷ kTheoryChargeClassification
  ∷ novikovAssemblyMap
  ∷ sixTermBulkBoundary
  ∷ massGapSpectralTarget
  ∷ lambdaVacuumCalibrationTarget
  ∷ []

record GRQFTDependencyEdge : Set where
  field
    source :
      GRQFTDependencyNode

    target :
      GRQFTDependencyNode

    label :
      String

open GRQFTDependencyEdge public

canonicalGRQFTDependencyEdges :
  List GRQFTDependencyEdge
canonicalGRQFTDependencyEdges =
  record
    { source = b0FormalGeometry
    ; target = aqftLocalAlgebra
    ; label = "geometry supplies regions/locality/metric adapter targets"
    }
  ∷ record
      { source = aqftLocalAlgebra
      ; target = dhrSuperselection
      ; label = "DHR sectors require a concrete AQFT net and representation/vacuum adapters"
      }
  ∷ record
      { source = dhrSuperselection
      ; target = kTheoryChargeClassification
      ; label = "charge classes require sector category to K-class adapter"
      }
  ∷ record
      { source = aqftLocalAlgebra
      ; target = novikovAssemblyMap
      ; label = "assembly target requires a concrete operator-algebraic carrier"
      }
  ∷ record
      { source = kTheoryChargeClassification
      ; target = sixTermBulkBoundary
      ; label = "bulk-boundary sequence consumes classified K-classes"
      }
  ∷ record
      { source = aqftLocalAlgebra
      ; target = massGapSpectralTarget
      ; label = "mass gap is a spectral property of the completed Yang-Mills/AQFT object"
      }
  ∷ record
      { source = b0FormalGeometry
      ; target = lambdaVacuumCalibrationTarget
      ; label = "Lambda depends on geometry plus vacuum/renormalisation calibration"
      }
  ∷ record
      { source = aqftLocalAlgebra
      ; target = lambdaVacuumCalibrationTarget
      ; label = "vacuum energy side of Lambda requires AQFT vacuum/renormalisation adapter"
      }
  ∷ []

record KTheoryNovikovDependencyGraphReceipt : Setω where
  field
    status :
      KTheoryNovikovSurfaceStatus

    novikovSurface :
      NovikovAssemblyMapReceiptSurface

    chargeSurface :
      KTheoryChargeClassificationReceiptSurface

    bulkBoundarySurface :
      SixTermBulkBoundaryReceiptSurface

    nodes :
      List GRQFTDependencyNode

    nodesAreCanonical :
      nodes
      ≡
      canonicalGRQFTDependencyNodes

    edges :
      List GRQFTDependencyEdge

    edgesAreCanonical :
      edges
      ≡
      canonicalGRQFTDependencyEdges

    terminalPromotionAvailable :
      Bool

    terminalPromotionAvailableIsFalse :
      terminalPromotionAvailable ≡ false

    noPromotionWithoutAuthority :
      KTheoryNovikovPromotionAuthorityToken →
      ⊥

    graphBoundary :
      List String

open KTheoryNovikovDependencyGraphReceipt public

canonicalKTheoryNovikovDependencyGraphReceipt :
  KTheoryNovikovDependencyGraphReceipt
canonicalKTheoryNovikovDependencyGraphReceipt =
  record
    { status =
        targetSurfaceOnlyNoPromotion
    ; novikovSurface =
        canonicalNovikovAssemblyMapReceiptSurface
    ; chargeSurface =
        canonicalKTheoryChargeClassificationReceiptSurface
    ; bulkBoundarySurface =
        canonicalSixTermBulkBoundaryReceiptSurface
    ; nodes =
        canonicalGRQFTDependencyNodes
    ; nodesAreCanonical =
        refl
    ; edges =
        canonicalGRQFTDependencyEdges
    ; edgesAreCanonical =
        refl
    ; terminalPromotionAvailable =
        false
    ; terminalPromotionAvailableIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; graphBoundary =
        "dependency graph ties B0, AQFT, DHR, K-theory, mass-gap, and Lambda targets"
        ∷ "all graph edges are staging dependencies, not proofs of reducibility or promotion"
        ∷ "mass gap and Lambda remain terminal output obligations, not inputs solved by K-theory"
        ∷ "no terminal GRQFT, Standard Model, or TOE receipt is constructed"
        ∷ []
    }

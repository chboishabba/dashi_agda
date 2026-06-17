module DASHI.Physics.Closure.GRChristoffelRicciKernelObligationCore where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; []; _++_)

open import DASHI.Core.Q using (oneℚ; zeroℚ)

import DASHI.Physics.Closure.ContinuumLimitTheorem as Continuum
import DASHI.Physics.Closure.GRCoord4TensorCore as Coord4
import DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature as Ricci
import DASHI.Physics.Closure.GROrderedRationalFiniteSlotBoundCore as OrderedRational
import DASHI.Physics.Closure.GRPerturbationBoundShapeCore as Perturbation

-- Canonical local carriers and law rows used to tie the obligation chain together.

canonicalSchwarzschildDiagonalMetric : Coord4.SchwarzschildDiagonalMetricSurface
canonicalSchwarzschildDiagonalMetric =
  Coord4.schwarzschildDiagonalMetricSurface
    (Coord4.scalarRadiusKey oneℚ oneℚ)
    oneℚ
    oneℚ
    oneℚ
    (Coord4.schwarzschildMetricTT oneℚ)
    (Coord4.schwarzschildMetricRR oneℚ)
    (Coord4.schwarzschildMetricThetaTheta oneℚ)
    (Coord4.schwarzschildMetricPhiPhi oneℚ)
    []

canonicalSchwarzschildInverseMetric : Coord4.SchwarzschildInverseDiagonalMetricSurface
canonicalSchwarzschildInverseMetric =
  Coord4.schwarzschildInverseDiagonalMetricSurface
    (Coord4.scalarRadiusKey oneℚ oneℚ)
    oneℚ
    oneℚ
    oneℚ
    (Coord4.schwarzschildInverseMetricTT oneℚ)
    (Coord4.schwarzschildInverseMetricRR oneℚ)
    (Coord4.schwarzschildInverseMetricThetaTheta oneℚ)
    (Coord4.schwarzschildInverseMetricPhiPhi oneℚ)
    []

canonicalSchwarzschildPartialG : Coord4.SchwarzschildPartialGFormulaSurface
canonicalSchwarzschildPartialG =
  Coord4.schwarzschildPartialGFormulaSurface
    zeroℚ zeroℚ zeroℚ zeroℚ
    zeroℚ zeroℚ zeroℚ zeroℚ
    zeroℚ zeroℚ zeroℚ zeroℚ
    zeroℚ zeroℚ zeroℚ zeroℚ
    []

canonicalSchwarzschildChristoffelFormula : Coord4.SchwarzschildChristoffelFormulaSurface
canonicalSchwarzschildChristoffelFormula =
  Coord4.schwarzschildChristoffelFormulaSurface
    (Coord4.schwarzschildGammaTtrFormula zeroℚ)
    (Coord4.schwarzschildGammaRttFormula zeroℚ)
    (Coord4.schwarzschildGammaRrrFormula zeroℚ)
    (Coord4.schwarzschildGammaRThetaThetaFormula zeroℚ)
    (Coord4.schwarzschildGammaRPhiPhiFormula zeroℚ)
    (Coord4.schwarzschildGammaThetaRThetaFormula zeroℚ)
    (Coord4.schwarzschildGammaPhiRPhiFormula zeroℚ)
    []

canonicalSchwarzschildDiagonalFormulaCarrier :
  Coord4.SchwarzschildDiagonalFormulaCarrierSurface
canonicalSchwarzschildDiagonalFormulaCarrier =
  Coord4.schwarzschildDiagonalFormulaCarrierSurface
    canonicalSchwarzschildDiagonalMetric
    canonicalSchwarzschildInverseMetric
    canonicalSchwarzschildPartialG
    canonicalSchwarzschildChristoffelFormula
    []

canonicalSchwarzschildFormulaLaw : Coord4.SchwarzschildFormulaLawSurface
canonicalSchwarzschildFormulaLaw =
  Coord4.schwarzschildFormulaLawSurfaceFromCarrier canonicalSchwarzschildDiagonalFormulaCarrier

canonicalRicciShellALaw :
  Ricci.GRDiscreteRicciShellAConstantLawShape
canonicalRicciShellALaw =
  Ricci.grDiscreteRicciShellA2144Over27≤80Law

canonicalPerturbationShape : Perturbation.GRPerturbationBoundShapeCore
canonicalPerturbationShape =
  Perturbation.canonicalGRPerturbationBoundShapeCore

canonicalSchwarzschildFormulaLawCarrierSurface :
  Coord4.SchwarzschildDiagonalFormulaLawCarrierSurface
canonicalSchwarzschildFormulaLawCarrierSurface =
  Coord4.schwarzschildDiagonalFormulaLawCarrierSurfaceFromCarrier
    canonicalSchwarzschildDiagonalFormulaCarrier

canonicalSchwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier :
  Coord4.SchwarzschildChristoffelFormulaLawProjectionSurface
canonicalSchwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier =
  Coord4.schwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier
    canonicalSchwarzschildDiagonalFormulaCarrier

canonicalSchwarzschildInverseMetricLawProjectionSurfaceFromCarrier :
  Coord4.SchwarzschildInverseMetricLawProjectionSurface
canonicalSchwarzschildInverseMetricLawProjectionSurfaceFromCarrier =
  Coord4.schwarzschildInverseMetricLawProjectionSurfaceFromCarrier
    canonicalSchwarzschildDiagonalFormulaCarrier

-- Typed projections/dependencies consumed by this kernel obligation.
canonicalChristoffelFormulaLawDependencySurface :
  Coord4.SchwarzschildFormulaLawSurface
canonicalChristoffelFormulaLawDependencySurface =
  canonicalSchwarzschildFormulaLaw

canonicalChristoffelFormulaLawProjectionSurface :
  Coord4.SchwarzschildChristoffelFormulaLawSurface
canonicalChristoffelFormulaLawProjectionSurface =
  Coord4.SchwarzschildFormulaLawSurface.christoffelFormulaLaw
    canonicalSchwarzschildFormulaLaw

canonicalInverseMetricLawDependencySurface :
  Coord4.SchwarzschildFormulaLawSurface
canonicalInverseMetricLawDependencySurface =
  canonicalSchwarzschildFormulaLaw

canonicalInverseMetricLawProjectionSurface :
  Coord4.SchwarzschildInverseMetricLawSurface
canonicalInverseMetricLawProjectionSurface =
  Coord4.SchwarzschildFormulaLawSurface.inverseMetricLaw
    canonicalSchwarzschildFormulaLaw

canonicalMetricCompatibilityLawDependencySurface :
  Coord4.SchwarzschildFormulaLawSurface
canonicalMetricCompatibilityLawDependencySurface =
  canonicalSchwarzschildFormulaLaw

canonicalMetricCompatibilityLawProjectionSurface :
  Coord4.SchwarzschildMetricCompatibilityLawSurface
canonicalMetricCompatibilityLawProjectionSurface =
  Coord4.SchwarzschildFormulaLawSurface.metricCompatibilityLaw
    canonicalSchwarzschildFormulaLaw

canonicalChristoffelPerturbBoundDependencySurface :
  Perturbation.GRPerturbationBoundShapeCore
canonicalChristoffelPerturbBoundDependencySurface =
  canonicalPerturbationShape

canonicalChristoffelPerturbBoundDependencySurfaceName :
  String
canonicalChristoffelPerturbBoundDependencySurfaceName =
  "GRPerturbationBoundShapeCore.canonicalGRPerturbationBoundShapeCore"

canonicalChristoffelPerturbBoundProjectionSurface :
  Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt
canonicalChristoffelPerturbBoundProjectionSurface =
  Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationRoute
    canonicalPerturbationShape

canonicalRicciBoundDependencySurface :
  Ricci.GRDiscreteRicciShellAConstantLawShape
canonicalRicciBoundDependencySurface =
  Perturbation.GRPerturbationBoundShapeCore.ricciShellA2144Over27Le80Le640Law
    canonicalPerturbationShape

canonicalRicciBoundProjectionSurface :
  Nat
canonicalRicciBoundProjectionSurface =
  Perturbation.GRPerturbationBoundShapeCore.ricciPerturbationBound
    canonicalPerturbationShape

canonicalSymbolicKernelConstructorHandoffDependencySurface :
  Coord4.SchwarzschildFormulaLawSurface
canonicalSymbolicKernelConstructorHandoffDependencySurface =
  canonicalSchwarzschildFormulaLaw

canonicalSymbolicKernelConstructorHandoffProjectionSurface :
  String
canonicalSymbolicKernelConstructorHandoffProjectionSurface =
  "ContinuumLimitTheorem.symbolicRationalFiniteCarrierChristoffelC0FromDerivativeLawFromKernel"

canonicalPerturbationAdapterRouteProjectionRows :
  OrderedRational.GROrderedRationalFiniteSlotBoundCoreAdapterRouteProjectionRows
canonicalPerturbationAdapterRouteProjectionRows =
  OrderedRational.canonicalGROrderedRationalFiniteSlotBoundCoreAdapterRouteProjectionRows

canonicalPerturbationAdapterBlockedRows :
  List OrderedRational.GROrderedRationalFiniteSlotBoundCoreBlockedRow
canonicalPerturbationAdapterBlockedRows =
  OrderedRational.canonicalGROrderedRationalFiniteSlotBoundCoreBlockedRows

canonicalOrderedRationalProofsPromotedIsFalse :
  Bool
canonicalOrderedRationalProofsPromotedIsFalse =
  OrderedRational.fullOrderedRationalProofsPromoted

canonicalChristoffelC0InverseMetricClosenessHypothesis :
  String
canonicalChristoffelC0InverseMetricClosenessHypothesis =
  Perturbation.GRPerturbationBoundShapeCore.christoffelC0InverseMetricClosenessHypothesis
    canonicalPerturbationShape

canonicalRicciSecondPartialC0DistHypothesis :
  String
canonicalRicciSecondPartialC0DistHypothesis =
  Perturbation.GRPerturbationBoundShapeCore.ricciSecondPartialC0DistHypothesis
    canonicalPerturbationShape

canonicalChristoffelC0InverseMetricClosenessHypothesisIsCanonical :
  String
canonicalChristoffelC0InverseMetricClosenessHypothesisIsCanonical =
  Perturbation.GRPerturbationBoundShapeCore.christoffelC0InverseMetricClosenessHypothesis
    canonicalPerturbationShape

canonicalPerturbationStaticHypothesis : String
canonicalPerturbationStaticHypothesis = "h_static"

canonicalPerturbationDiagHypothesis : String
canonicalPerturbationDiagHypothesis = "h_diag"

canonicalPerturbationPGIHypothesis : String
canonicalPerturbationPGIHypothesis = "h_pgi"

canonicalChristoffelPerSlot11Over2Route : String
canonicalChristoffelPerSlot11Over2Route =
  OrderedRational.orderedRationalChristoffel16p5Le22Le48LawName

canonicalRicci252Le640LooseRoute : String
canonicalRicci252Le640LooseRoute =
  OrderedRational.orderedRationalRicci252Le640LooseLawName

canonicalChristoffelC0InverseMetricClosenessPromotedIsFalse :
  Bool
canonicalChristoffelC0InverseMetricClosenessPromotedIsFalse =
  Perturbation.GRPerturbationBoundShapeCore.christoffelC0InverseMetricClosenessPromoted
    canonicalPerturbationShape

canonicalRicciSecondPartialC0DistPromotedIsFalse :
  Bool
canonicalRicciSecondPartialC0DistPromotedIsFalse =
  Perturbation.GRPerturbationBoundShapeCore.ricciSecondPartialC0DistPromoted
    canonicalPerturbationShape

-- Required symbolic token rows for the next-stage constructor handoff.
obligationMathTokenRows : List String
obligationMathTokenRows =
  "22<=48"
  ∷ "2144/27<=80<=640"
  ∷ OrderedRational.orderedRationalChristoffel16p5Le22Le48LawName
  ∷ OrderedRational.orderedRationalRicci252Le640LooseLawName
  ∷ "Shell A tight L=44"
  ∷ "Shell A accepted L=48"
  ∷ []

canonicalChristoffelFormulaLawDependencyRows : List String
canonicalChristoffelFormulaLawDependencyRows =
  "dependency: Coord4.schwarzschildDiagonalFormulaCarrierSurfaceFromCarrier"
  ∷ "dependency: canonicalSchwarzschildFormulaLawCarrierSurface.formulaCarrier = canonicalSchwarzschildDiagonalFormulaCarrier"
  ∷ "dependency: canonicalSchwarzschildFormulaLawCarrierSurface.formulaCarrierNotPromoted = false"
  ∷ "dependency: Coord4.SchwarzschildFormulaLawSurface.christoffelFormulaLaw canonicalSchwarzschildFormulaLaw"
  ∷ []

canonicalChristoffelFormulaLawProjectionRows : List String
canonicalChristoffelFormulaLawProjectionRows =
  "projection: canonicalSchwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier.christoffelFormula"
  ∷ "projection: canonicalSchwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier.nonzeroProjectionCount = 7"
  ∷ "projection: canonicalSchwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier.projectionNotPromoted = false"
  ∷ []

canonicalInverseMetricLawDependencyRows : List String
canonicalInverseMetricLawDependencyRows =
  "dependency: Coord4.schwarzschildDiagonalFormulaCarrierSurfaceFromCarrier"
  ∷ "dependency: canonicalSchwarzschildFormulaLawCarrierSurface.inverseMetricLawRows"
  ∷ "dependency: canonicalSchwarzschildFormulaLawCarrierSurface.formulaCarrierNotPromoted = false"
  ∷ "dependency: Coord4.SchwarzschildFormulaLawSurface.inverseMetricLaw canonicalSchwarzschildFormulaLaw"
  ∷ []

canonicalInverseMetricLawProjectionRows : List String
canonicalInverseMetricLawProjectionRows =
  "projection: canonicalSchwarzschildInverseMetricLawProjectionSurfaceFromCarrier.projectionNotPromoted = false"
  ∷ "projection: canonicalSchwarzschildInverseMetricLawProjectionSurfaceFromCarrier.projectionRows"
  ∷ "projection: canonicalSchwarzschildInverseMetricLawProjectionSurfaceFromCarrier.projectionCount = 4"
  ∷ []

canonicalMetricCompatibilityLawDependencyRows : List String
canonicalMetricCompatibilityLawDependencyRows =
  "dependency: Coord4.schwarzschildDiagonalFormulaCarrierSurfaceFromCarrier"
  ∷ "dependency: canonicalSchwarzschildFormulaLawCarrierSurface.metricCompatibilityRows"
  ∷ "dependency: canonicalSchwarzschildFormulaLawCarrierSurface.formulaCarrierNotPromoted = false"
  ∷ "dependency: Coord4.SchwarzschildFormulaLawSurface.metricCompatibilityLaw canonicalSchwarzschildFormulaLaw"
  ∷ []

canonicalMetricCompatibilityLawProjectionRows : List String
canonicalMetricCompatibilityLawProjectionRows =
  "projection: Coord4.SchwarzschildFormulaLawSurface.metricCompatibilityLaw canonicalSchwarzschildFormulaLaw"
  ∷ "projection: canonicalSchwarzschildFormulaLawCarrierSurface.formulaCarrierNotPromoted = false"
  ∷ []

canonicalChristoffelPerturbBoundDependencyRows : List String
canonicalChristoffelPerturbBoundDependencyRows =
  "dependency: Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationRoute canonicalPerturbationShape"
  ∷ "dependency: Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationTermCountIs2 canonicalPerturbationShape"
  ∷ "dependency: Perturbation.GRPerturbationBoundShapeCore.christoffelFiniteSlotFactorIs4 canonicalPerturbationShape"
  ∷ "dependency: Perturbation.GRPerturbationBoundShapeCore.christoffelFullOrderedQQEstimatePromotedIsFalse canonicalPerturbationShape"
  ∷ "dependency: Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationSplitExposedIsTrue canonicalPerturbationShape"
  ∷ "dependency: canonicalPerturbationAdapterRouteProjectionRows"
  ∷ []

canonicalChristoffelPerturbBoundProjectionRows : List String
canonicalChristoffelPerturbBoundProjectionRows =
  "projection: Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbBoundName canonicalPerturbationShape"
  ∷ "projection: Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationRoute canonicalPerturbationShape"
  ∷ "projection: OrderedRationalShellAChristoffelPerturbationRouteReceipt.perturbationTermCount = 2"
  ∷ "projection: OrderedRationalShellAChristoffelPerturbationRouteReceipt.finiteSumSlotFactor = 4"
  ∷ "projection: OrderedRationalShellAChristoffelPerturbationRouteReceipt.fullOrderedQQEstimatePromoted = false"
  ∷ []

canonicalRicciBoundDependencyRows : List String
canonicalRicciBoundDependencyRows =
  "dependency: Perturbation.GRPerturbationBoundShapeCore.ricciPerturbationBound canonicalPerturbationShape"
  ∷ "dependency: Perturbation.GRPerturbationBoundShapeCore.ricciConvergencePromotedIsFalse canonicalPerturbationShape"
  ∷ "dependency: Perturbation.GRPerturbationBoundShapeCore.ricciExternalSchwarzschildAuthorityClaimedIsFalse canonicalPerturbationShape"
  ∷ "dependency: Perturbation.GRPerturbationBoundShapeCore.ricciShellA2144Over27Le80Le640Law canonicalPerturbationShape"
  ∷ "dependency: canonicalRicciBoundDependencySurface = Perturbation.GRPerturbationBoundShapeCore.ricciShellA2144Over27Le80Le640Law canonicalPerturbationShape"
  ∷ []

canonicalRicciBoundProjectionRows : List String
canonicalRicciBoundProjectionRows =
  "projection: canonicalRicciBoundProjectionSurface = 640"
  ∷ "projection: Perturbation.GRPerturbationBoundShapeCore.ricciPerturbationBound canonicalPerturbationShape = 640"
  ∷ "projection: Perturbation.GRPerturbationBoundShapeCore.ricciShellA2144Over27Le80Le640Law canonicalPerturbationShape"
  ∷ []

canonicalSymbolicKernelConstructorHandoffDependencyRows : List String
canonicalSymbolicKernelConstructorHandoffDependencyRows =
  "dependency: canonicalSchwarzschildFormulaLawCarrierSurface"
  ∷ "dependency: canonicalSchwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier"
  ∷ "dependency: canonicalSchwarzschildInverseMetricLawProjectionSurfaceFromCarrier"
  ∷ "dependency: Perturbation.GRPerturbationBoundShapeCore.christoffelC0InverseMetricClosenessHypothesis canonicalPerturbationShape"
  ∷ "dependency: Perturbation.GRPerturbationBoundShapeCore.ricciSecondPartialC0DistHypothesis canonicalPerturbationShape"
  ∷ "dependency: h_gi"
  ∷ "dependency: h_p2g"
  ∷ "dependency: canonicalPerturbationStaticHypothesis"
  ∷ "dependency: canonicalPerturbationDiagHypothesis"
  ∷ "dependency: canonicalPerturbationPGIHypothesis"
  ∷ "dependency: canonicalChristoffelPerSlot11Over2Route"
  ∷ "dependency: canonicalRicci252Le640LooseRoute"
  ∷ "dependency: canonicalPerturbationAdapterRouteProjectionRows"
  ∷ "dependency: canonicalPerturbationAdapterBlockedRows"
  ∷ "dependency: obligationMathTokenRows"
  ∷ []

canonicalSymbolicKernelConstructorHandoffProjectionRows : List String
canonicalSymbolicKernelConstructorHandoffProjectionRows =
  "projection: canonicalSymbolicKernelConstructorHandoffProjectionSurface"
  ∷ "projection: canonicalPerturbationAdapterBlockedRows"
  ∷ "projection: Perturbation.GRPerturbationBoundShapeCore.christoffelC0InverseMetricClosenessPromotedIsFalse canonicalPerturbationShape"
  ∷ "projection: Perturbation.GRPerturbationBoundShapeCore.ricciSecondPartialC0DistPromotedIsFalse canonicalPerturbationShape"
  ∷ "projection: canonicalChristoffelPerSlot11Over2Route"
  ∷ "projection: canonicalRicci252Le640LooseRoute"
  ∷ "projection: canonicalChristoffelC0InverseMetricClosenessHypothesis = h_gi"
  ∷ "projection: canonicalRicciSecondPartialC0DistHypothesis = h_p2g"
  ∷ "projection: canonicalPerturbationStaticHypothesis = h_static"
  ∷ "projection: canonicalPerturbationDiagHypothesis = h_diag"
  ∷ "projection: canonicalPerturbationPGIHypothesis = h_pgi"
  ∷ "projection: canonicalOrderedRationalProofsPromotedIsFalse = false"
  ∷ []

record GRChristoffelRicciKernelObligationCoreORCSLPGF : Set where
  constructor grChristoffelRicciKernelObligationCoreORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ "GR-Christoffel-Ricci-kernel obligations"
    R : String
    RIsCanonical : R ≡ "record the concrete proof-grammar dependency/projection chain"
    C : String
    CIsCanonical : C ≡ "diagonal Coord4/Schwarzschild law → explicit row ledger → ordered rational → perturbation → Ricci"
    S : String
    SIsCanonical : S ≡ "fail-closed"
    L : String
    LIsCanonical : L ≡ "obligation token rows and blockers"
    P : String
    PIsCanonical : P ≡ "all promotions are blocked"
    G : String
    GIsCanonical : G ≡ "geometric surface+symbolic-kernel constructor shape"
    F : String
    FIsCanonical : F ≡
      "keeps concrete 22<=48 / 2144/27<=80<=640 rows and explicit dependency/projection rows; no Ricci-convergence, Schwarzschild-Birkhoff, or Clay promotion"

open GRChristoffelRicciKernelObligationCoreORCSLPGF public

canonicalGRChristoffelRicciKernelObligationCoreORCSLPGF :
  GRChristoffelRicciKernelObligationCoreORCSLPGF
canonicalGRChristoffelRicciKernelObligationCoreORCSLPGF =
    grChristoffelRicciKernelObligationCoreORCSLPGF
    "GR-Christoffel-Ricci-kernel obligations"
    refl
    "record the concrete proof-grammar dependency/projection chain"
    refl
    "diagonal Coord4/Schwarzschild law → explicit row ledger → ordered rational → perturbation → Ricci"
    refl
    "fail-closed"
    refl
    "obligation token rows and blockers"
    refl
    "all promotions are blocked"
    refl
    "geometric surface+symbolic-kernel constructor shape"
    refl
    "keeps concrete 22<=48 / 2144/27<=80<=640 rows and explicit dependency/projection rows; no Ricci-convergence, Schwarzschild-Birkhoff, or Clay promotion"
    refl

record GRChristoffelRicciKernelObligationCore : Setω where
  field
    coord4Carrier :
      Set

    coord4CarrierIsCanonical :
      coord4Carrier ≡ Coord4.Coord4

    diagonalSchwarzschildFormulaCarrier :
      Coord4.SchwarzschildDiagonalFormulaCarrierSurface

    diagonalSchwarzschildFormulaCarrierIsCanonical :
      diagonalSchwarzschildFormulaCarrier ≡ canonicalSchwarzschildDiagonalFormulaCarrier

    diagonalFormulaLawCarrierSurface :
      Coord4.SchwarzschildDiagonalFormulaLawCarrierSurface

    diagonalFormulaLawCarrierSurfaceIsCanonical :
      diagonalFormulaLawCarrierSurface ≡ canonicalSchwarzschildFormulaLawCarrierSurface

    christoffelFormulaLaw :
      Coord4.SchwarzschildChristoffelFormulaLawSurface

    christoffelFormulaLawIsCanonical :
      christoffelFormulaLaw ≡
        Coord4.SchwarzschildFormulaLawSurface.christoffelFormulaLaw
          canonicalSchwarzschildFormulaLaw

    inverseMetricLaw :
      Coord4.SchwarzschildInverseMetricLawSurface

    inverseMetricLawIsCanonical :
      inverseMetricLaw ≡
        Coord4.SchwarzschildFormulaLawSurface.inverseMetricLaw
          canonicalSchwarzschildFormulaLaw

    inverseMetricLawDependencySurface :
      Coord4.SchwarzschildFormulaLawSurface

    inverseMetricLawDependencySurfaceIsCanonical :
      inverseMetricLawDependencySurface ≡
        canonicalInverseMetricLawDependencySurface

    inverseMetricLawProjectionSurface :
      Coord4.SchwarzschildInverseMetricLawSurface

    inverseMetricLawProjectionSurfaceIsCanonical :
      inverseMetricLawProjectionSurface ≡
        canonicalInverseMetricLawProjectionSurface

    metricCompatibilityLaw :
      Coord4.SchwarzschildMetricCompatibilityLawSurface

    metricCompatibilityLawIsCanonical :
      metricCompatibilityLaw ≡
        Coord4.SchwarzschildFormulaLawSurface.metricCompatibilityLaw
          canonicalSchwarzschildFormulaLaw

    metricCompatibilityLawDependencySurface :
      Coord4.SchwarzschildFormulaLawSurface

    metricCompatibilityLawDependencySurfaceIsCanonical :
      metricCompatibilityLawDependencySurface ≡
        canonicalMetricCompatibilityLawDependencySurface

    metricCompatibilityLawProjectionSurface :
      Coord4.SchwarzschildMetricCompatibilityLawSurface

    metricCompatibilityLawProjectionSurfaceIsCanonical :
      metricCompatibilityLawProjectionSurface ≡
        canonicalMetricCompatibilityLawProjectionSurface

    diagonalSchwarzschildFormulaLaw :
      Coord4.SchwarzschildFormulaLawSurface

    diagonalSchwarzschildFormulaLawIsCanonical :
      diagonalSchwarzschildFormulaLaw ≡ canonicalSchwarzschildFormulaLaw

    christoffelFormulaLawDependencySurface :
      Coord4.SchwarzschildFormulaLawSurface

    christoffelFormulaLawDependencySurfaceIsCanonical :
      christoffelFormulaLawDependencySurface ≡
        canonicalChristoffelFormulaLawDependencySurface

    christoffelFormulaLawProjectionSurface :
      Coord4.SchwarzschildChristoffelFormulaLawSurface

    christoffelFormulaLawProjectionSurfaceIsCanonical :
      christoffelFormulaLawProjectionSurface ≡
        canonicalChristoffelFormulaLawProjectionSurface

    christoffelFormulaLawProjectionSurfaceFromCarrier :
      Coord4.SchwarzschildChristoffelFormulaLawProjectionSurface

    christoffelFormulaLawProjectionSurfaceFromCarrierIsCanonical :
      christoffelFormulaLawProjectionSurfaceFromCarrier ≡
        canonicalSchwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier

    inverseMetricLawProjectionSurfaceFromCarrier :
      Coord4.SchwarzschildInverseMetricLawProjectionSurface

    inverseMetricLawProjectionSurfaceFromCarrierIsCanonical :
      inverseMetricLawProjectionSurfaceFromCarrier ≡
        canonicalSchwarzschildInverseMetricLawProjectionSurfaceFromCarrier

    christoffelFormulaLawDependencyRows :
      List String

    christoffelFormulaLawDependencyRowsAreCanonical :
      christoffelFormulaLawDependencyRows ≡ canonicalChristoffelFormulaLawDependencyRows

    christoffelFormulaLawProjectionRows :
      List String

    christoffelFormulaLawProjectionRowsAreCanonical :
      christoffelFormulaLawProjectionRows ≡ canonicalChristoffelFormulaLawProjectionRows

    inverseMetricLawDependencyRows :
      List String

    inverseMetricLawDependencyRowsAreCanonical :
      inverseMetricLawDependencyRows ≡ canonicalInverseMetricLawDependencyRows

    inverseMetricLawProjectionRows :
      List String

    inverseMetricLawProjectionRowsAreCanonical :
      inverseMetricLawProjectionRows ≡ canonicalInverseMetricLawProjectionRows

    metricCompatibilityLawDependencyRows :
      List String

    metricCompatibilityLawDependencyRowsAreCanonical :
      metricCompatibilityLawDependencyRows ≡ canonicalMetricCompatibilityLawDependencyRows

    metricCompatibilityLawProjectionRows :
      List String

    metricCompatibilityLawProjectionRowsAreCanonical :
      metricCompatibilityLawProjectionRows ≡ canonicalMetricCompatibilityLawProjectionRows

    orderedRationalFormulaLemmas :
      List String

    orderedRationalFormulaLemmasAreCanonical :
      orderedRationalFormulaLemmas ≡
        ( OrderedRational.canonicalOrderedRationalScalarLemmaNames
          ++ OrderedRational.orderedRationalChristoffel16p5Le22Le48LawName
          ∷ OrderedRational.orderedRationalRicci252Le640LooseLawName
          ∷ "22<=48" ∷ "2144/27<=80<=640" ∷ [])

    orderedRationalPerturbationRoute :
      Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt

    orderedRationalPerturbationRouteIsCanonical :
      orderedRationalPerturbationRoute ≡
        Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

    orderedRationalPerturbationRouteAdapterProjectionRows :
      OrderedRational.GROrderedRationalFiniteSlotBoundCoreAdapterRouteProjectionRows

    orderedRationalPerturbationRouteAdapterProjectionRowsAreCanonical :
      orderedRationalPerturbationRouteAdapterProjectionRows ≡
        canonicalPerturbationAdapterRouteProjectionRows

    orderedRationalPerturbationBlockedRows :
      List OrderedRational.GROrderedRationalFiniteSlotBoundCoreBlockedRow

    orderedRationalPerturbationBlockedRowsAreCanonical :
      orderedRationalPerturbationBlockedRows ≡
        canonicalPerturbationAdapterBlockedRows

    orderedRationalProofsPromoted :
      Bool

    orderedRationalProofsPromotedIsFalse :
      orderedRationalProofsPromoted ≡ false

    symbolicKernelConstructorHandoffChristoffelC0InverseMetricClosenessHypothesis :
      String

    symbolicKernelConstructorHandoffChristoffelC0InverseMetricClosenessHypothesisIsCanonical :
      symbolicKernelConstructorHandoffChristoffelC0InverseMetricClosenessHypothesis
      ≡
      canonicalChristoffelC0InverseMetricClosenessHypothesis

    symbolicKernelConstructorHandoffRicciSecondPartialC0DistHypothesis :
      String

    symbolicKernelConstructorHandoffRicciSecondPartialC0DistHypothesisIsCanonical :
      symbolicKernelConstructorHandoffRicciSecondPartialC0DistHypothesis
      ≡
      canonicalRicciSecondPartialC0DistHypothesis

    symbolicKernelConstructorHandoffChristoffelC0InverseMetricClosenessPromoted :
      Bool

    symbolicKernelConstructorHandoffChristoffelC0InverseMetricClosenessPromotedIsFalse :
      symbolicKernelConstructorHandoffChristoffelC0InverseMetricClosenessPromoted
      ≡ false

    symbolicKernelConstructorHandoffRicciSecondPartialC0DistPromoted :
      Bool

    symbolicKernelConstructorHandoffRicciSecondPartialC0DistPromotedIsFalse :
      symbolicKernelConstructorHandoffRicciSecondPartialC0DistPromoted
      ≡ false

    symbolicKernelConstructorHandoffStaticHypothesis :
      String

    symbolicKernelConstructorHandoffStaticHypothesisIsCanonical :
      symbolicKernelConstructorHandoffStaticHypothesis
      ≡
      canonicalPerturbationStaticHypothesis

    symbolicKernelConstructorHandoffDiagHypothesis :
      String

    symbolicKernelConstructorHandoffDiagHypothesisIsCanonical :
      symbolicKernelConstructorHandoffDiagHypothesis
      ≡
      canonicalPerturbationDiagHypothesis

    symbolicKernelConstructorHandoffPGIHypothesis :
      String

    symbolicKernelConstructorHandoffPGIHypothesisIsCanonical :
      symbolicKernelConstructorHandoffPGIHypothesis
      ≡
      canonicalPerturbationPGIHypothesis

    symbolicKernelConstructorHandoffGiHypothesis :
      String

    symbolicKernelConstructorHandoffGiHypothesisIsCanonical :
      symbolicKernelConstructorHandoffGiHypothesis
      ≡
      canonicalChristoffelC0InverseMetricClosenessHypothesisIsCanonical

    symbolicKernelConstructorHandoffP2gHypothesis :
      String

    symbolicKernelConstructorHandoffP2gHypothesisIsCanonical :
      symbolicKernelConstructorHandoffP2gHypothesis
      ≡
      canonicalRicciSecondPartialC0DistHypothesis

    symbolicKernelConstructorHandoffPerSlot11Over2Route :
      String

    symbolicKernelConstructorHandoffPerSlot11Over2RouteIsCanonical :
      symbolicKernelConstructorHandoffPerSlot11Over2Route
      ≡
      canonicalChristoffelPerSlot11Over2Route

    symbolicKernelConstructorHandoffRicci252Le640LooseRoute :
      String

    symbolicKernelConstructorHandoffRicci252Le640LooseRouteIsCanonical :
      symbolicKernelConstructorHandoffRicci252Le640LooseRoute
      ≡
      canonicalRicci252Le640LooseRoute

    christoffelTermCount :
      Nat

    christoffelTermCountIs2 :
      christoffelTermCount ≡ 2

    finiteSlotFactor :
      Nat

    finiteSlotFactorIs4 :
      finiteSlotFactor ≡ 4

    sevenNonzeroSlotCount :
      Nat

    sevenNonzeroSlotCountIs7 :
      sevenNonzeroSlotCount ≡ 7

    christoffelPerturbBoundName :
      String

    christoffelPerturbBoundNameIsCanonical :
      christoffelPerturbBoundName
      ≡
      Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbBoundName
        canonicalPerturbationShape

    christoffelPerturbBoundDependencySurfaceName :
      String

    christoffelPerturbBoundDependencySurfaceNameIsCanonical :
      christoffelPerturbBoundDependencySurfaceName ≡
        canonicalChristoffelPerturbBoundDependencySurfaceName

    christoffelPerturbBoundProjectionSurface :
      Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt

    christoffelPerturbBoundProjectionSurfaceIsCanonical :
      christoffelPerturbBoundProjectionSurface ≡
        canonicalChristoffelPerturbBoundProjectionSurface

    christoffelPerturbBoundDependencyRows :
      List String

    christoffelPerturbBoundDependencyRowsAreCanonical :
      christoffelPerturbBoundDependencyRows ≡ canonicalChristoffelPerturbBoundDependencyRows

    christoffelPerturbBoundProjectionRows :
      List String

    christoffelPerturbBoundProjectionRowsAreCanonical :
      christoffelPerturbBoundProjectionRows ≡ canonicalChristoffelPerturbBoundProjectionRows

    ricciBound :
      Nat

    ricciBoundIs640 :
      ricciBound ≡ 640

    ricciBoundDependencySurface :
      Ricci.GRDiscreteRicciShellAConstantLawShape

    ricciBoundDependencySurfaceIsCanonical :
      ricciBoundDependencySurface ≡
        canonicalRicciBoundDependencySurface

    ricciBoundProjectionSurface :
      Nat

    ricciBoundProjectionSurfaceIs640 :
      ricciBoundProjectionSurface ≡
        canonicalRicciBoundProjectionSurface

    ricciBoundDependencyRows :
      List String

    ricciBoundDependencyRowsAreCanonical :
      ricciBoundDependencyRows ≡ canonicalRicciBoundDependencyRows

    ricciBoundProjectionRows :
      List String

    ricciBoundProjectionRowsAreCanonical :
      ricciBoundProjectionRows ≡ canonicalRicciBoundProjectionRows

    ricciShellA2144Over27Le80Le640Law :
      Ricci.GRDiscreteRicciShellAConstantLawShape

    ricciShellA2144Over27Le80Le640LawIsCanonical :
      ricciShellA2144Over27Le80Le640Law ≡ canonicalRicciShellALaw

    symbolicallyRecordedObligationRows :
      List String

    symbolicallyRecordedObligationRowsAreCanonical :
      symbolicallyRecordedObligationRows ≡ obligationMathTokenRows

    noArbitraryContinuumRicciConvergence :
      Bool

    noArbitraryContinuumRicciConvergenceIsFalse :
      noArbitraryContinuumRicciConvergence ≡ false

    noSchwarzschildBirkhoffPromotion :
      Bool

    noSchwarzschildBirkhoffPromotionIsFalse :
      noSchwarzschildBirkhoffPromotion ≡ false

    noClayPromotion :
      Bool

    noClayPromotionIsFalse :
      noClayPromotion ≡ false

    symbolicRationalChristoffelC0StabilityKernelConstructorName :
      String

    symbolicRationalChristoffelC0StabilityKernelConstructorNameIsCanonical :
      symbolicRationalChristoffelC0StabilityKernelConstructorName
      ≡
      "ContinuumLimitTheorem.symbolicRationalFiniteCarrierChristoffelC0FromDerivativeLawFromKernel"

    symbolicKernelConstructorHandoffDependencySurface :
      Coord4.SchwarzschildFormulaLawSurface

    symbolicKernelConstructorHandoffDependencySurfaceIsCanonical :
      symbolicKernelConstructorHandoffDependencySurface
      ≡
      canonicalSymbolicKernelConstructorHandoffDependencySurface

    symbolicKernelConstructorHandoffProjectionSurface :
      String

    symbolicKernelConstructorHandoffProjectionSurfaceIsCanonical :
      symbolicKernelConstructorHandoffProjectionSurface
      ≡
      canonicalSymbolicKernelConstructorHandoffProjectionSurface

    symbolicKernelConstructorHandoffDependencyRows :
      List String

    symbolicKernelConstructorHandoffDependencyRowsAreCanonical :
      symbolicKernelConstructorHandoffDependencyRows
      ≡
      canonicalSymbolicKernelConstructorHandoffDependencyRows

    symbolicKernelConstructorHandoffProjectionRows :
      List String

    symbolicKernelConstructorHandoffProjectionRowsAreCanonical :
      symbolicKernelConstructorHandoffProjectionRows
      ≡
      canonicalSymbolicKernelConstructorHandoffProjectionRows

    orcslpgf :
      GRChristoffelRicciKernelObligationCoreORCSLPGF

    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalGRChristoffelRicciKernelObligationCoreORCSLPGF

open GRChristoffelRicciKernelObligationCore public

canonicalGRChristoffelRicciKernelObligationCore :
  GRChristoffelRicciKernelObligationCore
canonicalGRChristoffelRicciKernelObligationCore =
  record
    { coord4Carrier =
        Coord4.Coord4
    ; coord4CarrierIsCanonical =
        refl
    ; diagonalSchwarzschildFormulaCarrier =
        canonicalSchwarzschildDiagonalFormulaCarrier
    ; diagonalSchwarzschildFormulaCarrierIsCanonical =
        refl
    ; diagonalFormulaLawCarrierSurface =
        canonicalSchwarzschildFormulaLawCarrierSurface
    ; diagonalFormulaLawCarrierSurfaceIsCanonical =
        refl
    ; christoffelFormulaLaw =
        Coord4.SchwarzschildFormulaLawSurface.christoffelFormulaLaw
          canonicalSchwarzschildFormulaLaw
    ; christoffelFormulaLawIsCanonical =
        refl
    ; inverseMetricLaw =
        Coord4.SchwarzschildFormulaLawSurface.inverseMetricLaw
          canonicalSchwarzschildFormulaLaw
    ; inverseMetricLawIsCanonical =
        refl
    ; inverseMetricLawDependencySurface =
        canonicalInverseMetricLawDependencySurface
    ; inverseMetricLawDependencySurfaceIsCanonical =
        refl
    ; inverseMetricLawProjectionSurface =
        canonicalInverseMetricLawProjectionSurface
    ; inverseMetricLawProjectionSurfaceIsCanonical =
        refl
    ; metricCompatibilityLaw =
        Coord4.SchwarzschildFormulaLawSurface.metricCompatibilityLaw
          canonicalSchwarzschildFormulaLaw
    ; metricCompatibilityLawIsCanonical =
        refl
    ; metricCompatibilityLawDependencySurface =
        canonicalMetricCompatibilityLawDependencySurface
    ; metricCompatibilityLawDependencySurfaceIsCanonical =
        refl
    ; metricCompatibilityLawProjectionSurface =
        canonicalMetricCompatibilityLawProjectionSurface
    ; metricCompatibilityLawProjectionSurfaceIsCanonical =
        refl
    ; diagonalSchwarzschildFormulaLaw =
        canonicalSchwarzschildFormulaLaw
    ; diagonalSchwarzschildFormulaLawIsCanonical =
        refl
    ; christoffelFormulaLawDependencySurface =
        canonicalChristoffelFormulaLawDependencySurface
    ; christoffelFormulaLawDependencySurfaceIsCanonical =
        refl
    ; christoffelFormulaLawProjectionSurface =
        canonicalChristoffelFormulaLawProjectionSurface
    ; christoffelFormulaLawProjectionSurfaceIsCanonical =
        refl
    ; christoffelFormulaLawProjectionSurfaceFromCarrier =
        canonicalSchwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier
    ; christoffelFormulaLawProjectionSurfaceFromCarrierIsCanonical =
        refl
    ; inverseMetricLawProjectionSurfaceFromCarrier =
        canonicalSchwarzschildInverseMetricLawProjectionSurfaceFromCarrier
    ; inverseMetricLawProjectionSurfaceFromCarrierIsCanonical =
        refl
    ; christoffelFormulaLawDependencyRows =
        canonicalChristoffelFormulaLawDependencyRows
    ; christoffelFormulaLawDependencyRowsAreCanonical =
        refl
    ; christoffelFormulaLawProjectionRows =
        canonicalChristoffelFormulaLawProjectionRows
    ; christoffelFormulaLawProjectionRowsAreCanonical =
        refl
    ; inverseMetricLawDependencyRows =
        canonicalInverseMetricLawDependencyRows
    ; inverseMetricLawDependencyRowsAreCanonical =
        refl
    ; inverseMetricLawProjectionRows =
        canonicalInverseMetricLawProjectionRows
    ; inverseMetricLawProjectionRowsAreCanonical =
        refl
    ; metricCompatibilityLawDependencyRows =
        canonicalMetricCompatibilityLawDependencyRows
    ; metricCompatibilityLawDependencyRowsAreCanonical =
        refl
    ; metricCompatibilityLawProjectionRows =
        canonicalMetricCompatibilityLawProjectionRows
    ; metricCompatibilityLawProjectionRowsAreCanonical =
        refl
    ; orderedRationalFormulaLemmas =
        OrderedRational.canonicalOrderedRationalScalarLemmaNames
          ++ OrderedRational.orderedRationalChristoffel16p5Le22Le48LawName
          ∷ OrderedRational.orderedRationalRicci252Le640LooseLawName
          ∷ "22<=48" ∷ "2144/27<=80<=640" ∷ []
    ; orderedRationalFormulaLemmasAreCanonical =
        refl
    ; orderedRationalPerturbationRoute =
        Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationRoute
          canonicalPerturbationShape
    ; orderedRationalPerturbationRouteIsCanonical =
        Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationRouteIsCanonical
          canonicalPerturbationShape
    ; orderedRationalPerturbationRouteAdapterProjectionRows =
        canonicalPerturbationAdapterRouteProjectionRows
    ; orderedRationalPerturbationRouteAdapterProjectionRowsAreCanonical =
        refl
    ; orderedRationalPerturbationBlockedRows =
        canonicalPerturbationAdapterBlockedRows
    ; orderedRationalPerturbationBlockedRowsAreCanonical =
        refl
    ; orderedRationalProofsPromoted =
        canonicalOrderedRationalProofsPromotedIsFalse
    ; orderedRationalProofsPromotedIsFalse =
        refl
    ; symbolicKernelConstructorHandoffChristoffelC0InverseMetricClosenessHypothesis =
        canonicalChristoffelC0InverseMetricClosenessHypothesis
    ; symbolicKernelConstructorHandoffChristoffelC0InverseMetricClosenessHypothesisIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffRicciSecondPartialC0DistHypothesis =
        canonicalRicciSecondPartialC0DistHypothesis
    ; symbolicKernelConstructorHandoffRicciSecondPartialC0DistHypothesisIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffChristoffelC0InverseMetricClosenessPromoted =
        canonicalChristoffelC0InverseMetricClosenessPromotedIsFalse
    ; symbolicKernelConstructorHandoffChristoffelC0InverseMetricClosenessPromotedIsFalse =
        refl
    ; symbolicKernelConstructorHandoffRicciSecondPartialC0DistPromoted =
        canonicalRicciSecondPartialC0DistPromotedIsFalse
    ; symbolicKernelConstructorHandoffRicciSecondPartialC0DistPromotedIsFalse =
        refl
    ; symbolicKernelConstructorHandoffStaticHypothesis =
        canonicalPerturbationStaticHypothesis
    ; symbolicKernelConstructorHandoffStaticHypothesisIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffDiagHypothesis =
        canonicalPerturbationDiagHypothesis
    ; symbolicKernelConstructorHandoffDiagHypothesisIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffPGIHypothesis =
        canonicalPerturbationPGIHypothesis
    ; symbolicKernelConstructorHandoffPGIHypothesisIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffGiHypothesis =
        canonicalChristoffelC0InverseMetricClosenessHypothesisIsCanonical
    ; symbolicKernelConstructorHandoffGiHypothesisIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffP2gHypothesis =
        canonicalRicciSecondPartialC0DistHypothesis
    ; symbolicKernelConstructorHandoffP2gHypothesisIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffPerSlot11Over2Route =
        canonicalChristoffelPerSlot11Over2Route
    ; symbolicKernelConstructorHandoffPerSlot11Over2RouteIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffRicci252Le640LooseRoute =
        canonicalRicci252Le640LooseRoute
    ; symbolicKernelConstructorHandoffRicci252Le640LooseRouteIsCanonical =
        refl
    ; christoffelTermCount =
        Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationTermCount
          canonicalPerturbationShape
    ; christoffelTermCountIs2 =
        Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationTermCountIs2
          canonicalPerturbationShape
    ; finiteSlotFactor =
        Perturbation.GRPerturbationBoundShapeCore.christoffelFiniteSlotFactor
          canonicalPerturbationShape
    ; finiteSlotFactorIs4 =
        Perturbation.GRPerturbationBoundShapeCore.christoffelFiniteSlotFactorIs4
          canonicalPerturbationShape
    ; sevenNonzeroSlotCount =
        OrderedRational.sevenNonzeroSlotCount
    ; sevenNonzeroSlotCountIs7 =
        OrderedRational.sevenNonzeroSlotCountIs7
    ; christoffelPerturbBoundName =
        Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbBoundName
          canonicalPerturbationShape
    ; christoffelPerturbBoundNameIsCanonical =
        refl
    ; christoffelPerturbBoundDependencySurfaceName =
        canonicalChristoffelPerturbBoundDependencySurfaceName
    ; christoffelPerturbBoundDependencySurfaceNameIsCanonical =
        refl
    ; christoffelPerturbBoundProjectionSurface =
        canonicalChristoffelPerturbBoundProjectionSurface
    ; christoffelPerturbBoundProjectionSurfaceIsCanonical =
        refl
    ; christoffelPerturbBoundDependencyRows =
        canonicalChristoffelPerturbBoundDependencyRows
    ; christoffelPerturbBoundDependencyRowsAreCanonical =
        refl
    ; christoffelPerturbBoundProjectionRows =
        canonicalChristoffelPerturbBoundProjectionRows
    ; christoffelPerturbBoundProjectionRowsAreCanonical =
        refl
    ; ricciBound =
        Perturbation.GRPerturbationBoundShapeCore.ricciPerturbationBound
          canonicalPerturbationShape
    ; ricciBoundIs640 =
        Perturbation.GRPerturbationBoundShapeCore.ricciPerturbationBoundIs640
          canonicalPerturbationShape
    ; ricciBoundDependencySurface =
        canonicalRicciBoundDependencySurface
    ; ricciBoundDependencySurfaceIsCanonical =
        refl
    ; ricciBoundProjectionSurface =
        canonicalRicciBoundProjectionSurface
    ; ricciBoundProjectionSurfaceIs640 =
        refl
    ; ricciBoundDependencyRows =
        canonicalRicciBoundDependencyRows
    ; ricciBoundDependencyRowsAreCanonical =
        refl
    ; ricciBoundProjectionRows =
        canonicalRicciBoundProjectionRows
    ; ricciBoundProjectionRowsAreCanonical =
        refl
    ; ricciShellA2144Over27Le80Le640Law =
        canonicalRicciShellALaw
    ; ricciShellA2144Over27Le80Le640LawIsCanonical =
        refl
    ; symbolicallyRecordedObligationRows =
        obligationMathTokenRows
    ; symbolicallyRecordedObligationRowsAreCanonical =
        refl
    ; noArbitraryContinuumRicciConvergence =
        Perturbation.GRPerturbationBoundShapeCore.ricciConvergencePromoted
          canonicalPerturbationShape
    ; noArbitraryContinuumRicciConvergenceIsFalse =
        Perturbation.GRPerturbationBoundShapeCore.ricciConvergencePromotedIsFalse
          canonicalPerturbationShape
    ; noSchwarzschildBirkhoffPromotion =
        Perturbation.GRPerturbationBoundShapeCore.ricciExternalSchwarzschildAuthorityClaimed
          canonicalPerturbationShape
    ; noSchwarzschildBirkhoffPromotionIsFalse =
        Perturbation.GRPerturbationBoundShapeCore.ricciExternalSchwarzschildAuthorityClaimedIsFalse
          canonicalPerturbationShape
    ; noClayPromotion =
        false
    ; noClayPromotionIsFalse =
        refl
    ; symbolicRationalChristoffelC0StabilityKernelConstructorName =
        "ContinuumLimitTheorem.symbolicRationalFiniteCarrierChristoffelC0FromDerivativeLawFromKernel"
    ; symbolicRationalChristoffelC0StabilityKernelConstructorNameIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffDependencySurface =
        canonicalSymbolicKernelConstructorHandoffDependencySurface
    ; symbolicKernelConstructorHandoffDependencySurfaceIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffProjectionSurface =
        canonicalSymbolicKernelConstructorHandoffProjectionSurface
    ; symbolicKernelConstructorHandoffProjectionSurfaceIsCanonical =
        refl
    ; symbolicKernelConstructorHandoffDependencyRows =
        canonicalSymbolicKernelConstructorHandoffDependencyRows
    ; symbolicKernelConstructorHandoffDependencyRowsAreCanonical =
        refl
    ; symbolicKernelConstructorHandoffProjectionRows =
        canonicalSymbolicKernelConstructorHandoffProjectionRows
    ; symbolicKernelConstructorHandoffProjectionRowsAreCanonical =
        refl
    ; orcslpgf =
        canonicalGRChristoffelRicciKernelObligationCoreORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    }

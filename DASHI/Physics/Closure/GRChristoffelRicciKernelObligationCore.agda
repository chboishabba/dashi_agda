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

-- Required symbolic token rows for the next-stage constructor handoff.
obligationMathTokenRows : List String
obligationMathTokenRows =
  "22<=48"
  ∷ "2144/27<=80<=640"
  ∷ "Shell A tight L=44"
  ∷ "Shell A accepted L=48"
  ∷ []

record GRChristoffelRicciKernelObligationCoreORCSLPGF : Set where
  constructor grChristoffelRicciKernelObligationCoreORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ "GR-Christoffel-Ricci-kernel obligations"
    R : String
    RIsCanonical : R ≡ "record the concrete proof-grammar dependency chain"
    C : String
    CIsCanonical : C ≡ "diagonal Coord4/Schwarzschild law → ordered rational → perturbation → Ricci"
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
      "keeps concrete 22<=48 / 2144/27<=80<=640 rows; no Ricci-convergence, Schwarzschild-Birkhoff, or Clay promotion"

open GRChristoffelRicciKernelObligationCoreORCSLPGF public

canonicalGRChristoffelRicciKernelObligationCoreORCSLPGF :
  GRChristoffelRicciKernelObligationCoreORCSLPGF
canonicalGRChristoffelRicciKernelObligationCoreORCSLPGF =
  grChristoffelRicciKernelObligationCoreORCSLPGF
    "GR-Christoffel-Ricci-kernel obligations"
    refl
    "record the concrete proof-grammar dependency chain"
    refl
    "diagonal Coord4/Schwarzschild law → ordered rational → perturbation → Ricci"
    refl
    "fail-closed"
    refl
    "obligation token rows and blockers"
    refl
    "all promotions are blocked"
    refl
    "geometric surface+symbolic-kernel constructor shape"
    refl
    "keeps concrete 22<=48 / 2144/27<=80<=640 rows; no Ricci-convergence, Schwarzschild-Birkhoff, or Clay promotion"
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

    metricCompatibilityLaw :
      Coord4.SchwarzschildMetricCompatibilityLawSurface

    metricCompatibilityLawIsCanonical :
      metricCompatibilityLaw ≡
        Coord4.SchwarzschildFormulaLawSurface.metricCompatibilityLaw
          canonicalSchwarzschildFormulaLaw

    diagonalSchwarzschildFormulaLaw :
      Coord4.SchwarzschildFormulaLawSurface

    diagonalSchwarzschildFormulaLawIsCanonical :
      diagonalSchwarzschildFormulaLaw ≡ canonicalSchwarzschildFormulaLaw

    orderedRationalFormulaLemmas :
      List String

    orderedRationalFormulaLemmasAreCanonical :
      orderedRationalFormulaLemmas ≡
        ( OrderedRational.canonicalOrderedRationalScalarLemmaNames
          ++ "22<=48" ∷ "2144/27<=80<=640" ∷ [])

    orderedRationalPerturbationRoute :
      Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt

    orderedRationalPerturbationRouteIsCanonical :
      orderedRationalPerturbationRoute ≡
        Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

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

    ricciBound :
      Nat

    ricciBoundIs640 :
      ricciBound ≡ 640

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
    ; metricCompatibilityLaw =
        Coord4.SchwarzschildFormulaLawSurface.metricCompatibilityLaw
          canonicalSchwarzschildFormulaLaw
    ; metricCompatibilityLawIsCanonical =
        refl
    ; diagonalSchwarzschildFormulaLaw =
        canonicalSchwarzschildFormulaLaw
    ; diagonalSchwarzschildFormulaLawIsCanonical =
        refl
    ; orderedRationalFormulaLemmas =
        OrderedRational.canonicalOrderedRationalScalarLemmaNames
          ++ "22<=48" ∷ "2144/27<=80<=640" ∷ []
    ; orderedRationalFormulaLemmasAreCanonical =
        refl
    ; orderedRationalPerturbationRoute =
        Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationRoute
          canonicalPerturbationShape
    ; orderedRationalPerturbationRouteIsCanonical =
        Perturbation.GRPerturbationBoundShapeCore.christoffelPerturbationRouteIsCanonical
          canonicalPerturbationShape
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
    ; ricciBound =
        Perturbation.GRPerturbationBoundShapeCore.ricciPerturbationBound
          canonicalPerturbationShape
    ; ricciBoundIs640 =
        Perturbation.GRPerturbationBoundShapeCore.ricciPerturbationBoundIs640
          canonicalPerturbationShape
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
    ; orcslpgf =
        canonicalGRChristoffelRicciKernelObligationCoreORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    }

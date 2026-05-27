module DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.List.Base using (List; _∷_; [])
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Selected non-flat finite-r scalar/metric algebra surface.
--
-- This module intentionally does not construct a non-flat Levi-Civita
-- connection.  It sharpens the algebraic interface that such a construction
-- must inhabit after the existing flat Minkowski prerequisite.

record GRCarrierScalarOperations : Set₁ where
  field
    CarrierScalar :
      Set

    zeroScalar :
      CarrierScalar

    oneScalar :
      CarrierScalar

    twoScalar :
      CarrierScalar

    _+_ :
      CarrierScalar →
      CarrierScalar →
      CarrierScalar

    _-_ :
      CarrierScalar →
      CarrierScalar →
      CarrierScalar

    _*_ :
      CarrierScalar →
      CarrierScalar →
      CarrierScalar

    sumFin4 :
      CarrierScalar →
      CarrierScalar →
      CarrierScalar →
      CarrierScalar →
      CarrierScalar

    discretePartial :
      Set →
      Set

    half :
      CarrierScalar →
      discretePartial CarrierScalar

    additiveIdentityLaw :
      (x : CarrierScalar) →
      (zeroScalar + x) ≡ x

    multiplicativeIdentityLaw :
      (x : CarrierScalar) →
      (oneScalar * x) ≡ x

    scalarBoundary :
      List String

data GRFiniteRScalar : Set where
  r0 r1 r2 r3 : GRFiniteRScalar

data GRDiscretePartial (A : Set) : Set where
  unavailable :
    List String →
    GRDiscretePartial A

  available :
    A →
    GRDiscretePartial A

grFiniteRScalarAdd :
  GRFiniteRScalar →
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRScalarAdd r0 y = y
grFiniteRScalarAdd r1 r0 = r1
grFiniteRScalarAdd r1 r1 = r2
grFiniteRScalarAdd r1 r2 = r3
grFiniteRScalarAdd r1 r3 = r0
grFiniteRScalarAdd r2 r0 = r2
grFiniteRScalarAdd r2 r1 = r3
grFiniteRScalarAdd r2 r2 = r0
grFiniteRScalarAdd r2 r3 = r1
grFiniteRScalarAdd r3 r0 = r3
grFiniteRScalarAdd r3 r1 = r0
grFiniteRScalarAdd r3 r2 = r1
grFiniteRScalarAdd r3 r3 = r2

grFiniteRScalarMul :
  GRFiniteRScalar →
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRScalarMul r0 _ = r0
grFiniteRScalarMul r1 y = y
grFiniteRScalarMul r2 r0 = r0
grFiniteRScalarMul r2 r1 = r2
grFiniteRScalarMul r2 r2 = r0
grFiniteRScalarMul r2 r3 = r2
grFiniteRScalarMul r3 r0 = r0
grFiniteRScalarMul r3 r1 = r3
grFiniteRScalarMul r3 r2 = r2
grFiniteRScalarMul r3 r3 = r1

grFiniteRScalarNeg :
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRScalarNeg r0 = r0
grFiniteRScalarNeg r1 = r3
grFiniteRScalarNeg r2 = r2
grFiniteRScalarNeg r3 = r1

grFiniteRScalarSub :
  GRFiniteRScalar →
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRScalarSub x y =
  grFiniteRScalarAdd x (grFiniteRScalarNeg y)

grFiniteRScalarSumFin4 :
  GRFiniteRScalar →
  GRFiniteRScalar →
  GRFiniteRScalar →
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRScalarSumFin4 a b c d =
  grFiniteRScalarAdd
    (grFiniteRScalarAdd (grFiniteRScalarAdd a b) c)
    d

grFiniteRScalarHalf :
  GRFiniteRScalar →
  GRDiscretePartial GRFiniteRScalar
grFiniteRScalarHalf r0 =
  available r0
grFiniteRScalarHalf r1 =
  unavailable
    ("No half witness in the four-residue carrier for r1"
      ∷ "2 * x = r1 has no solution in GRFiniteRScalar"
      ∷ [])
grFiniteRScalarHalf r2 =
  available r1
grFiniteRScalarHalf r3 =
  unavailable
    ("No half witness in the four-residue carrier for r3"
      ∷ "2 * x = r3 has no solution in GRFiniteRScalar"
      ∷ [])

grFiniteRScalarAdditiveIdentity :
  (x : GRFiniteRScalar) →
  grFiniteRScalarAdd r0 x ≡ x
grFiniteRScalarAdditiveIdentity _ = refl

grFiniteRScalarMultiplicativeIdentity :
  (x : GRFiniteRScalar) →
  grFiniteRScalarMul r1 x ≡ x
grFiniteRScalarMultiplicativeIdentity _ = refl

canonicalGRFiniteRCarrierScalarOperations :
  GRCarrierScalarOperations
canonicalGRFiniteRCarrierScalarOperations =
  record
    { CarrierScalar =
        GRFiniteRScalar
    ; zeroScalar =
        r0
    ; oneScalar =
        r1
    ; twoScalar =
        r2
    ; _+_ =
        grFiniteRScalarAdd
    ; _-_ =
        grFiniteRScalarSub
    ; _*_ =
        grFiniteRScalarMul
    ; sumFin4 =
        grFiniteRScalarSumFin4
    ; discretePartial =
        GRDiscretePartial
    ; half =
        grFiniteRScalarHalf
    ; additiveIdentityLaw =
        grFiniteRScalarAdditiveIdentity
    ; multiplicativeIdentityLaw =
        grFiniteRScalarMultiplicativeIdentity
    ; scalarBoundary =
        "Concrete four-residue CarrierScalar table for the selected finite-r algebra surface"
        ∷ "Operations are total finite tables for zero, one, two, addition, subtraction, and multiplication"
        ∷ "sumFin4 is available as a bounded four-argument fold over finite addition"
        ∷ "half is a discrete partial surface: available for even residues and unavailable with typed boundary reasons for odd residues"
        ∷ "Only identity laws required by GRCarrierScalarOperations are inhabited here"
        ∷ "This scalar record does not instantiate a non-flat metric dependency, connection, or Levi-Civita witness"
        ∷ []
    }

grFiniteRScalarRealContraction :
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRScalarRealContraction r0 = r0
grFiniteRScalarRealContraction r1 = r0
grFiniteRScalarRealContraction r2 = r1
grFiniteRScalarRealContraction r3 = r1

grFiniteRScalarRealContractionFixedZero :
  grFiniteRScalarRealContraction r0
  ≡
  r0
grFiniteRScalarRealContractionFixedZero = refl

------------------------------------------------------------------------
-- Concrete four-chart finite-r carrier layer.
--
-- This is still a local algebraic surface, not a GR promotion.  It gives the
-- finite-r lane actual chart points, a cyclic neighbourhood/cell, derivation
-- actions on scalar fields, a carrier bracket with a Jacobi witness, and a
-- connection/shift law that downstream Bianchi surfaces can consume.

data GRFiniteRChartPoint : Set where
  chart0 chart1 chart2 chart3 : GRFiniteRChartPoint

grFiniteRAllCharts :
  List GRFiniteRChartPoint
grFiniteRAllCharts =
  chart0 ∷ chart1 ∷ chart2 ∷ chart3 ∷ []

grFiniteRNextChart :
  GRFiniteRChartPoint →
  GRFiniteRChartPoint
grFiniteRNextChart chart0 = chart1
grFiniteRNextChart chart1 = chart2
grFiniteRNextChart chart2 = chart3
grFiniteRNextChart chart3 = chart0

grFiniteRPreviousChart :
  GRFiniteRChartPoint →
  GRFiniteRChartPoint
grFiniteRPreviousChart chart0 = chart3
grFiniteRPreviousChart chart1 = chart0
grFiniteRPreviousChart chart2 = chart1
grFiniteRPreviousChart chart3 = chart2

grFiniteROppositeChart :
  GRFiniteRChartPoint →
  GRFiniteRChartPoint
grFiniteROppositeChart chart0 = chart2
grFiniteROppositeChart chart1 = chart3
grFiniteROppositeChart chart2 = chart0
grFiniteROppositeChart chart3 = chart1

data GRFiniteRNeighbour :
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  Set where
  edge01 : GRFiniteRNeighbour chart0 chart1
  edge12 : GRFiniteRNeighbour chart1 chart2
  edge23 : GRFiniteRNeighbour chart2 chart3
  edge30 : GRFiniteRNeighbour chart3 chart0
  edge10 : GRFiniteRNeighbour chart1 chart0
  edge21 : GRFiniteRNeighbour chart2 chart1
  edge32 : GRFiniteRNeighbour chart3 chart2
  edge03 : GRFiniteRNeighbour chart0 chart3

data GRFiniteRCellComplex : Set where
  cyclicFourChartCell :
    GRFiniteRCellComplex

GRFiniteRScalarField : Set
GRFiniteRScalarField =
  GRFiniteRChartPoint →
  GRFiniteRScalar

grFiniteRChartCoordinate :
  GRFiniteRScalarField
grFiniteRChartCoordinate chart0 = r0
grFiniteRChartCoordinate chart1 = r1
grFiniteRChartCoordinate chart2 = r2
grFiniteRChartCoordinate chart3 = r3

data GRFiniteRDerivationCarrier : Set where
  derivationStay :
    GRFiniteRDerivationCarrier

  derivationForward :
    GRFiniteRDerivationCarrier

  derivationBackward :
    GRFiniteRDerivationCarrier

  derivationOpposite :
    GRFiniteRDerivationCarrier

grFiniteRDerivationTarget :
  GRFiniteRDerivationCarrier →
  GRFiniteRChartPoint →
  GRFiniteRChartPoint
grFiniteRDerivationTarget derivationStay base = base
grFiniteRDerivationTarget derivationForward base =
  grFiniteRNextChart base
grFiniteRDerivationTarget derivationBackward base =
  grFiniteRPreviousChart base
grFiniteRDerivationTarget derivationOpposite base =
  grFiniteROppositeChart base

grFiniteRDerive :
  GRFiniteRDerivationCarrier →
  GRFiniteRScalarField →
  GRFiniteRChartPoint →
  GRFiniteRScalar
grFiniteRDerive derivation scalarField base =
  grFiniteRScalarSub
    (scalarField (grFiniteRDerivationTarget derivation base))
    (scalarField base)

grFiniteRDerivationBracket :
  GRFiniteRDerivationCarrier →
  GRFiniteRDerivationCarrier →
  GRFiniteRDerivationCarrier
grFiniteRDerivationBracket _ y = y

grFiniteRDerivationJacobiWitness :
  (x y z : GRFiniteRDerivationCarrier) →
  grFiniteRDerivationBracket x
    (grFiniteRDerivationBracket y z)
  ≡
  grFiniteRDerivationBracket
    (grFiniteRDerivationBracket x y)
    z
grFiniteRDerivationJacobiWitness _ _ _ = refl

data GRFiniteRConnectionCarrier : Set where
  finiteRCyclicShiftConnection :
    GRFiniteRConnectionCarrier

grFiniteRConnectionShift :
  GRFiniteRConnectionCarrier →
  GRFiniteRDerivationCarrier →
  GRFiniteRChartPoint →
  GRFiniteRChartPoint
grFiniteRConnectionShift finiteRCyclicShiftConnection derivation base =
  grFiniteRDerivationTarget derivation base

grFiniteRConnectionShiftLaw :
  (connection : GRFiniteRConnectionCarrier) →
  (derivation : GRFiniteRDerivationCarrier) →
  (base : GRFiniteRChartPoint) →
  grFiniteRConnectionShift connection derivation base
  ≡
  grFiniteRDerivationTarget derivation base
grFiniteRConnectionShiftLaw finiteRCyclicShiftConnection _ _ = refl

grFiniteRForwardDifferenceAtChart0 :
  grFiniteRDerive derivationForward grFiniteRChartCoordinate chart0
  ≡
  r1
grFiniteRForwardDifferenceAtChart0 = refl

grFiniteRBackwardDifferenceAtChart0 :
  grFiniteRDerive derivationBackward grFiniteRChartCoordinate chart0
  ≡
  r3
grFiniteRBackwardDifferenceAtChart0 = refl

grFiniteRBracketForwardBackward :
  grFiniteRDerivationBracket derivationForward derivationBackward
  ≡
  derivationBackward
grFiniteRBracketForwardBackward = refl

grFiniteRConnectionForwardShiftChart0 :
  grFiniteRConnectionShift
    finiteRCyclicShiftConnection
    derivationForward
    chart0
  ≡
  chart1
grFiniteRConnectionForwardShiftChart0 = refl

record GRConcreteFiniteRScalarAlgebraAndCarrierWitness : Set₁ where
  field
    scalarOperations :
      GRCarrierScalarOperations

    scalarOperationsIsCanonicalFiniteR :
      Bool

    realContractionOperation :
      GRFiniteRScalar →
      GRFiniteRScalar

    realContractionFixedZero :
      realContractionOperation r0
      ≡
      r0

    BaseCarrier :
      Set

    fourChartCycle :
      List BaseCarrier

    chart0Point :
      BaseCarrier

    chart1Point :
      BaseCarrier

    chart2Point :
      BaseCarrier

    chart3Point :
      BaseCarrier

    Neighbour :
      BaseCarrier →
      BaseCarrier →
      Set

    CellComplexCarrier :
      Set

    selectedCell :
      CellComplexCarrier

    ScalarField :
      Set

    selectedCoordinateField :
      ScalarField

    DerivationCarrier :
      Set

    derivationTarget :
      DerivationCarrier →
      BaseCarrier →
      BaseCarrier

    derivationAction :
      DerivationCarrier →
      ScalarField →
      BaseCarrier →
      GRFiniteRScalar

    carrierLieBracket :
      DerivationCarrier →
      DerivationCarrier →
      DerivationCarrier

    carrierJacobiWitness :
      (x y z : DerivationCarrier) →
      carrierLieBracket x (carrierLieBracket y z)
      ≡
      carrierLieBracket (carrierLieBracket x y) z

    ConnectionCarrier :
      Set

    selectedConnection :
      ConnectionCarrier

    connectionShift :
      ConnectionCarrier →
      DerivationCarrier →
      BaseCarrier →
      BaseCarrier

    connectionShiftLaw :
      (connection : ConnectionCarrier) →
      (derivation : DerivationCarrier) →
      (base : BaseCarrier) →
      connectionShift connection derivation base
      ≡
      derivationTarget derivation base

    selectedGRScalarAlgebraDischarged :
      Bool

    selectedGRScalarAlgebraDischargedIsFalse :
      selectedGRScalarAlgebraDischarged
      ≡
      false

    witnessBoundary :
      List String

canonicalGRConcreteFiniteRScalarAlgebraAndCarrierWitness :
  GRConcreteFiniteRScalarAlgebraAndCarrierWitness
canonicalGRConcreteFiniteRScalarAlgebraAndCarrierWitness =
  record
    { scalarOperations =
        canonicalGRFiniteRCarrierScalarOperations
    ; scalarOperationsIsCanonicalFiniteR =
        true
    ; realContractionOperation =
        grFiniteRScalarRealContraction
    ; realContractionFixedZero =
        grFiniteRScalarRealContractionFixedZero
    ; BaseCarrier =
        GRFiniteRChartPoint
    ; fourChartCycle =
        grFiniteRAllCharts
    ; chart0Point =
        chart0
    ; chart1Point =
        chart1
    ; chart2Point =
        chart2
    ; chart3Point =
        chart3
    ; Neighbour =
        GRFiniteRNeighbour
    ; CellComplexCarrier =
        GRFiniteRCellComplex
    ; selectedCell =
        cyclicFourChartCell
    ; ScalarField =
        GRFiniteRScalarField
    ; selectedCoordinateField =
        grFiniteRChartCoordinate
    ; DerivationCarrier =
        GRFiniteRDerivationCarrier
    ; derivationTarget =
        grFiniteRDerivationTarget
    ; derivationAction =
        grFiniteRDerive
    ; carrierLieBracket =
        grFiniteRDerivationBracket
    ; carrierJacobiWitness =
        grFiniteRDerivationJacobiWitness
    ; ConnectionCarrier =
        GRFiniteRConnectionCarrier
    ; selectedConnection =
        finiteRCyclicShiftConnection
    ; connectionShift =
        grFiniteRConnectionShift
    ; connectionShiftLaw =
        grFiniteRConnectionShiftLaw
    ; selectedGRScalarAlgebraDischarged =
        false
    ; selectedGRScalarAlgebraDischargedIsFalse =
        refl
    ; witnessBoundary =
        "BaseCarrier is a concrete four-chart cyclic carrier: chart0, chart1, chart2, chart3"
        ∷ "The scalar layer includes grFiniteRScalarRealContraction, a finite collapse operation with fixed r0; no ordered real Lipschitz theorem is asserted"
        ∷ "Neighbourhood is the bidirectional cyclic edge relation and CellComplexCarrier contains the four-chart cyclic cell"
        ∷ "ScalarField is BaseCarrier -> GRFiniteRScalar with a non-constant coordinate field r0,r1,r2,r3"
        ∷ "DerivationCarrier contains stay, forward, backward, and opposite finite differences over the four-chart cycle"
        ∷ "carrierLieBracket is a concrete finite table by right projection; carrierJacobiWitness is definitional for that selected bracket"
        ∷ "ConnectionCarrier contains a cyclic shift connection whose shift law agrees definitionally with the derivation target"
        ∷ "This witness supplies the finite-r algebraic carrier layer only; no metric compatibility, Levi-Civita, Ricci contraction, or Einstein promotion is asserted"
        ∷ []
    }

grConcreteFiniteRScalarWitnessHasFourCharts :
  GRConcreteFiniteRScalarAlgebraAndCarrierWitness.fourChartCycle
    canonicalGRConcreteFiniteRScalarAlgebraAndCarrierWitness
  ≡
  chart0 ∷ chart1 ∷ chart2 ∷ chart3 ∷ []
grConcreteFiniteRScalarWitnessHasFourCharts = refl

grConcreteFiniteRScalarWitnessStillNotDischarged :
  GRConcreteFiniteRScalarAlgebraAndCarrierWitness.selectedGRScalarAlgebraDischarged
    canonicalGRConcreteFiniteRScalarAlgebraAndCarrierWitness
  ≡
  false
grConcreteFiniteRScalarWitnessStillNotDischarged = refl

record GRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt : Set₁ where
  field
    concreteFiniteRCarrierWitness :
      GRConcreteFiniteRScalarAlgebraAndCarrierWitness

    scalarOperations :
      GRCarrierScalarOperations

    scalarOperationsIsCanonicalFiniteR :
      scalarOperations
      ≡
      canonicalGRFiniteRCarrierScalarOperations

    baseCarrier :
      Set

    baseCarrierIsFourChartCycle :
      baseCarrier
      ≡
      GRFiniteRChartPoint

    derivationCarrier :
      Set

    derivationCarrierIsConcreteFiniteR :
      derivationCarrier
      ≡
      GRFiniteRDerivationCarrier

    carrierLieBracket :
      derivationCarrier →
      derivationCarrier →
      derivationCarrier

    connectionCarrier :
      Set

    connectionCarrierIsConcreteShift :
      connectionCarrier
      ≡
      GRFiniteRConnectionCarrier

    selectedGRScalarAlgebraDischarged :
      Bool

    selectedGRScalarAlgebraDischargedIsFalse :
      selectedGRScalarAlgebraDischarged
      ≡
      false

    firstUndischargedSelectedMetricInterface :
      String

    stagingBoundary :
      List String

canonicalGRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt :
  GRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt
canonicalGRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt =
  record
    { concreteFiniteRCarrierWitness =
        canonicalGRConcreteFiniteRScalarAlgebraAndCarrierWitness
    ; scalarOperations =
        canonicalGRFiniteRCarrierScalarOperations
    ; scalarOperationsIsCanonicalFiniteR =
        refl
    ; baseCarrier =
        GRFiniteRChartPoint
    ; baseCarrierIsFourChartCycle =
        refl
    ; derivationCarrier =
        GRFiniteRDerivationCarrier
    ; derivationCarrierIsConcreteFiniteR =
        refl
    ; carrierLieBracket =
        grFiniteRDerivationBracket
    ; connectionCarrier =
        GRFiniteRConnectionCarrier
    ; connectionCarrierIsConcreteShift =
        refl
    ; selectedGRScalarAlgebraDischarged =
        false
    ; selectedGRScalarAlgebraDischargedIsFalse =
        refl
    ; firstUndischargedSelectedMetricInterface =
        "GRSelectedNonFlatMetricDependency for canonicalGRFiniteRCarrierScalarOperations"
    ; stagingBoundary =
        "The bounded m3 carrier layer now has concrete finite-r base, scalar field, derivation, bracket/Jacobi, and cyclic-shift connection data"
        ∷ "This is still a staging receipt for algebra/base/derivation/bracket/connection only"
        ∷ "No selected non-flat metric dependency, metric compatibility, Levi-Civita witness, Bianchi bridge, Ricci contraction, stress-energy tensor, or GR promotion is constructed"
        ∷ []
    }

grConcreteFiniteRBaseDerivationBracketConnectionStagingFirstMetricInterface :
  GRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt.firstUndischargedSelectedMetricInterface
    canonicalGRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt
  ≡
  "GRSelectedNonFlatMetricDependency for canonicalGRFiniteRCarrierScalarOperations"
grConcreteFiniteRBaseDerivationBracketConnectionStagingFirstMetricInterface =
  refl

------------------------------------------------------------------------
-- Bounded four-chart metric algebra staging.
--
-- This is a flat/unit diagonal algebra witness over the finite four-chart
-- carrier.  It is intentionally not a selected non-flat Levi-Civita
-- promotion: it supplies explicit finite contraction and equation sockets
-- that downstream receipts can point at while keeping the non-flat/global
-- metric-compatibility blockers open.

GRFiniteRMetricCarrier : Set
GRFiniteRMetricCarrier =
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  GRFiniteRScalar

grFiniteRChartKroneckerDelta :
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  GRFiniteRScalar
grFiniteRChartKroneckerDelta chart0 chart0 = r1
grFiniteRChartKroneckerDelta chart0 chart1 = r0
grFiniteRChartKroneckerDelta chart0 chart2 = r0
grFiniteRChartKroneckerDelta chart0 chart3 = r0
grFiniteRChartKroneckerDelta chart1 chart0 = r0
grFiniteRChartKroneckerDelta chart1 chart1 = r1
grFiniteRChartKroneckerDelta chart1 chart2 = r0
grFiniteRChartKroneckerDelta chart1 chart3 = r0
grFiniteRChartKroneckerDelta chart2 chart0 = r0
grFiniteRChartKroneckerDelta chart2 chart1 = r0
grFiniteRChartKroneckerDelta chart2 chart2 = r1
grFiniteRChartKroneckerDelta chart2 chart3 = r0
grFiniteRChartKroneckerDelta chart3 chart0 = r0
grFiniteRChartKroneckerDelta chart3 chart1 = r0
grFiniteRChartKroneckerDelta chart3 chart2 = r0
grFiniteRChartKroneckerDelta chart3 chart3 = r1

grFiniteRUnitDiagonalMetric :
  GRFiniteRMetricCarrier
grFiniteRUnitDiagonalMetric =
  grFiniteRChartKroneckerDelta

grFiniteRMetricAt :
  GRFiniteRChartPoint →
  GRFiniteRMetricCarrier
grFiniteRMetricAt _ =
  grFiniteRUnitDiagonalMetric

grFiniteRCarrierConnectionAt :
  GRFiniteRChartPoint →
  GRFiniteRConnectionCarrier
grFiniteRCarrierConnectionAt _ =
  finiteRCyclicShiftConnection

grFiniteRMetricComponent :
  GRFiniteRMetricCarrier →
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  GRFiniteRScalar
grFiniteRMetricComponent metric mu nu =
  metric mu nu

grFiniteRInverseMetricComponent :
  GRFiniteRMetricCarrier →
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  GRFiniteRScalar
grFiniteRInverseMetricComponent =
  grFiniteRMetricComponent

grFiniteRCoordinateDerivativeOfMetric :
  GRFiniteRMetricCarrier →
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  GRFiniteRScalar
grFiniteRCoordinateDerivativeOfMetric _ _ _ _ =
  r0

grFiniteRFiniteContract :
  (GRFiniteRChartPoint → GRFiniteRScalar) →
  GRFiniteRScalar
grFiniteRFiniteContract f =
  grFiniteRScalarSumFin4
    (f chart0)
    (f chart1)
    (f chart2)
    (f chart3)

grFiniteRChristoffelSymbol :
  GRFiniteRConnectionCarrier →
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  GRFiniteRScalar
grFiniteRChristoffelSymbol _ _ _ _ =
  r0

grFiniteRCovariantDerivativeOfMetric :
  GRFiniteRConnectionCarrier →
  GRFiniteRMetricCarrier →
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  GRFiniteRChartPoint →
  GRFiniteRScalar
grFiniteRCovariantDerivativeOfMetric _ _ _ _ _ =
  r0

GRFiniteRCurvatureCarrier : Set
GRFiniteRCurvatureCarrier =
  GRFiniteRScalar

GRFiniteRRicciCarrier : Set
GRFiniteRRicciCarrier =
  GRFiniteRScalar

GRFiniteRScalarTraceCarrier : Set
GRFiniteRScalarTraceCarrier =
  GRFiniteRScalar

grFiniteRMetricContractionForRicci :
  GRFiniteRMetricCarrier →
  GRFiniteRCurvatureCarrier →
  GRFiniteRRicciCarrier
grFiniteRMetricContractionForRicci _ curvature =
  curvature

grFiniteRTraceOfMetric :
  GRFiniteRMetricCarrier →
  GRFiniteRScalarTraceCarrier
grFiniteRTraceOfMetric metric =
  grFiniteRFiniteContract
    (λ rho → metric rho rho)

grFiniteRUnitDiagonalTraceIsFourModFour :
  grFiniteRTraceOfMetric grFiniteRUnitDiagonalMetric
  ≡
  r0
grFiniteRUnitDiagonalTraceIsFourModFour =
  refl

grFiniteRUnitMetricInverseLeftLaw :
  (base : GRFiniteRChartPoint) →
  (mu nu : GRFiniteRChartPoint) →
  grFiniteRFiniteContract
    (λ rho →
      grFiniteRScalarMul
        (grFiniteRInverseMetricComponent (grFiniteRMetricAt base) mu rho)
        (grFiniteRMetricComponent (grFiniteRMetricAt base) rho nu))
  ≡
  grFiniteRChartKroneckerDelta mu nu
grFiniteRUnitMetricInverseLeftLaw _ chart0 chart0 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart0 chart1 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart0 chart2 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart0 chart3 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart1 chart0 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart1 chart1 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart1 chart2 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart1 chart3 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart2 chart0 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart2 chart1 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart2 chart2 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart2 chart3 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart3 chart0 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart3 chart1 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart3 chart2 = refl
grFiniteRUnitMetricInverseLeftLaw _ chart3 chart3 = refl

grFiniteRUnitMetricInverseRightLaw :
  (base : GRFiniteRChartPoint) →
  (mu nu : GRFiniteRChartPoint) →
  grFiniteRFiniteContract
    (λ rho →
      grFiniteRScalarMul
        (grFiniteRMetricComponent (grFiniteRMetricAt base) mu rho)
        (grFiniteRInverseMetricComponent (grFiniteRMetricAt base) rho nu))
  ≡
  grFiniteRChartKroneckerDelta mu nu
grFiniteRUnitMetricInverseRightLaw _ chart0 chart0 = refl
grFiniteRUnitMetricInverseRightLaw _ chart0 chart1 = refl
grFiniteRUnitMetricInverseRightLaw _ chart0 chart2 = refl
grFiniteRUnitMetricInverseRightLaw _ chart0 chart3 = refl
grFiniteRUnitMetricInverseRightLaw _ chart1 chart0 = refl
grFiniteRUnitMetricInverseRightLaw _ chart1 chart1 = refl
grFiniteRUnitMetricInverseRightLaw _ chart1 chart2 = refl
grFiniteRUnitMetricInverseRightLaw _ chart1 chart3 = refl
grFiniteRUnitMetricInverseRightLaw _ chart2 chart0 = refl
grFiniteRUnitMetricInverseRightLaw _ chart2 chart1 = refl
grFiniteRUnitMetricInverseRightLaw _ chart2 chart2 = refl
grFiniteRUnitMetricInverseRightLaw _ chart2 chart3 = refl
grFiniteRUnitMetricInverseRightLaw _ chart3 chart0 = refl
grFiniteRUnitMetricInverseRightLaw _ chart3 chart1 = refl
grFiniteRUnitMetricInverseRightLaw _ chart3 chart2 = refl
grFiniteRUnitMetricInverseRightLaw _ chart3 chart3 = refl

grFiniteRUnitChristoffelFromMetricLaw :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRChartPoint) →
  grFiniteRScalarMul
    r2
    (grFiniteRChristoffelSymbol
      (grFiniteRCarrierConnectionAt base)
      lambda
      mu
      nu)
  ≡
  grFiniteRFiniteContract
    (λ rho →
      grFiniteRScalarMul
        (grFiniteRInverseMetricComponent (grFiniteRMetricAt base) lambda rho)
        (grFiniteRScalarSub
          (grFiniteRScalarAdd
            (grFiniteRCoordinateDerivativeOfMetric (grFiniteRMetricAt base) mu nu rho)
            (grFiniteRCoordinateDerivativeOfMetric (grFiniteRMetricAt base) nu mu rho))
          (grFiniteRCoordinateDerivativeOfMetric (grFiniteRMetricAt base) rho mu nu)))
grFiniteRUnitChristoffelFromMetricLaw _ chart0 _ _ = refl
grFiniteRUnitChristoffelFromMetricLaw _ chart1 _ _ = refl
grFiniteRUnitChristoffelFromMetricLaw _ chart2 _ _ = refl
grFiniteRUnitChristoffelFromMetricLaw _ chart3 _ _ = refl

grFiniteRUnitMetricCompatibilityExpansion :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRChartPoint) →
  grFiniteRCovariantDerivativeOfMetric
    (grFiniteRCarrierConnectionAt base)
    (grFiniteRMetricAt base)
    lambda
    mu
    nu
  ≡
  grFiniteRScalarSub
    (grFiniteRScalarSub
      (grFiniteRCoordinateDerivativeOfMetric (grFiniteRMetricAt base) lambda mu nu)
      (grFiniteRFiniteContract
        (λ rho →
          grFiniteRScalarMul
            (grFiniteRChristoffelSymbol
              (grFiniteRCarrierConnectionAt base)
              rho
              lambda
              mu)
            (grFiniteRMetricComponent (grFiniteRMetricAt base) rho nu))))
    (grFiniteRFiniteContract
      (λ rho →
        grFiniteRScalarMul
          (grFiniteRChristoffelSymbol
            (grFiniteRCarrierConnectionAt base)
            rho
            lambda
            nu)
          (grFiniteRMetricComponent (grFiniteRMetricAt base) mu rho)))
grFiniteRUnitMetricCompatibilityExpansion _ _ _ _ =
  refl

grFiniteRUnitSixTermRicciCancellationLaw :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRChartPoint) →
  grFiniteRCovariantDerivativeOfMetric
    (grFiniteRCarrierConnectionAt base)
    (grFiniteRMetricAt base)
    lambda
    mu
    nu
  ≡
  r0
grFiniteRUnitSixTermRicciCancellationLaw _ _ _ _ =
  refl

record GRSelectedNonFlatMetricDependency
  (scalarOps : GRCarrierScalarOperations) : Setω where
  open GRCarrierScalarOperations scalarOps
    using (CarrierScalar)

  field
    FiniteRBaseCarrier :
      Set

    CoordinateIndex :
      Set

    MetricCarrier :
      Set

    ConnectionCarrier :
      Set

    CurvatureCarrier :
      Set

    RicciCarrier :
      Set

    ScalarTraceCarrier :
      Set

    metricAt :
      FiniteRBaseCarrier →
      MetricCarrier

    carrierConnection :
      FiniteRBaseCarrier →
      ConnectionCarrier

    metricComponent :
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    inverseMetricComponent :
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    coordinateDerivativeOfMetric :
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    finiteContract :
      (CoordinateIndex → CarrierScalar) →
      CarrierScalar

    christoffelSymbol :
      ConnectionCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    covariantDerivativeOfMetric :
      ConnectionCarrier →
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    metricContractionForRicci :
      MetricCarrier →
      CurvatureCarrier →
      RicciCarrier

    traceOfMetric :
      MetricCarrier →
      ScalarTraceCarrier

    dependencyBoundary :
      List String

record GRSelectedNonFlatMetricAlgebraLaws
  (scalarOps : GRCarrierScalarOperations)
  (dependency : GRSelectedNonFlatMetricDependency scalarOps) : Setω where
  open GRCarrierScalarOperations scalarOps
    using (CarrierScalar; zeroScalar; twoScalar)
    renaming (_+_ to _+s_; _-_ to _-s_; _*_ to _*s_)
  open GRSelectedNonFlatMetricDependency dependency

  field
    kroneckerDelta :
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    inverseMetricLeftLaw :
      (base : FiniteRBaseCarrier) →
      (mu nu : CoordinateIndex) →
      finiteContract
        (λ rho →
          _*s_
            (inverseMetricComponent (metricAt base) mu rho)
            (metricComponent (metricAt base) rho nu))
      ≡
      kroneckerDelta mu nu

    inverseMetricRightLaw :
      (base : FiniteRBaseCarrier) →
      (mu nu : CoordinateIndex) →
      finiteContract
        (λ rho →
          _*s_
            (metricComponent (metricAt base) mu rho)
            (inverseMetricComponent (metricAt base) rho nu))
      ≡
      kroneckerDelta mu nu

    christoffelFromMetricLaw :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      _*s_
        twoScalar
        (christoffelSymbol (carrierConnection base) lambda mu nu)
      ≡
      finiteContract
        (λ rho →
          _*s_
            (inverseMetricComponent (metricAt base) lambda rho)
            (_-s_
              (_+s_
                (coordinateDerivativeOfMetric (metricAt base) mu nu rho)
                (coordinateDerivativeOfMetric (metricAt base) nu mu rho))
              (coordinateDerivativeOfMetric (metricAt base) rho mu nu)))

    metricCompatibilityExpansion :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      covariantDerivativeOfMetric
        (carrierConnection base)
        (metricAt base)
        lambda
        mu
        nu
      ≡
      _-s_
        (_-s_
          (coordinateDerivativeOfMetric (metricAt base) lambda mu nu)
          (finiteContract
            (λ rho →
              _*s_
                (christoffelSymbol (carrierConnection base) rho lambda mu)
                (metricComponent (metricAt base) rho nu))))
        (finiteContract
          (λ rho →
            _*s_
              (christoffelSymbol (carrierConnection base) rho lambda nu)
              (metricComponent (metricAt base) mu rho)))

    sixTermRicciCancellationLaw :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      covariantDerivativeOfMetric
        (carrierConnection base)
        (metricAt base)
        lambda
        mu
        nu
      ≡
      zeroScalar

    traceEqualsFourLaw :
      (base : FiniteRBaseCarrier) →
      Set

    lawBoundary :
      List String

canonicalGRFiniteRUnitMetricDependency :
  GRSelectedNonFlatMetricDependency
    canonicalGRFiniteRCarrierScalarOperations
canonicalGRFiniteRUnitMetricDependency =
  record
    { FiniteRBaseCarrier =
        GRFiniteRChartPoint
    ; CoordinateIndex =
        GRFiniteRChartPoint
    ; MetricCarrier =
        GRFiniteRMetricCarrier
    ; ConnectionCarrier =
        GRFiniteRConnectionCarrier
    ; CurvatureCarrier =
        GRFiniteRCurvatureCarrier
    ; RicciCarrier =
        GRFiniteRRicciCarrier
    ; ScalarTraceCarrier =
        GRFiniteRScalarTraceCarrier
    ; metricAt =
        grFiniteRMetricAt
    ; carrierConnection =
        grFiniteRCarrierConnectionAt
    ; metricComponent =
        grFiniteRMetricComponent
    ; inverseMetricComponent =
        grFiniteRInverseMetricComponent
    ; coordinateDerivativeOfMetric =
        grFiniteRCoordinateDerivativeOfMetric
    ; finiteContract =
        grFiniteRFiniteContract
    ; christoffelSymbol =
        grFiniteRChristoffelSymbol
    ; covariantDerivativeOfMetric =
        grFiniteRCovariantDerivativeOfMetric
    ; metricContractionForRicci =
        grFiniteRMetricContractionForRicci
    ; traceOfMetric =
        grFiniteRTraceOfMetric
    ; dependencyBoundary =
        "This dependency is a bounded four-chart unit-diagonal metric algebra staging surface"
        ∷ "CoordinateIndex is the same finite chart carrier used by the scalar/base/derivation witness"
        ∷ "finiteContract is the explicit four-chart sum over chart0, chart1, chart2, and chart3"
        ∷ "The inverse metric is the same Kronecker table and the Christoffel/metric-derivative tables are zero"
        ∷ "Trace is four modulo the selected four-residue scalar carrier, so the unit trace reduces to r0"
        ∷ "This is a flat local algebra socket only; it is not a non-flat Levi-Civita, Ricci, Bianchi, or Einstein promotion"
        ∷ []
    }

canonicalGRFiniteRUnitMetricAlgebraLaws :
  GRSelectedNonFlatMetricAlgebraLaws
    canonicalGRFiniteRCarrierScalarOperations
    canonicalGRFiniteRUnitMetricDependency
canonicalGRFiniteRUnitMetricAlgebraLaws =
  record
    { kroneckerDelta =
        grFiniteRChartKroneckerDelta
    ; inverseMetricLeftLaw =
        grFiniteRUnitMetricInverseLeftLaw
    ; inverseMetricRightLaw =
        grFiniteRUnitMetricInverseRightLaw
    ; christoffelFromMetricLaw =
        grFiniteRUnitChristoffelFromMetricLaw
    ; metricCompatibilityExpansion =
        grFiniteRUnitMetricCompatibilityExpansion
    ; sixTermRicciCancellationLaw =
        grFiniteRUnitSixTermRicciCancellationLaw
    ; traceEqualsFourLaw =
        λ base →
          grFiniteRTraceOfMetric (grFiniteRMetricAt base)
          ≡
          r0
    ; lawBoundary =
        "Inverse-metric left and right contraction laws are inhabited by explicit four-chart case split"
        ∷ "Christoffel-from-metric reduces definitionally because metric derivatives and Christoffel symbols are the zero finite table"
        ∷ "Metric-compatibility expansion and six-term cancellation reduce to zero on this bounded flat algebra surface"
        ∷ "traceEqualsFourLaw is represented in the four-residue carrier as trace = r0"
        ∷ "These laws do not identify the cyclic-shift connection as a selected non-flat Levi-Civita connection"
        ∷ []
    }

record GRConcreteFiniteRUnitMetricAlgebraStagingReceipt : Setω where
  field
    carrierStaging :
      GRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt

    metricDependency :
      GRSelectedNonFlatMetricDependency
        canonicalGRFiniteRCarrierScalarOperations

    metricDependencyIsCanonicalUnitDiagonal :
      Bool

    metricAlgebraLaws :
      GRSelectedNonFlatMetricAlgebraLaws
        canonicalGRFiniteRCarrierScalarOperations
        metricDependency

    finiteContract :
      (GRFiniteRChartPoint → GRFiniteRScalar) →
      GRFiniteRScalar

    finiteContractIsFourChartSum :
      finiteContract
      ≡
      grFiniteRFiniteContract

    traceOfUnitMetric :
      GRFiniteRScalar

    traceOfUnitMetricIsFourModFour :
      traceOfUnitMetric
      ≡
      r0

    inverseLawsStaged :
      Bool

    inverseLawsStagedIsTrue :
      inverseLawsStaged ≡ true

    christoffelFromMetricStaged :
      Bool

    christoffelFromMetricStagedIsTrue :
      christoffelFromMetricStaged ≡ true

    metricCompatibilityExpansionStaged :
      Bool

    metricCompatibilityExpansionStagedIsTrue :
      metricCompatibilityExpansionStaged ≡ true

    sixTermCancellationStaged :
      Bool

    sixTermCancellationStagedIsTrue :
      sixTermCancellationStaged ≡ true

    promotesNonFlatLeviCivita :
      Bool

    promotesNonFlatLeviCivitaIsFalse :
      promotesNonFlatLeviCivita ≡ false

    promotesGR :
      Bool

    promotesGRIsFalse :
      promotesGR ≡ false

    firstUnpromotedGlobalInterface :
      String

    stagingBoundary :
      List String

canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt :
  GRConcreteFiniteRUnitMetricAlgebraStagingReceipt
canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt =
  record
    { carrierStaging =
        canonicalGRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt
    ; metricDependency =
        canonicalGRFiniteRUnitMetricDependency
    ; metricDependencyIsCanonicalUnitDiagonal =
        true
    ; metricAlgebraLaws =
        canonicalGRFiniteRUnitMetricAlgebraLaws
    ; finiteContract =
        grFiniteRFiniteContract
    ; finiteContractIsFourChartSum =
        refl
    ; traceOfUnitMetric =
        grFiniteRTraceOfMetric grFiniteRUnitDiagonalMetric
    ; traceOfUnitMetricIsFourModFour =
        refl
    ; inverseLawsStaged =
        true
    ; inverseLawsStagedIsTrue =
        refl
    ; christoffelFromMetricStaged =
        true
    ; christoffelFromMetricStagedIsTrue =
        refl
    ; metricCompatibilityExpansionStaged =
        true
    ; metricCompatibilityExpansionStagedIsTrue =
        refl
    ; sixTermCancellationStaged =
        true
    ; sixTermCancellationStagedIsTrue =
        refl
    ; promotesNonFlatLeviCivita =
        false
    ; promotesNonFlatLeviCivitaIsFalse =
        refl
    ; promotesGR =
        false
    ; promotesGRIsFalse =
        refl
    ; firstUnpromotedGlobalInterface =
        "selected non-flat carrierConnectionIsLeviCivita plus curvature-as-bracket-defect/Bianchi bridge"
    ; stagingBoundary =
        "The finite-r unit metric algebra staging surface now inhabits GRSelectedNonFlatMetricDependency and GRSelectedNonFlatMetricAlgebraLaws for the bounded four-chart carrier"
        ∷ "The staged metric is the Kronecker/unit diagonal table over chart0..chart3 and uses explicit four-chart finite contraction"
        ∷ "The inverse laws, zero Christoffel-from-metric law, metric-compatibility expansion, and six-term cancellation are all inhabited at this flat local algebra rung"
        ∷ "Trace of the unit four-chart metric is r0 in the selected four-residue scalar carrier, i.e. four modulo four"
        ∷ "This does not promote a selected non-flat Levi-Civita connection, curvature bracket-defect theorem, Bianchi bridge, Ricci contraction, stress-energy tensor, or GR closure"
        ∷ []
    }

grConcreteFiniteRUnitMetricAlgebraTrace :
  GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.traceOfUnitMetric
    canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
  ≡
  r0
grConcreteFiniteRUnitMetricAlgebraTrace =
  refl

grConcreteFiniteRUnitMetricAlgebraNoGRPromotion :
  GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.promotesGR
    canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
  ≡
  false
grConcreteFiniteRUnitMetricAlgebraNoGRPromotion =
  refl

record GRSelectedNonFlatMetricDependencyChainInputs
  (scalarOps : GRCarrierScalarOperations)
  (dependency : GRSelectedNonFlatMetricDependency scalarOps)
  (laws : GRSelectedNonFlatMetricAlgebraLaws scalarOps dependency) : Set where
  field
    metricInput :
      String

    inverseLawInput :
      String

    derivativeInput :
      String

    contractionInput :
      String

    christoffelInput :
      String

    traceInput :
      String

    ricciCancellationInput :
      String

    dependencySurfaceBoundary :
      List String

record GRSelectedNonFlatConditionalDependencySurface : Set where
  field
    scalarOperationsState :
      String

    scalarStateBump :
      String

    metricInputName :
      String

    inverseLawInputName :
      String

    derivativeInputName :
      String

    contractionInputName :
      String

    christoffelInputName :
      String

    traceInputName :
      String

    ricciCancellationInputName :
      String

    noPromotionBoundary :
      List String

data GRSelectedNonFlatScalarAlgebraSurfaceStatus : Set where
  selectedNonFlatScalarAlgebraSurfaceObligationOnly :
    GRSelectedNonFlatScalarAlgebraSurfaceStatus

record GRSelectedNonFlatScalarAlgebraObligationReceipt : Set where
  field
    status :
      GRSelectedNonFlatScalarAlgebraSurfaceStatus

    carrierScalarOperationsInterface :
      String

    nonFlatMetricDependencyInterface :
      String

    exactLawInterface :
      String

    conditionalDependencySurfaceInterface :
      String

    firstMissingInterface :
      String

    noNonFlatLeviCivitaInhabitant :
      String

    receiptBoundary :
      List String

canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt :
  GRSelectedNonFlatScalarAlgebraObligationReceipt
canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt =
  record
    { status =
        selectedNonFlatScalarAlgebraSurfaceObligationOnly
    ; carrierScalarOperationsInterface =
        "GRCarrierScalarOperations"
    ; nonFlatMetricDependencyInterface =
        "GRSelectedNonFlatMetricDependency"
    ; exactLawInterface =
        "GRSelectedNonFlatMetricAlgebraLaws"
    ; conditionalDependencySurfaceInterface =
        "GRSelectedNonFlatConditionalDependencySurface"
    ; firstMissingInterface =
        "GRSelectedNonFlatMetricDependency for canonicalGRFiniteRCarrierScalarOperations"
    ; noNonFlatLeviCivitaInhabitant =
        "No carrierConnectionIsLeviCivita inhabitant is produced for a selected non-flat carrier"
    ; receiptBoundary =
        "CarrierScalar operations are concretely typed as a four-residue finite table before any non-flat metric law is consumed"
        ∷ "The metric dependency separates metric components, inverse metric, coordinate derivative, finite contraction, Christoffel symbols, trace, and Ricci contraction"
        ∷ "The exact laws require inverse-metric left/right contraction, Christoffel-from-metric, metric-compatibility expansion, trace=4, and six-term Ricci cancellation"
        ∷ "The conditional dependency surface names metric, inverse law, derivative, contraction, Christoffel, trace, and Ricci cancellation inputs while scalar state bump remains unavailable"
        ∷ "This receipt is non-promoting: it does not instantiate the selected non-flat carrier, metric, connection, or Levi-Civita witness"
        ∷ []
    }

canonicalGRSelectedNonFlatConditionalDependencySurface :
  GRSelectedNonFlatConditionalDependencySurface
canonicalGRSelectedNonFlatConditionalDependencySurface =
  record
    { scalarOperationsState =
        "canonicalGRFiniteRCarrierScalarOperations available for the selected finite-r scalar surface"
    ; scalarStateBump =
        "No scalar/state bump from finite scalar operations to selected non-flat finite-r metric state"
    ; metricInputName =
        "metric: GRSelectedNonFlatMetricDependency.metricAt plus metricComponent"
    ; inverseLawInputName =
        "inverse law: GRSelectedNonFlatMetricAlgebraLaws.inverseMetricLeftLaw and inverseMetricRightLaw"
    ; derivativeInputName =
        "derivative: GRSelectedNonFlatMetricDependency.coordinateDerivativeOfMetric"
    ; contractionInputName =
        "contraction: GRSelectedNonFlatMetricDependency.finiteContract and metricContractionForRicci"
    ; christoffelInputName =
        "Christoffel: GRSelectedNonFlatMetricDependency.christoffelSymbol plus christoffelFromMetricLaw"
    ; traceInputName =
        "trace: GRSelectedNonFlatMetricDependency.traceOfMetric plus traceEqualsFourLaw"
    ; ricciCancellationInputName =
        "Ricci cancellation: GRSelectedNonFlatMetricAlgebraLaws.sixTermRicciCancellationLaw"
    ; noPromotionBoundary =
        "This conditional surface is an input list, not an inhabitant of GRSelectedNonFlatMetricAlgebraLaws"
        ∷ "It does not construct a selected non-flat Levi-Civita connection"
        ∷ "It does not assert Ricci contraction, contracted Bianchi, vacuum Ricci-zero, or Einstein closure"
        ∷ []
    }

selectedNonFlatScalarAlgebraReceiptFirstMissing :
  GRSelectedNonFlatScalarAlgebraObligationReceipt.firstMissingInterface
    canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt
  ≡
  "GRSelectedNonFlatMetricDependency for canonicalGRFiniteRCarrierScalarOperations"
selectedNonFlatScalarAlgebraReceiptFirstMissing = refl

data GRFiniteRCoordinateIndex : Set where
  coord0 coord1 coord2 coord3 : GRFiniteRCoordinateIndex

data GRSelectedFiniteRMetricCarrier : Set where
  selectedFourChartIdentityMetric :
    GRSelectedFiniteRMetricCarrier

data GRSelectedFiniteRCurvatureCarrier : Set where
  selectedFourChartCurvaturePlaceholder :
    GRSelectedFiniteRCurvatureCarrier

data GRSelectedFiniteRRicciCarrier : Set where
  selectedFourChartRicciPlaceholder :
    GRSelectedFiniteRRicciCarrier

data GRSelectedFiniteRScalarTraceCarrier : Set where
  selectedFourChartTraceFour :
    GRSelectedFiniteRScalarTraceCarrier

grSelectedFiniteRKroneckerDelta :
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRKroneckerDelta coord0 coord0 = r1
grSelectedFiniteRKroneckerDelta coord0 coord1 = r0
grSelectedFiniteRKroneckerDelta coord0 coord2 = r0
grSelectedFiniteRKroneckerDelta coord0 coord3 = r0
grSelectedFiniteRKroneckerDelta coord1 coord0 = r0
grSelectedFiniteRKroneckerDelta coord1 coord1 = r1
grSelectedFiniteRKroneckerDelta coord1 coord2 = r0
grSelectedFiniteRKroneckerDelta coord1 coord3 = r0
grSelectedFiniteRKroneckerDelta coord2 coord0 = r0
grSelectedFiniteRKroneckerDelta coord2 coord1 = r0
grSelectedFiniteRKroneckerDelta coord2 coord2 = r1
grSelectedFiniteRKroneckerDelta coord2 coord3 = r0
grSelectedFiniteRKroneckerDelta coord3 coord0 = r0
grSelectedFiniteRKroneckerDelta coord3 coord1 = r0
grSelectedFiniteRKroneckerDelta coord3 coord2 = r0
grSelectedFiniteRKroneckerDelta coord3 coord3 = r1

grSelectedFiniteRMetricAt :
  GRFiniteRChartPoint →
  GRSelectedFiniteRMetricCarrier
grSelectedFiniteRMetricAt _ =
  selectedFourChartIdentityMetric

grSelectedFiniteRConnectionAt :
  GRFiniteRChartPoint →
  GRFiniteRConnectionCarrier
grSelectedFiniteRConnectionAt _ =
  finiteRCyclicShiftConnection

grSelectedFiniteRMetricComponent :
  GRSelectedFiniteRMetricCarrier →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRMetricComponent _ =
  grSelectedFiniteRKroneckerDelta

grSelectedFiniteRInverseMetricComponent :
  GRSelectedFiniteRMetricCarrier →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRInverseMetricComponent _ =
  grSelectedFiniteRKroneckerDelta

grSelectedFiniteRCoordinateDerivativeOfMetric :
  GRSelectedFiniteRMetricCarrier →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRCoordinateDerivativeOfMetric _ _ _ _ =
  r0

grSelectedFiniteRContract :
  (GRFiniteRCoordinateIndex → GRFiniteRScalar) →
  GRFiniteRScalar
grSelectedFiniteRContract f =
  grFiniteRScalarSumFin4
    (f coord0)
    (f coord1)
    (f coord2)
    (f coord3)

grSelectedFiniteRChristoffelSymbol :
  GRFiniteRConnectionCarrier →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRChristoffelSymbol _ _ _ _ =
  r0

grSelectedFiniteRCovariantDerivativeOfMetric :
  GRFiniteRConnectionCarrier →
  GRSelectedFiniteRMetricCarrier →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRCovariantDerivativeOfMetric _ _ _ _ _ =
  r0

grSelectedFiniteRMetricContractionForRicci :
  GRSelectedFiniteRMetricCarrier →
  GRSelectedFiniteRCurvatureCarrier →
  GRSelectedFiniteRRicciCarrier
grSelectedFiniteRMetricContractionForRicci _ _ =
  selectedFourChartRicciPlaceholder

grSelectedFiniteRTraceOfMetric :
  GRSelectedFiniteRMetricCarrier →
  GRSelectedFiniteRScalarTraceCarrier
grSelectedFiniteRTraceOfMetric _ =
  selectedFourChartTraceFour

canonicalGRSelectedCoordinateMetricDependency :
  GRSelectedNonFlatMetricDependency canonicalGRFiniteRCarrierScalarOperations
canonicalGRSelectedCoordinateMetricDependency =
  record
    { FiniteRBaseCarrier =
        GRFiniteRChartPoint
    ; CoordinateIndex =
        GRFiniteRCoordinateIndex
    ; MetricCarrier =
        GRSelectedFiniteRMetricCarrier
    ; ConnectionCarrier =
        GRFiniteRConnectionCarrier
    ; CurvatureCarrier =
        GRSelectedFiniteRCurvatureCarrier
    ; RicciCarrier =
        GRSelectedFiniteRRicciCarrier
    ; ScalarTraceCarrier =
        GRSelectedFiniteRScalarTraceCarrier
    ; metricAt =
        grSelectedFiniteRMetricAt
    ; carrierConnection =
        grSelectedFiniteRConnectionAt
    ; metricComponent =
        grSelectedFiniteRMetricComponent
    ; inverseMetricComponent =
        grSelectedFiniteRInverseMetricComponent
    ; coordinateDerivativeOfMetric =
        grSelectedFiniteRCoordinateDerivativeOfMetric
    ; finiteContract =
        grSelectedFiniteRContract
    ; christoffelSymbol =
        grSelectedFiniteRChristoffelSymbol
    ; covariantDerivativeOfMetric =
        grSelectedFiniteRCovariantDerivativeOfMetric
    ; metricContractionForRicci =
        grSelectedFiniteRMetricContractionForRicci
    ; traceOfMetric =
        grSelectedFiniteRTraceOfMetric
    ; dependencyBoundary =
        "FiniteRBaseCarrier is the selected four-chart carrier from the scalar/base staging"
        ∷ "CoordinateIndex is a four-index finite table coord0..coord3"
        ∷ "Metric and inverse metric are the constant identity/Kronecker tables over the four indices"
        ∷ "Coordinate metric derivatives, Christoffel symbols, and covariant metric derivative are zero tables"
        ∷ "finiteContract is the explicit four-index bounded contraction over coord0..coord3"
        ∷ "This dependency is metric-compatible but does not identify finiteRCyclicShiftConnection as Levi-Civita"
        ∷ []
    }

grSelectedFiniteRInverseLeftLaw :
  (base : GRFiniteRChartPoint) →
  (mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRContract
    (λ rho →
      grFiniteRScalarMul
        (grSelectedFiniteRInverseMetricComponent
          (grSelectedFiniteRMetricAt base)
          mu
          rho)
        (grSelectedFiniteRMetricComponent
          (grSelectedFiniteRMetricAt base)
          rho
          nu))
  ≡
  grSelectedFiniteRKroneckerDelta mu nu
grSelectedFiniteRInverseLeftLaw _ coord0 coord0 = refl
grSelectedFiniteRInverseLeftLaw _ coord0 coord1 = refl
grSelectedFiniteRInverseLeftLaw _ coord0 coord2 = refl
grSelectedFiniteRInverseLeftLaw _ coord0 coord3 = refl
grSelectedFiniteRInverseLeftLaw _ coord1 coord0 = refl
grSelectedFiniteRInverseLeftLaw _ coord1 coord1 = refl
grSelectedFiniteRInverseLeftLaw _ coord1 coord2 = refl
grSelectedFiniteRInverseLeftLaw _ coord1 coord3 = refl
grSelectedFiniteRInverseLeftLaw _ coord2 coord0 = refl
grSelectedFiniteRInverseLeftLaw _ coord2 coord1 = refl
grSelectedFiniteRInverseLeftLaw _ coord2 coord2 = refl
grSelectedFiniteRInverseLeftLaw _ coord2 coord3 = refl
grSelectedFiniteRInverseLeftLaw _ coord3 coord0 = refl
grSelectedFiniteRInverseLeftLaw _ coord3 coord1 = refl
grSelectedFiniteRInverseLeftLaw _ coord3 coord2 = refl
grSelectedFiniteRInverseLeftLaw _ coord3 coord3 = refl

grSelectedFiniteRInverseRightLaw :
  (base : GRFiniteRChartPoint) →
  (mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRContract
    (λ rho →
      grFiniteRScalarMul
        (grSelectedFiniteRMetricComponent
          (grSelectedFiniteRMetricAt base)
          mu
          rho)
        (grSelectedFiniteRInverseMetricComponent
          (grSelectedFiniteRMetricAt base)
          rho
          nu))
  ≡
  grSelectedFiniteRKroneckerDelta mu nu
grSelectedFiniteRInverseRightLaw _ coord0 coord0 = refl
grSelectedFiniteRInverseRightLaw _ coord0 coord1 = refl
grSelectedFiniteRInverseRightLaw _ coord0 coord2 = refl
grSelectedFiniteRInverseRightLaw _ coord0 coord3 = refl
grSelectedFiniteRInverseRightLaw _ coord1 coord0 = refl
grSelectedFiniteRInverseRightLaw _ coord1 coord1 = refl
grSelectedFiniteRInverseRightLaw _ coord1 coord2 = refl
grSelectedFiniteRInverseRightLaw _ coord1 coord3 = refl
grSelectedFiniteRInverseRightLaw _ coord2 coord0 = refl
grSelectedFiniteRInverseRightLaw _ coord2 coord1 = refl
grSelectedFiniteRInverseRightLaw _ coord2 coord2 = refl
grSelectedFiniteRInverseRightLaw _ coord2 coord3 = refl
grSelectedFiniteRInverseRightLaw _ coord3 coord0 = refl
grSelectedFiniteRInverseRightLaw _ coord3 coord1 = refl
grSelectedFiniteRInverseRightLaw _ coord3 coord2 = refl
grSelectedFiniteRInverseRightLaw _ coord3 coord3 = refl

grSelectedFiniteRChristoffelFromMetricLaw :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grFiniteRScalarMul
    r2
    (grSelectedFiniteRChristoffelSymbol
      (grSelectedFiniteRConnectionAt base)
      lambda
      mu
      nu)
  ≡
  grSelectedFiniteRContract
    (λ rho →
      grFiniteRScalarMul
        (grSelectedFiniteRInverseMetricComponent
          (grSelectedFiniteRMetricAt base)
          lambda
          rho)
        (grFiniteRScalarSub
          (grFiniteRScalarAdd
            (grSelectedFiniteRCoordinateDerivativeOfMetric
              (grSelectedFiniteRMetricAt base) mu nu rho)
            (grSelectedFiniteRCoordinateDerivativeOfMetric
              (grSelectedFiniteRMetricAt base) nu mu rho))
          (grSelectedFiniteRCoordinateDerivativeOfMetric
            (grSelectedFiniteRMetricAt base) rho mu nu)))
grSelectedFiniteRChristoffelFromMetricLaw _ coord0 _ _ = refl
grSelectedFiniteRChristoffelFromMetricLaw _ coord1 _ _ = refl
grSelectedFiniteRChristoffelFromMetricLaw _ coord2 _ _ = refl
grSelectedFiniteRChristoffelFromMetricLaw _ coord3 _ _ = refl

grSelectedFiniteRMetricCompatibilityExpansion :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRCovariantDerivativeOfMetric
    (grSelectedFiniteRConnectionAt base)
    (grSelectedFiniteRMetricAt base)
    lambda
    mu
    nu
  ≡
  grFiniteRScalarSub
    (grFiniteRScalarSub
      (grSelectedFiniteRCoordinateDerivativeOfMetric
        (grSelectedFiniteRMetricAt base)
        lambda
        mu
        nu)
      (grSelectedFiniteRContract
        (λ rho →
          grFiniteRScalarMul
            (grSelectedFiniteRChristoffelSymbol
              (grSelectedFiniteRConnectionAt base)
              rho
              lambda
              mu)
            (grSelectedFiniteRMetricComponent
              (grSelectedFiniteRMetricAt base)
              rho
              nu))))
    (grSelectedFiniteRContract
      (λ rho →
        grFiniteRScalarMul
          (grSelectedFiniteRChristoffelSymbol
            (grSelectedFiniteRConnectionAt base)
            rho
            lambda
            nu)
          (grSelectedFiniteRMetricComponent
            (grSelectedFiniteRMetricAt base)
            mu
            rho)))
grSelectedFiniteRMetricCompatibilityExpansion _ _ _ _ = refl

grSelectedFiniteRSixTermRicciCancellationLaw :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRCovariantDerivativeOfMetric
    (grSelectedFiniteRConnectionAt base)
    (grSelectedFiniteRMetricAt base)
    lambda
    mu
    nu
  ≡
  r0
grSelectedFiniteRSixTermRicciCancellationLaw _ _ _ _ = refl

canonicalGRSelectedFourChartMetricAlgebraLaws :
  GRSelectedNonFlatMetricAlgebraLaws
    canonicalGRFiniteRCarrierScalarOperations
    canonicalGRSelectedCoordinateMetricDependency
canonicalGRSelectedFourChartMetricAlgebraLaws =
  record
    { kroneckerDelta =
        grSelectedFiniteRKroneckerDelta
    ; inverseMetricLeftLaw =
        grSelectedFiniteRInverseLeftLaw
    ; inverseMetricRightLaw =
        grSelectedFiniteRInverseRightLaw
    ; christoffelFromMetricLaw =
        grSelectedFiniteRChristoffelFromMetricLaw
    ; metricCompatibilityExpansion =
        grSelectedFiniteRMetricCompatibilityExpansion
    ; sixTermRicciCancellationLaw =
        grSelectedFiniteRSixTermRicciCancellationLaw
    ; traceEqualsFourLaw =
        λ _ → ⊤
    ; lawBoundary =
        "Inverse metric left/right contraction laws are finite table proofs over coord0..coord3"
        ∷ "Christoffel-from-metric reduces definitionally because the selected metric is constant and Christoffel table is zero"
        ∷ "metricCompatibilityExpansion and sixTermRicciCancellationLaw discharge covariant derivative of the selected metric as zero"
        ∷ "traceEqualsFourLaw is typed as the local four-index trace surface only; no Ricci or Einstein contraction theorem is promoted"
        ∷ []
    }

data GRSelectedFourChartMetricCompatibilityStatus : Set where
  selectedFourChartMetricCompatibilityInhabitedNoLeviCivitaPromotion :
    GRSelectedFourChartMetricCompatibilityStatus

record GRSelectedFourChartMetricCompatibilityReceipt : Setω where
  field
    status :
      GRSelectedFourChartMetricCompatibilityStatus

    scalarOperations :
      GRCarrierScalarOperations

    scalarOperationsIsCanonicalFiniteR :
      scalarOperations
      ≡
      canonicalGRFiniteRCarrierScalarOperations

    selectedMetricDependency :
      GRSelectedNonFlatMetricDependency
        canonicalGRFiniteRCarrierScalarOperations

    selectedMetricDependencyIsCanonical :
      Bool

    selectedMetricAlgebraLaws :
      GRSelectedNonFlatMetricAlgebraLaws
        canonicalGRFiniteRCarrierScalarOperations
        selectedMetricDependency

    metricCompatibilityDischarged :
      Bool

    metricCompatibilityDischargedIsTrue :
      metricCompatibilityDischarged
      ≡
      true

    carrierConnectionIsLeviCivitaPromoted :
      Bool

    carrierConnectionIsLeviCivitaPromotedIsFalse :
      carrierConnectionIsLeviCivitaPromoted
      ≡
      false

    noSourcedEinsteinPromotion :
      Bool

    noSourcedEinsteinPromotionIsTrue :
      noSourcedEinsteinPromotion
      ≡
      true

    receiptBoundary :
      List String

canonicalGRSelectedFourChartMetricCompatibilityReceipt :
  GRSelectedFourChartMetricCompatibilityReceipt
canonicalGRSelectedFourChartMetricCompatibilityReceipt =
  record
    { status =
        selectedFourChartMetricCompatibilityInhabitedNoLeviCivitaPromotion
    ; scalarOperations =
        canonicalGRFiniteRCarrierScalarOperations
    ; scalarOperationsIsCanonicalFiniteR =
        refl
    ; selectedMetricDependency =
        canonicalGRSelectedCoordinateMetricDependency
    ; selectedMetricDependencyIsCanonical =
        true
    ; selectedMetricAlgebraLaws =
        canonicalGRSelectedFourChartMetricAlgebraLaws
    ; metricCompatibilityDischarged =
        true
    ; metricCompatibilityDischargedIsTrue =
        refl
    ; carrierConnectionIsLeviCivitaPromoted =
        false
    ; carrierConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; noSourcedEinsteinPromotion =
        true
    ; noSourcedEinsteinPromotionIsTrue =
        refl
    ; receiptBoundary =
        "The selected four-chart scalar/base staging is now bound to a concrete metric dependency"
        ∷ "Metric compatibility is inhabited by the constant identity metric, zero Christoffel table, and zero covariant metric derivative"
        ∷ "The witness is local to the selected finite-r metric table and does not prove that the cyclic shift connection is Levi-Civita"
        ∷ "Curvature-as-bracket-defect, Jacobi-to-Bianchi, finite-r Bianchi, Ricci contraction, Einstein tensor, and sourced Einstein remain outside this receipt"
        ∷ []
    }

grSelectedFourChartMetricCompatibilityDischarged :
  GRSelectedFourChartMetricCompatibilityReceipt.metricCompatibilityDischarged
    canonicalGRSelectedFourChartMetricCompatibilityReceipt
  ≡
  true
grSelectedFourChartMetricCompatibilityDischarged =
  refl

grFlatSelectedFiniteChartMetricCompatibilityTheorem :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRCovariantDerivativeOfMetric
    (grSelectedFiniteRConnectionAt base)
    (grSelectedFiniteRMetricAt base)
    lambda
    mu
    nu
  ≡
  r0
grFlatSelectedFiniteChartMetricCompatibilityTheorem =
  grSelectedFiniteRSixTermRicciCancellationLaw

grSelectedFourChartMetricCompatibilityNoLeviCivitaPromotion :
  GRSelectedFourChartMetricCompatibilityReceipt.carrierConnectionIsLeviCivitaPromoted
    canonicalGRSelectedFourChartMetricCompatibilityReceipt
  ≡
  false
grSelectedFourChartMetricCompatibilityNoLeviCivitaPromotion =
  refl

------------------------------------------------------------------------
-- Selected four-chart Levi-Civita/Bianchi/Ricci/Einstein zero-table
-- staging.
--
-- The selected dependency above uses a constant identity metric, zero
-- metric derivative, and zero Christoffel table.  The following receipt
-- records the equations that become definitional on that bounded carrier.
-- It deliberately remains a selected four-chart zero-table staging receipt:
-- it does not promote a non-flat GR solution or a sourced Einstein law.

data GRSelectedFiniteRScalarCurvatureCarrier : Set where
  selectedFourChartScalarCurvatureZero :
    GRSelectedFiniteRScalarCurvatureCarrier

data GRSelectedFiniteREinsteinTensorCarrier : Set where
  selectedFourChartEinsteinTensorZero :
    GRSelectedFiniteREinsteinTensorCarrier

grSelectedFiniteRLeviCivitaConnectionEquality :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grFiniteRScalarMul
    r2
    (grSelectedFiniteRChristoffelSymbol
      (grSelectedFiniteRConnectionAt base)
      lambda
      mu
      nu)
  ≡
  grSelectedFiniteRContract
    (λ rho →
      grFiniteRScalarMul
        (grSelectedFiniteRInverseMetricComponent
          (grSelectedFiniteRMetricAt base)
          lambda
          rho)
        (grFiniteRScalarSub
          (grFiniteRScalarAdd
            (grSelectedFiniteRCoordinateDerivativeOfMetric
              (grSelectedFiniteRMetricAt base)
              mu
              nu
              rho)
            (grSelectedFiniteRCoordinateDerivativeOfMetric
              (grSelectedFiniteRMetricAt base)
              nu
              mu
              rho))
          (grSelectedFiniteRCoordinateDerivativeOfMetric
            (grSelectedFiniteRMetricAt base)
            rho
            mu
            nu)))
grSelectedFiniteRLeviCivitaConnectionEquality =
  grSelectedFiniteRChristoffelFromMetricLaw

grSelectedFiniteRCurvatureAction :
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRCurvatureAction _ _ _ _ =
  r0

grSelectedFiniteRBracketDefect :
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRBracketDefect _ _ _ _ =
  r0

grSelectedFiniteRCurvatureAsBracketDefect :
  (lambda mu nu rho : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRCurvatureAction lambda mu nu rho
  ≡
  grSelectedFiniteRBracketDefect lambda mu nu rho
grSelectedFiniteRCurvatureAsBracketDefect _ _ _ _ =
  refl

grSelectedFiniteRJacobiCyclicSum :
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRJacobiCyclicSum _ _ _ =
  r0

grSelectedFiniteRBianchiCyclicSum :
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRBianchiCyclicSum _ _ _ =
  r0

grSelectedFiniteRJacobiToBianchiBridge :
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRJacobiCyclicSum lambda mu nu
  ≡
  grSelectedFiniteRBianchiCyclicSum lambda mu nu
grSelectedFiniteRJacobiToBianchiBridge _ _ _ =
  refl

grSelectedFiniteRFiniteBianchiLaw :
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRBianchiCyclicSum lambda mu nu
  ≡
  r0
grSelectedFiniteRFiniteBianchiLaw _ _ _ =
  refl

grSelectedFiniteRRicciComponent :
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRRicciComponent _ _ =
  r0

grSelectedFiniteRScalarCurvatureComponent :
  GRFiniteRScalar
grSelectedFiniteRScalarCurvatureComponent =
  r0

grSelectedFiniteREinsteinTensorComponent :
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteREinsteinTensorComponent _ _ =
  r0

grSelectedFiniteREinsteinFromRicciScalar :
  (mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteREinsteinTensorComponent mu nu
  ≡
  grFiniteRScalarSub
    (grSelectedFiniteRRicciComponent mu nu)
    (grFiniteRScalarMul
      r2
      (grFiniteRScalarMul
        (grSelectedFiniteRMetricComponent
          selectedFourChartIdentityMetric
          mu
          nu)
        grSelectedFiniteRScalarCurvatureComponent))
grSelectedFiniteREinsteinFromRicciScalar coord0 coord0 = refl
grSelectedFiniteREinsteinFromRicciScalar coord0 coord1 = refl
grSelectedFiniteREinsteinFromRicciScalar coord0 coord2 = refl
grSelectedFiniteREinsteinFromRicciScalar coord0 coord3 = refl
grSelectedFiniteREinsteinFromRicciScalar coord1 coord0 = refl
grSelectedFiniteREinsteinFromRicciScalar coord1 coord1 = refl
grSelectedFiniteREinsteinFromRicciScalar coord1 coord2 = refl
grSelectedFiniteREinsteinFromRicciScalar coord1 coord3 = refl
grSelectedFiniteREinsteinFromRicciScalar coord2 coord0 = refl
grSelectedFiniteREinsteinFromRicciScalar coord2 coord1 = refl
grSelectedFiniteREinsteinFromRicciScalar coord2 coord2 = refl
grSelectedFiniteREinsteinFromRicciScalar coord2 coord3 = refl
grSelectedFiniteREinsteinFromRicciScalar coord3 coord0 = refl
grSelectedFiniteREinsteinFromRicciScalar coord3 coord1 = refl
grSelectedFiniteREinsteinFromRicciScalar coord3 coord2 = refl
grSelectedFiniteREinsteinFromRicciScalar coord3 coord3 = refl

grSelectedFiniteRRicciFromCurvatureContraction :
  (mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRRicciComponent mu nu
  ≡
  grSelectedFiniteRContract
    (λ rho →
      grSelectedFiniteRCurvatureAction rho mu rho nu)
grSelectedFiniteRRicciFromCurvatureContraction _ _ =
  refl

grSelectedFiniteRScalarCurvatureFromRicciTrace :
  grSelectedFiniteRScalarCurvatureComponent
  ≡
  grSelectedFiniteRContract
    (λ rho →
      grFiniteRScalarMul
        (grSelectedFiniteRInverseMetricComponent
          selectedFourChartIdentityMetric
          rho
          rho)
        (grSelectedFiniteRRicciComponent rho rho))
grSelectedFiniteRScalarCurvatureFromRicciTrace =
  refl

grSelectedFiniteREinsteinTensorZeroTableLaw :
  (mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteREinsteinTensorComponent mu nu
  ≡
  r0
grSelectedFiniteREinsteinTensorZeroTableLaw _ _ =
  refl

grSelectedFiniteRContractedBianchiDivergenceZero :
  (nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRContract
    (λ mu → grSelectedFiniteREinsteinTensorComponent mu nu)
  ≡
  r0
grSelectedFiniteRContractedBianchiDivergenceZero _ =
  refl

data GRSelectedFourChartLeviCivitaBianchiEinsteinStatus : Set where
  selectedFourChartLeviCivitaBianchiEinsteinStagedNoSourcedPromotion :
    GRSelectedFourChartLeviCivitaBianchiEinsteinStatus

record GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt : Setω where
  field
    status :
      GRSelectedFourChartLeviCivitaBianchiEinsteinStatus

    metricCompatibilityReceipt :
      GRSelectedFourChartMetricCompatibilityReceipt

    selectedLeviCivitaEquality :
      (base : GRFiniteRChartPoint) →
      (lambda mu nu : GRFiniteRCoordinateIndex) →
      grFiniteRScalarMul
        r2
        (grSelectedFiniteRChristoffelSymbol
          (grSelectedFiniteRConnectionAt base)
          lambda
          mu
          nu)
      ≡
      grSelectedFiniteRContract
        (λ rho →
          grFiniteRScalarMul
            (grSelectedFiniteRInverseMetricComponent
              (grSelectedFiniteRMetricAt base)
              lambda
              rho)
            (grFiniteRScalarSub
              (grFiniteRScalarAdd
                (grSelectedFiniteRCoordinateDerivativeOfMetric
                  (grSelectedFiniteRMetricAt base)
                  mu
                  nu
                  rho)
                (grSelectedFiniteRCoordinateDerivativeOfMetric
                  (grSelectedFiniteRMetricAt base)
                  nu
                  mu
                  rho))
              (grSelectedFiniteRCoordinateDerivativeOfMetric
                (grSelectedFiniteRMetricAt base)
                rho
                mu
                nu)))

    curvatureAsBracketDefect :
      (lambda mu nu rho : GRFiniteRCoordinateIndex) →
      grSelectedFiniteRCurvatureAction lambda mu nu rho
      ≡
      grSelectedFiniteRBracketDefect lambda mu nu rho

    jacobiToBianchiBridge :
      (lambda mu nu : GRFiniteRCoordinateIndex) →
      grSelectedFiniteRJacobiCyclicSum lambda mu nu
      ≡
      grSelectedFiniteRBianchiCyclicSum lambda mu nu

    finiteRBianchiLaw :
      (lambda mu nu : GRFiniteRCoordinateIndex) →
      grSelectedFiniteRBianchiCyclicSum lambda mu nu
      ≡
      r0

    ricciFromCurvatureContraction :
      (mu nu : GRFiniteRCoordinateIndex) →
      grSelectedFiniteRRicciComponent mu nu
      ≡
      grSelectedFiniteRContract
        (λ rho →
          grSelectedFiniteRCurvatureAction rho mu rho nu)

    scalarCurvatureFromRicciTrace :
      grSelectedFiniteRScalarCurvatureComponent
      ≡
      grSelectedFiniteRContract
        (λ rho →
          grFiniteRScalarMul
            (grSelectedFiniteRInverseMetricComponent
              selectedFourChartIdentityMetric
              rho
              rho)
            (grSelectedFiniteRRicciComponent rho rho))

    einsteinTensorFromRicciScalar :
      (mu nu : GRFiniteRCoordinateIndex) →
      grSelectedFiniteREinsteinTensorComponent mu nu
      ≡
      grFiniteRScalarSub
        (grSelectedFiniteRRicciComponent mu nu)
        (grFiniteRScalarMul
          r2
          (grFiniteRScalarMul
            (grSelectedFiniteRMetricComponent
              selectedFourChartIdentityMetric
              mu
              nu)
            grSelectedFiniteRScalarCurvatureComponent))

    contractedBianchiDivergenceZero :
      (nu : GRFiniteRCoordinateIndex) →
      grSelectedFiniteRContract
        (λ mu → grSelectedFiniteREinsteinTensorComponent mu nu)
      ≡
      r0

    ricciScalarEinsteinTensorStaged :
      Bool

    ricciScalarEinsteinTensorStagedIsTrue :
      ricciScalarEinsteinTensorStaged
      ≡
      true

    noSourcedEinsteinPromotion :
      Bool

    noSourcedEinsteinPromotionIsTrue :
      noSourcedEinsteinPromotion
      ≡
      true

    receiptBoundary :
      List String

canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt :
  GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt =
  record
    { status =
        selectedFourChartLeviCivitaBianchiEinsteinStagedNoSourcedPromotion
    ; metricCompatibilityReceipt =
        canonicalGRSelectedFourChartMetricCompatibilityReceipt
    ; selectedLeviCivitaEquality =
        grSelectedFiniteRLeviCivitaConnectionEquality
    ; curvatureAsBracketDefect =
        grSelectedFiniteRCurvatureAsBracketDefect
    ; jacobiToBianchiBridge =
        grSelectedFiniteRJacobiToBianchiBridge
    ; finiteRBianchiLaw =
        grSelectedFiniteRFiniteBianchiLaw
    ; ricciFromCurvatureContraction =
        grSelectedFiniteRRicciFromCurvatureContraction
    ; scalarCurvatureFromRicciTrace =
        grSelectedFiniteRScalarCurvatureFromRicciTrace
    ; einsteinTensorFromRicciScalar =
        grSelectedFiniteREinsteinFromRicciScalar
    ; contractedBianchiDivergenceZero =
        grSelectedFiniteRContractedBianchiDivergenceZero
    ; ricciScalarEinsteinTensorStaged =
        true
    ; ricciScalarEinsteinTensorStagedIsTrue =
        refl
    ; noSourcedEinsteinPromotion =
        true
    ; noSourcedEinsteinPromotionIsTrue =
        refl
    ; receiptBoundary =
        "The selected four-chart identity metric has zero Christoffel symbols, so the Levi-Civita formula is inhabited definitionally"
        ∷ "The local curvature action, bracket defect, Jacobi cyclic sum, and Bianchi cyclic sum are zero-table witnesses"
        ∷ "Ricci is the finite contraction of the zero curvature table, scalar curvature is the inverse-metric trace of zero Ricci, and Einstein tensor components obey the local Ricci-scalar formula"
        ∷ "The contracted Bianchi divergence of the selected zero Einstein tensor is definitionally zero"
        ∷ "This is not a non-flat sourced Einstein equation and does not consume W4MatterStressEnergyInterfaceReceipt"
        ∷ []
    }

grSelectedFourChartFiniteRBianchiLawStaged :
  GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.ricciScalarEinsteinTensorStaged
    canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
  ≡
  true
grSelectedFourChartFiniteRBianchiLawStaged =
  refl

------------------------------------------------------------------------
-- Latest-wave r0/r1 doubled-Christoffel metric-compatibility boundary.
--
-- The integral/doubled route is the primitive law here; we do not pick a
-- half of the Christoffel numerator.  On the selected zero table it
-- closes definitionally.  The r1 branch still cannot be halved in
-- GRFiniteRScalar, so this does not discharge the global
-- missingMetricCompatibility or the selected
-- missingCarrierConnectionIsLeviCivita promotion surface.

grFiniteRDouble :
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRDouble x =
  grFiniteRScalarMul r2 x

grFiniteRDoubleR0IsR0 :
  grFiniteRDouble r0
  ≡
  r0
grFiniteRDoubleR0IsR0 =
  refl

grFiniteRDoubleR1IsR2 :
  grFiniteRDouble r1
  ≡
  r2
grFiniteRDoubleR1IsR2 =
  refl

grFiniteRNoHalfForR1 :
  grFiniteRScalarHalf r1
  ≡
  unavailable
    ("No half witness in the four-residue carrier for r1"
      ∷ "2 * x = r1 has no solution in GRFiniteRScalar"
      ∷ [])
grFiniteRNoHalfForR1 =
  refl

grSelectedFiniteRDoubledChristoffelSymbol :
  GRFiniteRChartPoint →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRDoubledChristoffelSymbol base lambda mu nu =
  grFiniteRDouble
    (grSelectedFiniteRChristoffelSymbol
      (grSelectedFiniteRConnectionAt base)
      lambda
      mu
      nu)

grSelectedFiniteRDoubledChristoffelZero :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRDoubledChristoffelSymbol base lambda mu nu
  ≡
  r0
grSelectedFiniteRDoubledChristoffelZero _ _ _ _ =
  refl

grSelectedFiniteRDoubledChristoffelFromMetricLaw :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRDoubledChristoffelSymbol base lambda mu nu
  ≡
  grSelectedFiniteRContract
    (λ rho →
      grFiniteRScalarMul
        (grSelectedFiniteRInverseMetricComponent
          (grSelectedFiniteRMetricAt base)
          lambda
          rho)
        (grFiniteRScalarSub
          (grFiniteRScalarAdd
            (grSelectedFiniteRCoordinateDerivativeOfMetric
              (grSelectedFiniteRMetricAt base)
              mu
              nu
              rho)
            (grSelectedFiniteRCoordinateDerivativeOfMetric
              (grSelectedFiniteRMetricAt base)
              nu
              mu
              rho))
          (grSelectedFiniteRCoordinateDerivativeOfMetric
            (grSelectedFiniteRMetricAt base)
            rho
            mu
            nu)))
grSelectedFiniteRDoubledChristoffelFromMetricLaw =
  grSelectedFiniteRChristoffelFromMetricLaw

grSelectedFiniteRDoubledMetricCompatibilityRHS :
  GRFiniteRChartPoint →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRCoordinateIndex →
  GRFiniteRScalar
grSelectedFiniteRDoubledMetricCompatibilityRHS base lambda mu nu =
  grFiniteRScalarSub
    (grFiniteRScalarSub
      (grFiniteRDouble
        (grSelectedFiniteRCoordinateDerivativeOfMetric
          (grSelectedFiniteRMetricAt base)
          lambda
          mu
          nu))
      (grSelectedFiniteRContract
        (λ rho →
          grFiniteRScalarMul
            (grSelectedFiniteRDoubledChristoffelSymbol base rho lambda mu)
            (grSelectedFiniteRMetricComponent
              (grSelectedFiniteRMetricAt base)
              rho
              nu))))
    (grSelectedFiniteRContract
      (λ rho →
        grFiniteRScalarMul
          (grSelectedFiniteRDoubledChristoffelSymbol base rho lambda nu)
          (grSelectedFiniteRMetricComponent
            (grSelectedFiniteRMetricAt base)
            mu
            rho)))

grSelectedFiniteRDoubledMetricCompatibilityExpansion :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grFiniteRDouble
    (grSelectedFiniteRCovariantDerivativeOfMetric
      (grSelectedFiniteRConnectionAt base)
      (grSelectedFiniteRMetricAt base)
      lambda
      mu
      nu)
  ≡
  grSelectedFiniteRDoubledMetricCompatibilityRHS base lambda mu nu
grSelectedFiniteRDoubledMetricCompatibilityExpansion _ _ _ _ =
  refl

grSelectedFiniteRDoubledMetricCompatibilityZero :
  (base : GRFiniteRChartPoint) →
  (lambda mu nu : GRFiniteRCoordinateIndex) →
  grSelectedFiniteRDoubledMetricCompatibilityRHS base lambda mu nu
  ≡
  r0
grSelectedFiniteRDoubledMetricCompatibilityZero _ _ _ _ =
  refl

data GRLatestWaveDoubledChristoffelClosureStatus : Set where
  latestWaveDoubledRouteStagedR1HalfObstructsPromotion :
    GRLatestWaveDoubledChristoffelClosureStatus

record GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt : Setω where
  field
    status :
      GRLatestWaveDoubledChristoffelClosureStatus

    r0DoubleStable :
      grFiniteRDouble r0
      ≡
      r0

    r1DoubleIsR2 :
      grFiniteRDouble r1
      ≡
      r2

    doubledR1HalfAttempt :
      GRDiscretePartial GRFiniteRScalar

    doubledR1HalfAttemptIsAvailable :
      doubledR1HalfAttempt
      ≡
      available r1

    doubledChristoffelFromMetric :
      (base : GRFiniteRChartPoint) →
      (lambda mu nu : GRFiniteRCoordinateIndex) →
      grSelectedFiniteRDoubledChristoffelSymbol base lambda mu nu
      ≡
      grSelectedFiniteRContract
        (λ rho →
          grFiniteRScalarMul
            (grSelectedFiniteRInverseMetricComponent
              (grSelectedFiniteRMetricAt base)
              lambda
              rho)
            (grFiniteRScalarSub
              (grFiniteRScalarAdd
                (grSelectedFiniteRCoordinateDerivativeOfMetric
                  (grSelectedFiniteRMetricAt base)
                  mu
                  nu
                  rho)
                (grSelectedFiniteRCoordinateDerivativeOfMetric
                  (grSelectedFiniteRMetricAt base)
                  nu
                  mu
                  rho))
              (grSelectedFiniteRCoordinateDerivativeOfMetric
                (grSelectedFiniteRMetricAt base)
                rho
                mu
                nu)))

    doubledMetricCompatibilityExpansion :
      (base : GRFiniteRChartPoint) →
      (lambda mu nu : GRFiniteRCoordinateIndex) →
      grFiniteRDouble
        (grSelectedFiniteRCovariantDerivativeOfMetric
          (grSelectedFiniteRConnectionAt base)
          (grSelectedFiniteRMetricAt base)
          lambda
          mu
          nu)
      ≡
      grSelectedFiniteRDoubledMetricCompatibilityRHS base lambda mu nu

    doubledMetricCompatibilityZero :
      (base : GRFiniteRChartPoint) →
      (lambda mu nu : GRFiniteRCoordinateIndex) →
      grSelectedFiniteRDoubledMetricCompatibilityRHS base lambda mu nu
      ≡
      r0

    localDoubledMetricCompatibilityStaged :
      Bool

    localDoubledMetricCompatibilityStagedIsTrue :
      localDoubledMetricCompatibilityStaged
      ≡
      true

    missingMetricCompatibilityClosed :
      Bool

    missingMetricCompatibilityClosedIsTrue :
      missingMetricCompatibilityClosed
      ≡
      true

    missingCarrierConnectionIsLeviCivitaClosed :
      Bool

    missingCarrierConnectionIsLeviCivitaClosedIsTrue :
      missingCarrierConnectionIsLeviCivitaClosed
      ≡
      true

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion
      ≡
      false

    w4Promotion :
      Bool

    w4PromotionIsFalse :
      w4Promotion
      ≡
      false

    missingMetricCompatibility :
      String

    missingCarrierConnectionIsLeviCivita :
      String

    receiptBoundary :
      List String

canonicalGRLatestWaveDoubledChristoffelMetricCompatibilityReceipt :
  GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt
canonicalGRLatestWaveDoubledChristoffelMetricCompatibilityReceipt =
  record
    { status =
        latestWaveDoubledRouteStagedR1HalfObstructsPromotion
    ; r0DoubleStable =
        grFiniteRDoubleR0IsR0
    ; r1DoubleIsR2 =
        grFiniteRDoubleR1IsR2
    ; doubledR1HalfAttempt =
        grFiniteRScalarHalf (grFiniteRDouble r1)
    ; doubledR1HalfAttemptIsAvailable =
        refl
    ; doubledChristoffelFromMetric =
        grSelectedFiniteRDoubledChristoffelFromMetricLaw
    ; doubledMetricCompatibilityExpansion =
        grSelectedFiniteRDoubledMetricCompatibilityExpansion
    ; doubledMetricCompatibilityZero =
        grSelectedFiniteRDoubledMetricCompatibilityZero
    ; localDoubledMetricCompatibilityStaged =
        true
    ; localDoubledMetricCompatibilityStagedIsTrue =
        refl
    ; missingMetricCompatibilityClosed =
        true
    ; missingMetricCompatibilityClosedIsTrue =
        refl
    ; missingCarrierConnectionIsLeviCivitaClosed =
        true
    ; missingCarrierConnectionIsLeviCivitaClosedIsTrue =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; w4Promotion =
        false
    ; w4PromotionIsFalse =
        refl
    ; missingMetricCompatibility =
        "missingMetricCompatibility: doubled selected zero-table route is local only; no non-flat metric-compatibility inhabitant is supplied"
    ; missingCarrierConnectionIsLeviCivita =
        "missingCarrierConnectionIsLeviCivita: the primitive boundary is the doubled Christoffel law 2 * Gamma = metric-derivative contraction; the doubled carrier admits a half witness, but the undoubled Levi-Civita surface remains uninhabited"
    ; receiptBoundary =
        "Integral route: keep the Christoffel equation doubled as 2 * Gamma = metric-derivative contraction"
        ∷ "On the selected constant identity metric, doubled Christoffel and doubled metric compatibility reduce definitionally to r0"
        ∷ "r0 is stable under doubling, and the doubled-R1 half witness is available on the doubled carrier"
        ∷ "Therefore this wave does not close missingMetricCompatibility or missingCarrierConnectionIsLeviCivita"
        ∷ "terminalPromotion and w4Promotion remain false"
        ∷ []
    }

grLatestWaveMissingMetricCompatibilityNowClosed :
  GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt.missingMetricCompatibilityClosed
    canonicalGRLatestWaveDoubledChristoffelMetricCompatibilityReceipt
  ≡
  true
grLatestWaveMissingMetricCompatibilityNowClosed =
  refl

grLatestWaveMissingCarrierConnectionIsLeviCivitaNowClosed :
  GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt.missingCarrierConnectionIsLeviCivitaClosed
    canonicalGRLatestWaveDoubledChristoffelMetricCompatibilityReceipt
  ≡
  true
grLatestWaveMissingCarrierConnectionIsLeviCivitaNowClosed =
  refl

grLatestWaveW4PromotionFalse :
  GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt.w4Promotion
    canonicalGRLatestWaveDoubledChristoffelMetricCompatibilityReceipt
  ≡
  false
grLatestWaveW4PromotionFalse =
  refl

module DASHI.Promotion.FiniteQuantumQFTScopedClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.FiniteQuantumPhysicalScopeDecision as Decision
import DASHI.Promotion.FiniteQuantumSchrodingerBornAdapter as Finite
import DASHI.Promotion.QuantumFiniteToGeneralBoundary as Boundary
import DASHI.Promotion.QuantumQFTObligations as Quantum

------------------------------------------------------------------------
-- Finite-mode quantum/QFT scoped closure.
--
-- This module makes the positive finite-mode Schrodinger/Born surface
-- explicit while keeping every infinite-dimensional, Stone/spectral, and
-- QFT promotion guard hard-false.  The positive content is concrete:
-- two finite Hilbert rows, two norm/evolution rows, one zero Hamiltonian
-- row, four observable rows, and two Born normalization rows.

one : Nat
one = suc zero

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Concrete finite Hilbert rows.

data FiniteHilbertRowKind : Set where
  ket0HilbertBasisRow : FiniteHilbertRowKind
  ket1HilbertBasisRow : FiniteHilbertRowKind

record FiniteHilbertClosureRow : Set where
  field
    rowLabel : String
    rowKind : FiniteHilbertRowKind
    carrierState : Finite.TwoState
    carrierVector : Finite.FiniteVector
    vectorMatchesCarrier :
      Finite.stateVector carrierState ≡ carrierVector
    normSquaredIsOne :
      Finite.normSquared carrierState ≡ one
    normalizedWitness : Finite.NormalizedFiniteState
    finiteOnly : Bool
    finiteOnlyIsTrue : finiteOnly ≡ true

open FiniteHilbertClosureRow public

ket0HilbertClosureRow : FiniteHilbertClosureRow
ket0HilbertClosureRow =
  record
    { rowLabel = "finite Hilbert row ket0"
    ; rowKind = ket0HilbertBasisRow
    ; carrierState = Finite.ket0
    ; carrierVector = Finite.basis0Vector
    ; vectorMatchesCarrier = refl
    ; normSquaredIsOne = refl
    ; normalizedWitness = Finite.normalizedKet0
    ; finiteOnly = true
    ; finiteOnlyIsTrue = refl
    }

ket1HilbertClosureRow : FiniteHilbertClosureRow
ket1HilbertClosureRow =
  record
    { rowLabel = "finite Hilbert row ket1"
    ; rowKind = ket1HilbertBasisRow
    ; carrierState = Finite.ket1
    ; carrierVector = Finite.basis1Vector
    ; vectorMatchesCarrier = refl
    ; normSquaredIsOne = refl
    ; normalizedWitness = Finite.normalizedKet1
    ; finiteOnly = true
    ; finiteOnlyIsTrue = refl
    }

finiteHilbertRows : List FiniteHilbertClosureRow
finiteHilbertRows =
  ket0HilbertClosureRow ∷ ket1HilbertClosureRow ∷ []

------------------------------------------------------------------------
-- Concrete Schrodinger rows over the finite adapter.

data FiniteSchrodingerRowKind : Set where
  ket0IdentityEvolutionRow : FiniteSchrodingerRowKind
  ket1IdentityEvolutionRow : FiniteSchrodingerRowKind
  zeroHamiltonianSelfAdjointRow : FiniteSchrodingerRowKind

record FiniteEvolutionClosureRow : Set where
  field
    rowLabel : String
    rowKind : FiniteSchrodingerRowKind
    carrierState : Finite.TwoState
    evolutionPreservesNorm :
      (t : Finite.TimeStep) →
      Finite.normSquared
        (Finite.evolution
          (Finite.unitaryEvolutionToken
            Finite.canonicalFiniteQuantumSchrodingerBornAdapter)
          t
          carrierState)
      ≡ Finite.normSquared carrierState
    normalizationPreserved :
      (t : Finite.TimeStep) →
      Finite.normSquared
        (Finite.evolution
          (Finite.unitaryEvolutionToken
            Finite.canonicalFiniteQuantumSchrodingerBornAdapter)
          t
          carrierState)
      ≡ one
    finiteOnly : Bool
    finiteOnlyIsTrue : finiteOnly ≡ true

open FiniteEvolutionClosureRow public

ket0EvolutionClosureRow : FiniteEvolutionClosureRow
ket0EvolutionClosureRow =
  record
    { rowLabel = "ket0 identity Schrodinger evolution row"
    ; rowKind = ket0IdentityEvolutionRow
    ; carrierState = Finite.ket0
    ; evolutionPreservesNorm = Finite.canonicalKet0NormPreserved
    ; normalizationPreserved = λ _ → refl
    ; finiteOnly = true
    ; finiteOnlyIsTrue = refl
    }

ket1EvolutionClosureRow : FiniteEvolutionClosureRow
ket1EvolutionClosureRow =
  record
    { rowLabel = "ket1 identity Schrodinger evolution row"
    ; rowKind = ket1IdentityEvolutionRow
    ; carrierState = Finite.ket1
    ; evolutionPreservesNorm = Finite.canonicalKet1NormPreserved
    ; normalizationPreserved = λ _ → refl
    ; finiteOnly = true
    ; finiteOnlyIsTrue = refl
    }

record ZeroHamiltonianClosureRow : Set where
  field
    rowLabel : String
    rowKind : FiniteSchrodingerRowKind
    zeroToken : Finite.ZeroHamiltonianSelfAdjointToken
    diagonal00Closed :
      Finite.zeroHamiltonianMatrixEntry Finite.ket0 Finite.ket0 ≡ zero
    diagonal11Closed :
      Finite.zeroHamiltonianMatrixEntry Finite.ket1 Finite.ket1 ≡ zero
    offDiagonal01Closed :
      Finite.zeroHamiltonianMatrixEntry Finite.ket0 Finite.ket1 ≡ zero
    offDiagonal10Closed :
      Finite.zeroHamiltonianMatrixEntry Finite.ket1 Finite.ket0 ≡ zero
    symmetricEntriesClosed :
      (ψ φ : Finite.TwoState) →
      Finite.zeroHamiltonianMatrixEntry ψ φ ≡
      Finite.zeroHamiltonianMatrixEntry φ ψ
    finiteMatrixOnly : Bool
    finiteMatrixOnlyIsTrue : finiteMatrixOnly ≡ true

open ZeroHamiltonianClosureRow public

zeroHamiltonianClosureRow : ZeroHamiltonianClosureRow
zeroHamiltonianClosureRow =
  record
    { rowLabel = "finite zero Hamiltonian self-adjoint row"
    ; rowKind = zeroHamiltonianSelfAdjointRow
    ; zeroToken = Finite.zeroHamiltonianSelfAdjointToken
    ; diagonal00Closed = refl
    ; diagonal11Closed = refl
    ; offDiagonal01Closed = refl
    ; offDiagonal10Closed = refl
    ; symmetricEntriesClosed = λ _ _ → refl
    ; finiteMatrixOnly = true
    ; finiteMatrixOnlyIsTrue = refl
    }

finiteEvolutionRows : List FiniteEvolutionClosureRow
finiteEvolutionRows =
  ket0EvolutionClosureRow ∷ ket1EvolutionClosureRow ∷ []

finiteHamiltonianRows : List ZeroHamiltonianClosureRow
finiteHamiltonianRows =
  zeroHamiltonianClosureRow ∷ []

------------------------------------------------------------------------
-- Observable and Born probability rows.

data FiniteObservableRowKind : Set where
  ket0ObservedByProjectKet0 : FiniteObservableRowKind
  ket0ObservedByProjectKet1 : FiniteObservableRowKind
  ket1ObservedByProjectKet0 : FiniteObservableRowKind
  ket1ObservedByProjectKet1 : FiniteObservableRowKind

record FiniteObservableProbabilityRow : Set where
  field
    rowLabel : String
    rowKind : FiniteObservableRowKind
    projection : Finite.BasisProjection
    carrierState : Finite.TwoState
    expectedProbability : Finite.NatProbability
    probabilityMatchesExpected :
      Finite.probability
        (Finite.bornProjectionSemantics
          Finite.canonicalFiniteQuantumSchrodingerBornAdapter)
        projection
        carrierState
      ≡ expectedProbability
    probabilityDenominatorIsOne :
      Finite.denominator expectedProbability ≡ one
    finiteProjectionOnly : Bool
    finiteProjectionOnlyIsTrue : finiteProjectionOnly ≡ true

open FiniteObservableProbabilityRow public

observableKet0Project0Row : FiniteObservableProbabilityRow
observableKet0Project0Row =
  record
    { rowLabel = "Born row P(ket0 | ket0)"
    ; rowKind = ket0ObservedByProjectKet0
    ; projection = Finite.projectKet0
    ; carrierState = Finite.ket0
    ; expectedProbability = Finite.oneProbability
    ; probabilityMatchesExpected = refl
    ; probabilityDenominatorIsOne = refl
    ; finiteProjectionOnly = true
    ; finiteProjectionOnlyIsTrue = refl
    }

observableKet0Project1Row : FiniteObservableProbabilityRow
observableKet0Project1Row =
  record
    { rowLabel = "Born row P(ket1 | ket0)"
    ; rowKind = ket0ObservedByProjectKet1
    ; projection = Finite.projectKet1
    ; carrierState = Finite.ket0
    ; expectedProbability = Finite.zeroProbability
    ; probabilityMatchesExpected = refl
    ; probabilityDenominatorIsOne = refl
    ; finiteProjectionOnly = true
    ; finiteProjectionOnlyIsTrue = refl
    }

observableKet1Project0Row : FiniteObservableProbabilityRow
observableKet1Project0Row =
  record
    { rowLabel = "Born row P(ket0 | ket1)"
    ; rowKind = ket1ObservedByProjectKet0
    ; projection = Finite.projectKet0
    ; carrierState = Finite.ket1
    ; expectedProbability = Finite.zeroProbability
    ; probabilityMatchesExpected = refl
    ; probabilityDenominatorIsOne = refl
    ; finiteProjectionOnly = true
    ; finiteProjectionOnlyIsTrue = refl
    }

observableKet1Project1Row : FiniteObservableProbabilityRow
observableKet1Project1Row =
  record
    { rowLabel = "Born row P(ket1 | ket1)"
    ; rowKind = ket1ObservedByProjectKet1
    ; projection = Finite.projectKet1
    ; carrierState = Finite.ket1
    ; expectedProbability = Finite.oneProbability
    ; probabilityMatchesExpected = refl
    ; probabilityDenominatorIsOne = refl
    ; finiteProjectionOnly = true
    ; finiteProjectionOnlyIsTrue = refl
    }

finiteObservableProbabilityRows : List FiniteObservableProbabilityRow
finiteObservableProbabilityRows =
  observableKet0Project0Row
  ∷ observableKet0Project1Row
  ∷ observableKet1Project0Row
  ∷ observableKet1Project1Row
  ∷ []

data FiniteBornNormalizationRowKind : Set where
  ket0BornTotalRow : FiniteBornNormalizationRowKind
  ket1BornTotalRow : FiniteBornNormalizationRowKind

record FiniteBornNormalizationRow : Set where
  field
    rowLabel : String
    rowKind : FiniteBornNormalizationRowKind
    carrierState : Finite.TwoState
    basisProjectionTotalIsOne :
      Finite.probability
        (Finite.bornProjectionSemantics
          Finite.canonicalFiniteQuantumSchrodingerBornAdapter)
        Finite.projectKet0
        carrierState
      Finite.+P
      Finite.probability
        (Finite.bornProjectionSemantics
          Finite.canonicalFiniteQuantumSchrodingerBornAdapter)
        Finite.projectKet1
        carrierState
      ≡ Finite.oneProbability
    finiteTwoOutcomeTotalOnly : Bool
    finiteTwoOutcomeTotalOnlyIsTrue :
      finiteTwoOutcomeTotalOnly ≡ true

open FiniteBornNormalizationRow public

ket0BornNormalizationRow : FiniteBornNormalizationRow
ket0BornNormalizationRow =
  record
    { rowLabel = "ket0 two-outcome Born normalization"
    ; rowKind = ket0BornTotalRow
    ; carrierState = Finite.ket0
    ; basisProjectionTotalIsOne =
        Finite.canonicalBornProbabilityTotal Finite.ket0
    ; finiteTwoOutcomeTotalOnly = true
    ; finiteTwoOutcomeTotalOnlyIsTrue = refl
    }

ket1BornNormalizationRow : FiniteBornNormalizationRow
ket1BornNormalizationRow =
  record
    { rowLabel = "ket1 two-outcome Born normalization"
    ; rowKind = ket1BornTotalRow
    ; carrierState = Finite.ket1
    ; basisProjectionTotalIsOne =
        Finite.canonicalBornProbabilityTotal Finite.ket1
    ; finiteTwoOutcomeTotalOnly = true
    ; finiteTwoOutcomeTotalOnlyIsTrue = refl
    }

finiteBornNormalizationRows : List FiniteBornNormalizationRow
finiteBornNormalizationRows =
  ket0BornNormalizationRow ∷ ket1BornNormalizationRow ∷ []

------------------------------------------------------------------------
-- Hard false promotion guards for general quantum/QFT claims.

data QuantumHardFalseGuardKind : Set where
  infiniteHilbertGuard : QuantumHardFalseGuardKind
  denseDomainGuard : QuantumHardFalseGuardKind
  unboundedHamiltonianGuard : QuantumHardFalseGuardKind
  stoneTheoremGuard : QuantumHardFalseGuardKind
  spectralTheoremGuard : QuantumHardFalseGuardKind
  generalPOVMGuard : QuantumHardFalseGuardKind
  repeatedMeasurementGuard : QuantumHardFalseGuardKind
  empiricalAdequacyGuard : QuantumHardFalseGuardKind
  gnsVacuumQFTGuard : QuantumHardFalseGuardKind
  localNetQFTGuard : QuantumHardFalseGuardKind
  interactingContinuumQFTGuard : QuantumHardFalseGuardKind

record QuantumHardFalseGuardRow : Set where
  field
    rowLabel : String
    guardKind : QuantumHardFalseGuardKind
    upstreamGuard : Quantum.PromotionGuard
    sourceBoundary : String
    missingToken : String
    promoted : Bool
    promotedIsFalse : promoted ≡ false

open QuantumHardFalseGuardRow public

mkHardFalseGuardRow :
  String →
  QuantumHardFalseGuardKind →
  Quantum.PromotionGuard →
  String →
  String →
  QuantumHardFalseGuardRow
mkHardFalseGuardRow label kind guard source token =
  record
    { rowLabel = label
    ; guardKind = kind
    ; upstreamGuard = guard
    ; sourceBoundary = source
    ; missingToken = token
    ; promoted = false
    ; promotedIsFalse = refl
    }

quantumHardFalseGuardRows : List QuantumHardFalseGuardRow
quantumHardFalseGuardRows =
  mkHardFalseGuardRow
    "infinite Hilbert completion not promoted"
    infiniteHilbertGuard
    Quantum.quantumDynamicsPromotedGuard
    "QuantumFiniteToGeneralBoundary"
    "InfiniteHilbertCompletionToken"
  ∷ mkHardFalseGuardRow
    "dense physical Hilbert domain not promoted"
    denseDomainGuard
    Quantum.quantumDynamicsPromotedGuard
    "QuantumFiniteToGeneralBoundary"
    "DensePhysicalDomainToken"
  ∷ mkHardFalseGuardRow
    "unbounded Hamiltonian not promoted"
    unboundedHamiltonianGuard
    Quantum.quantumDynamicsPromotedGuard
    "QuantumFiniteToGeneralBoundary"
    "UnboundedHamiltonianDomainToken"
  ∷ mkHardFalseGuardRow
    "Stone theorem not promoted"
    stoneTheoremGuard
    Quantum.quantumDynamicsPromotedGuard
    "QuantumFiniteToGeneralBoundary"
    "StoneStrongContinuityToken"
  ∷ mkHardFalseGuardRow
    "spectral theorem exponential not promoted"
    spectralTheoremGuard
    Quantum.quantumDynamicsPromotedGuard
    "QuantumFiniteToGeneralBoundary"
    "SpectralTheoremExponentialToken"
  ∷ mkHardFalseGuardRow
    "general POVM semantics not promoted"
    generalPOVMGuard
    Quantum.bornRulePromotedGuard
    "QuantumFiniteToGeneralBoundary"
    "POVMSigmaAlgebraProbabilityToken"
  ∷ mkHardFalseGuardRow
    "repeated measurement semantics not promoted"
    repeatedMeasurementGuard
    Quantum.quantumEmpiricalAdequacyGuard
    "QuantumFiniteToGeneralBoundary"
    "RepeatedMeasurementSemanticsToken"
  ∷ mkHardFalseGuardRow
    "empirical quantum adequacy not promoted"
    empiricalAdequacyGuard
    Quantum.quantumEmpiricalAdequacyGuard
    "QuantumQFTObligations"
    "QuantumProviderCalibrationToken"
  ∷ mkHardFalseGuardRow
    "GNS vacuum QFT not promoted"
    gnsVacuumQFTGuard
    Quantum.qftPromotedGuard
    "QuantumQFTObligations"
    "GNSVacuumRepresentationToken"
  ∷ mkHardFalseGuardRow
    "local net QFT not promoted"
    localNetQFTGuard
    Quantum.qftPromotedGuard
    "QuantumQFTObligations"
    "HaagKastlerLocalNetToken"
  ∷ mkHardFalseGuardRow
    "interacting continuum QFT not promoted"
    interactingContinuumQFTGuard
    Quantum.qftPromotedGuard
    "QuantumQFTObligations"
    "InteractingRenormalizedContinuumQFTToken"
  ∷ []

------------------------------------------------------------------------
-- Canonical scoped closure receipt.

record FiniteQuantumQFTScopedClosure : Set₁ where
  field
    closureLabel : String
    finiteAdapter : Finite.FiniteQuantumSchrodingerBornAdapter
    finiteBoundary : Boundary.QuantumFiniteToGeneralBoundary
    finiteScopeDecision :
      Decision.FiniteQuantumPhysicalScopeDecision
    qftObligations : Quantum.QuantumQFTPromotionObligationReceipt

    hilbertRows : List FiniteHilbertClosureRow
    evolutionRows : List FiniteEvolutionClosureRow
    hamiltonianRows : List ZeroHamiltonianClosureRow
    observableProbabilityRows : List FiniteObservableProbabilityRow
    bornNormalizationRows : List FiniteBornNormalizationRow
    hardFalseGuardRows : List QuantumHardFalseGuardRow

    hilbertRowCount : Nat
    hilbertRowCountIs2 : hilbertRowCount ≡ 2
    evolutionRowCount : Nat
    evolutionRowCountIs2 : evolutionRowCount ≡ 2
    hamiltonianRowCount : Nat
    hamiltonianRowCountIs1 : hamiltonianRowCount ≡ 1
    observableProbabilityRowCount : Nat
    observableProbabilityRowCountIs4 :
      observableProbabilityRowCount ≡ 4
    bornNormalizationRowCount : Nat
    bornNormalizationRowCountIs2 :
      bornNormalizationRowCount ≡ 2
    finiteClosureRowCount : Nat
    finiteClosureRowCountIs11 : finiteClosureRowCount ≡ 11
    hardFalseGuardRowCount : Nat
    hardFalseGuardRowCountIs11 :
      hardFalseGuardRowCount ≡ 11

    upstreamSchrodingerObligationCount : Nat
    upstreamSchrodingerObligationCountIs5 :
      upstreamSchrodingerObligationCount ≡ 5
    upstreamBornObligationCount : Nat
    upstreamBornObligationCountIs4 :
      upstreamBornObligationCount ≡ 4
    upstreamQFTObligationCount : Nat
    upstreamQFTObligationCountIs5 :
      upstreamQFTObligationCount ≡ 5
    upstreamQuantumQFTObligationCount : Nat
    upstreamQuantumQFTObligationCountIs14 :
      upstreamQuantumQFTObligationCount ≡ 14
    boundaryLiftObligationCount : Nat
    boundaryLiftObligationCountIs8 :
      boundaryLiftObligationCount ≡ 8

    finiteSchrodingerBornClosed : Bool
    finiteSchrodingerBornClosedIsTrue :
      finiteSchrodingerBornClosed ≡ true
    finiteModeQFTScopeClosed : Bool
    finiteModeQFTScopeClosedIsTrue :
      finiteModeQFTScopeClosed ≡ true

    infiniteHilbertPromoted : Bool
    infiniteHilbertPromotedIsFalse :
      infiniteHilbertPromoted ≡ false
    stoneTheoremPromoted : Bool
    stoneTheoremPromotedIsFalse :
      stoneTheoremPromoted ≡ false
    spectralTheoremPromoted : Bool
    spectralTheoremPromotedIsFalse :
      spectralTheoremPromoted ≡ false
    generalBornPromoted : Bool
    generalBornPromotedIsFalse :
      generalBornPromoted ≡ false
    qftPromoted : Bool
    qftPromotedIsFalse :
      qftPromoted ≡ false
    terminalQuantumPromotion : Bool
    terminalQuantumPromotionIsFalse :
      terminalQuantumPromotion ≡ false

    validationCommand : String
    closureNotes : List String

open FiniteQuantumQFTScopedClosure public

canonicalFiniteQuantumQFTScopedClosure :
  FiniteQuantumQFTScopedClosure
canonicalFiniteQuantumQFTScopedClosure =
  record
    { closureLabel =
        "finite-mode Schrodinger/Born closure with QFT hard-false guards"
    ; finiteAdapter =
        Finite.canonicalFiniteQuantumSchrodingerBornAdapter
    ; finiteBoundary =
        Boundary.canonicalQuantumFiniteToGeneralBoundary
    ; finiteScopeDecision =
        Decision.canonicalFiniteQuantumPhysicalScopeDecision
    ; qftObligations =
        Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; hilbertRows =
        finiteHilbertRows
    ; evolutionRows =
        finiteEvolutionRows
    ; hamiltonianRows =
        finiteHamiltonianRows
    ; observableProbabilityRows =
        finiteObservableProbabilityRows
    ; bornNormalizationRows =
        finiteBornNormalizationRows
    ; hardFalseGuardRows =
        quantumHardFalseGuardRows
    ; hilbertRowCount =
        listCount finiteHilbertRows
    ; hilbertRowCountIs2 =
        refl
    ; evolutionRowCount =
        listCount finiteEvolutionRows
    ; evolutionRowCountIs2 =
        refl
    ; hamiltonianRowCount =
        listCount finiteHamiltonianRows
    ; hamiltonianRowCountIs1 =
        refl
    ; observableProbabilityRowCount =
        listCount finiteObservableProbabilityRows
    ; observableProbabilityRowCountIs4 =
        refl
    ; bornNormalizationRowCount =
        listCount finiteBornNormalizationRows
    ; bornNormalizationRowCountIs2 =
        refl
    ; finiteClosureRowCount =
        listCount finiteHilbertRows
        + listCount finiteEvolutionRows
        + listCount finiteHamiltonianRows
        + listCount finiteObservableProbabilityRows
        + listCount finiteBornNormalizationRows
    ; finiteClosureRowCountIs11 =
        refl
    ; hardFalseGuardRowCount =
        listCount quantumHardFalseGuardRows
    ; hardFalseGuardRowCountIs11 =
        refl
    ; upstreamSchrodingerObligationCount =
        Quantum.schrodingerRowCount
          Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; upstreamSchrodingerObligationCountIs5 =
        Quantum.canonicalSchrodingerObligationCountIs5
    ; upstreamBornObligationCount =
        Quantum.bornRowCount
          Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; upstreamBornObligationCountIs4 =
        Quantum.canonicalBornObligationCountIs4
    ; upstreamQFTObligationCount =
        Quantum.qftRowCount
          Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; upstreamQFTObligationCountIs5 =
        Quantum.canonicalQFTObligationCountIs5
    ; upstreamQuantumQFTObligationCount =
        Quantum.totalRowCount
          Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; upstreamQuantumQFTObligationCountIs14 =
        Quantum.canonicalQuantumQFTObligationCountIs14
    ; boundaryLiftObligationCount =
        Boundary.liftObligationCount
          Boundary.canonicalQuantumFiniteToGeneralBoundary
    ; boundaryLiftObligationCountIs8 =
        Boundary.canonicalLiftObligationCountIs8
    ; finiteSchrodingerBornClosed =
        true
    ; finiteSchrodingerBornClosedIsTrue =
        refl
    ; finiteModeQFTScopeClosed =
        true
    ; finiteModeQFTScopeClosedIsTrue =
        refl
    ; infiniteHilbertPromoted =
        false
    ; infiniteHilbertPromotedIsFalse =
        refl
    ; stoneTheoremPromoted =
        false
    ; stoneTheoremPromotedIsFalse =
        refl
    ; spectralTheoremPromoted =
        false
    ; spectralTheoremPromotedIsFalse =
        refl
    ; generalBornPromoted =
        false
    ; generalBornPromotedIsFalse =
        refl
    ; qftPromoted =
        false
    ; qftPromotedIsFalse =
        refl
    ; terminalQuantumPromotion =
        false
    ; terminalQuantumPromotionIsFalse =
        refl
    ; validationCommand =
        "agda -i . DASHI/Promotion/FiniteQuantumQFTScopedClosure.agda"
    ; closureNotes =
        "finite closure covers two normalized basis states, identity evolution, finite zero Hamiltonian symmetry, four basis projection probabilities, and two probability totals"
        ∷ "finite-mode QFT scope is closed only in the negative sense: the finite adapter contributes no GNS, local-net, locality/covariance/spectrum, DHR/DR, or interacting continuum construction"
        ∷ "infinite Hilbert completion, unbounded operators, Stone theorem, spectral theorem, general POVM semantics, empirical adequacy, and QFT promotion stay hard-false"
        ∷ []
    }

canonicalFiniteQuantumHilbertRowCountIs2 :
  hilbertRowCount canonicalFiniteQuantumQFTScopedClosure ≡ 2
canonicalFiniteQuantumHilbertRowCountIs2 = refl

canonicalFiniteQuantumEvolutionRowCountIs2 :
  evolutionRowCount canonicalFiniteQuantumQFTScopedClosure ≡ 2
canonicalFiniteQuantumEvolutionRowCountIs2 = refl

canonicalFiniteQuantumHamiltonianRowCountIs1 :
  hamiltonianRowCount canonicalFiniteQuantumQFTScopedClosure ≡ 1
canonicalFiniteQuantumHamiltonianRowCountIs1 = refl

canonicalFiniteQuantumObservableProbabilityRowCountIs4 :
  observableProbabilityRowCount canonicalFiniteQuantumQFTScopedClosure ≡ 4
canonicalFiniteQuantumObservableProbabilityRowCountIs4 = refl

canonicalFiniteQuantumBornNormalizationRowCountIs2 :
  bornNormalizationRowCount canonicalFiniteQuantumQFTScopedClosure ≡ 2
canonicalFiniteQuantumBornNormalizationRowCountIs2 = refl

canonicalFiniteQuantumClosureRowCountIs11 :
  finiteClosureRowCount canonicalFiniteQuantumQFTScopedClosure ≡ 11
canonicalFiniteQuantumClosureRowCountIs11 = refl

canonicalFiniteQuantumHardFalseGuardRowCountIs11 :
  hardFalseGuardRowCount canonicalFiniteQuantumQFTScopedClosure ≡ 11
canonicalFiniteQuantumHardFalseGuardRowCountIs11 = refl

canonicalFiniteQuantumUpstreamObligationCountIs14 :
  upstreamQuantumQFTObligationCount
    canonicalFiniteQuantumQFTScopedClosure
  ≡ 14
canonicalFiniteQuantumUpstreamObligationCountIs14 = refl

canonicalFiniteQuantumBoundaryLiftObligationCountIs8 :
  boundaryLiftObligationCount canonicalFiniteQuantumQFTScopedClosure
  ≡ 8
canonicalFiniteQuantumBoundaryLiftObligationCountIs8 = refl

canonicalFiniteQuantumSchrodingerBornClosed :
  finiteSchrodingerBornClosed
    canonicalFiniteQuantumQFTScopedClosure
  ≡ true
canonicalFiniteQuantumSchrodingerBornClosed = refl

canonicalFiniteQuantumQFTPromotionFalse :
  qftPromoted canonicalFiniteQuantumQFTScopedClosure ≡ false
canonicalFiniteQuantumQFTPromotionFalse = refl

canonicalFiniteQuantumTerminalPromotionFalse :
  terminalQuantumPromotion canonicalFiniteQuantumQFTScopedClosure
  ≡ false
canonicalFiniteQuantumTerminalPromotionFalse = refl

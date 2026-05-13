module DASHI.Physics.Closure.G3WaveFunctionOperatorAlgebra where

open import Agda.Primitive using (Set; Setω; lzero; lsuc)
open import Agda.Builtin.Nat using (Nat; _+_) renaming (zero to natZero; suc to natSuc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

import DASHI.Algebra.CCR as CCR
open import DASHI.Core.Q using (ℚ; _+ℚ_; _-ℚ_; _*ℚ_; 0ℚ; 1ℚ)
import DASHI.Geometry.EnergyAdditivityProof as Energy
import DASHI.Geometry.ScalarLawsQ as ScalarQ
import DASHI.Physics.Closure.G3ConcreteOperators as G3Concrete
import DASHI.Physics.Closure.G3ContractionCarrier as G3Contraction
open import Data.Rational.Solver using (module +-*-Solver)
import Data.Rational.Properties as Rₚ

open +-*-Solver

------------------------------------------------------------------------
-- Selected G3 wave-function/operator algebra.
--
-- This module is intentionally a bridge, not a promotion theorem.  It
-- fixes the concrete selected state carrier, uses the repo's canonical ℚ
-- scalar field/laws, defines pointwise wave-function operations, lifts the
-- selected p2/spatial state endomorphisms to wave-function operators, and
-- exposes the CCR commutator over wave-function subtraction.

data G3WaveFunctionOperatorAlgebraStatus : Set where
  selectedWaveFunctionOperatorAlgebraNoContractionPromotion :
    G3WaveFunctionOperatorAlgebraStatus

data G3WaveFunctionOperatorAlgebraGap : Set where
  missingWaveFunctionModuleLaws :
    G3WaveFunctionOperatorAlgebraGap

  missingOperatorLinearityProofs :
    G3WaveFunctionOperatorAlgebraGap

  missingCommutatorLieLaws :
    G3WaveFunctionOperatorAlgebraGap

  missingFilteredBracketCompatibility :
    G3WaveFunctionOperatorAlgebraGap

  missingAssociatedGradedGalileiIdentification :
    G3WaveFunctionOperatorAlgebraGap

  missingContractionParameterLaw :
    G3WaveFunctionOperatorAlgebraGap

  missingSchrodingerPoincareToGalileiContractionCarrier :
    G3WaveFunctionOperatorAlgebraGap

SelectedG3State :
  Set
SelectedG3State =
  G3Concrete.SelectedG3State

WaveFunction :
  Set
WaveFunction =
  SelectedG3State → ℚ

WaveFunctionOperator :
  Set
WaveFunctionOperator =
  WaveFunction → WaveFunction

_+ψ_ :
  WaveFunction →
  WaveFunction →
  WaveFunction
(ψ +ψ φ) v =
  ψ v +ℚ φ v

_-ψ_ :
  WaveFunction →
  WaveFunction →
  WaveFunction
(ψ -ψ φ) v =
  ψ v -ℚ φ v

_*ψ_ :
  WaveFunction →
  WaveFunction →
  WaveFunction
(ψ *ψ φ) v =
  ψ v *ℚ φ v

zeroψ :
  WaveFunction
zeroψ v =
  0ℚ

oneψ :
  WaveFunction
oneψ v =
  1ℚ

scaleψ :
  ℚ →
  WaveFunction →
  WaveFunction
scaleψ a ψ v =
  a *ℚ ψ v

------------------------------------------------------------------------
-- Pointwise wave-function laws.
--
-- These are intentionally pointwise: the module does not assume function
-- extensionality, so no whole-function equalities are claimed.

+ψ-assoc-pointwise :
  (ψ φ χ : WaveFunction) →
  (v : SelectedG3State) →
  ((ψ +ψ φ) +ψ χ) v ≡ (ψ +ψ (φ +ψ χ)) v
+ψ-assoc-pointwise ψ φ χ v =
  Rₚ.+-assoc (ψ v) (φ v) (χ v)

+ψ-comm-pointwise :
  (ψ φ : WaveFunction) →
  (v : SelectedG3State) →
  (ψ +ψ φ) v ≡ (φ +ψ ψ) v
+ψ-comm-pointwise ψ φ v =
  Rₚ.+-comm (ψ v) (φ v)

+ψ-identityˡ-pointwise :
  (ψ : WaveFunction) →
  (v : SelectedG3State) →
  (zeroψ +ψ ψ) v ≡ ψ v
+ψ-identityˡ-pointwise ψ v =
  Rₚ.+-identityˡ (ψ v)

+ψ-identityʳ-pointwise :
  (ψ : WaveFunction) →
  (v : SelectedG3State) →
  (ψ +ψ zeroψ) v ≡ ψ v
+ψ-identityʳ-pointwise ψ v =
  Rₚ.+-identityʳ (ψ v)

scaleψ-distrib-+ψ-pointwise :
  (a : ℚ) →
  (ψ φ : WaveFunction) →
  (v : SelectedG3State) →
  scaleψ a (ψ +ψ φ) v ≡ (scaleψ a ψ +ψ scaleψ a φ) v
scaleψ-distrib-+ψ-pointwise a ψ φ v =
  Rₚ.*-distribˡ-+ a (ψ v) (φ v)

scaleψ-assoc-pointwise :
  (a b : ℚ) →
  (ψ : WaveFunction) →
  (v : SelectedG3State) →
  scaleψ a (scaleψ b ψ) v ≡ scaleψ (a *ℚ b) ψ v
scaleψ-assoc-pointwise a b ψ v =
  sym (Rₚ.*-assoc a b (ψ v))

scaleψ-identity-pointwise :
  (ψ : WaveFunction) →
  (v : SelectedG3State) →
  scaleψ 1ℚ ψ v ≡ ψ v
scaleψ-identity-pointwise ψ v =
  Rₚ.*-identityˡ (ψ v)

-ψ-self-zero-pointwise :
  (ψ : WaveFunction) →
  (v : SelectedG3State) →
  (ψ -ψ ψ) v ≡ 0ℚ
-ψ-self-zero-pointwise ψ v =
  Rₚ.+-inverseʳ (ψ v)

record G3WaveFunctionPointwiseModuleLaws : Setω where
  field
    +ψ-assoc :
      (ψ φ χ : WaveFunction) →
      (v : SelectedG3State) →
      ((ψ +ψ φ) +ψ χ) v ≡ (ψ +ψ (φ +ψ χ)) v

    +ψ-comm :
      (ψ φ : WaveFunction) →
      (v : SelectedG3State) →
      (ψ +ψ φ) v ≡ (φ +ψ ψ) v

    +ψ-identityˡ :
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      (zeroψ +ψ ψ) v ≡ ψ v

    +ψ-identityʳ :
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      (ψ +ψ zeroψ) v ≡ ψ v

    scaleψ-distrib-+ψ :
      (a : ℚ) →
      (ψ φ : WaveFunction) →
      (v : SelectedG3State) →
      scaleψ a (ψ +ψ φ) v ≡ (scaleψ a ψ +ψ scaleψ a φ) v

    scaleψ-assoc :
      (a b : ℚ) →
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      scaleψ a (scaleψ b ψ) v ≡ scaleψ (a *ℚ b) ψ v

    scaleψ-identity :
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      scaleψ 1ℚ ψ v ≡ ψ v

    -ψ-self-zero :
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      (ψ -ψ ψ) v ≡ 0ℚ

canonicalG3WaveFunctionPointwiseModuleLaws :
  G3WaveFunctionPointwiseModuleLaws
canonicalG3WaveFunctionPointwiseModuleLaws =
  record
    { +ψ-assoc =
        +ψ-assoc-pointwise
    ; +ψ-comm =
        +ψ-comm-pointwise
    ; +ψ-identityˡ =
        +ψ-identityˡ-pointwise
    ; +ψ-identityʳ =
        +ψ-identityʳ-pointwise
    ; scaleψ-distrib-+ψ =
        scaleψ-distrib-+ψ-pointwise
    ; scaleψ-assoc =
        scaleψ-assoc-pointwise
    ; scaleψ-identity =
        scaleψ-identity-pointwise
    ; -ψ-self-zero =
        -ψ-self-zero-pointwise
    }

stateOperatorToWaveFunctionOperator :
  G3Concrete.SelectedG3Operator →
  WaveFunctionOperator
stateOperatorToWaveFunctionOperator T ψ v =
  ψ (T v)

selectedPψ :
  G3Concrete.G3SpatialDirection →
  WaveFunctionOperator
selectedPψ d =
  stateOperatorToWaveFunctionOperator (G3Concrete.selectedP d)

selectedHψ :
  WaveFunctionOperator
selectedHψ =
  stateOperatorToWaveFunctionOperator G3Concrete.selectedH

selectedKψ :
  G3Concrete.G3SpatialDirection →
  WaveFunctionOperator
selectedKψ d =
  stateOperatorToWaveFunctionOperator (G3Concrete.selectedK d)

record WaveFunctionOperatorPointwiseLinearity
  (A : WaveFunctionOperator) : Setω where
  field
    preserves-+ψ :
      (ψ φ : WaveFunction) →
      (v : SelectedG3State) →
      A (ψ +ψ φ) v ≡ (A ψ +ψ A φ) v

    preserves-scaleψ :
      (a : ℚ) →
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      A (scaleψ a ψ) v ≡ scaleψ a (A ψ) v

    preserves--ψ :
      (ψ φ : WaveFunction) →
      (v : SelectedG3State) →
      A (ψ -ψ φ) v ≡ (A ψ -ψ A φ) v

stateOperatorToWaveFunctionOperatorPointwiseLinearity :
  (T : G3Concrete.SelectedG3Operator) →
  WaveFunctionOperatorPointwiseLinearity
    (stateOperatorToWaveFunctionOperator T)
stateOperatorToWaveFunctionOperatorPointwiseLinearity T =
  record
    { preserves-+ψ =
        λ ψ φ v → refl
    ; preserves-scaleψ =
        λ a ψ v → refl
    ; preserves--ψ =
        λ ψ φ v → refl
    }

selectedPψPointwiseLinearity :
  (d : G3Concrete.G3SpatialDirection) →
  WaveFunctionOperatorPointwiseLinearity (selectedPψ d)
selectedPψPointwiseLinearity d =
  stateOperatorToWaveFunctionOperatorPointwiseLinearity
    (G3Concrete.selectedP d)

selectedHψPointwiseLinearity :
  WaveFunctionOperatorPointwiseLinearity selectedHψ
selectedHψPointwiseLinearity =
  stateOperatorToWaveFunctionOperatorPointwiseLinearity
    G3Concrete.selectedH

selectedKψPointwiseLinearity :
  (d : G3Concrete.G3SpatialDirection) →
  WaveFunctionOperatorPointwiseLinearity (selectedKψ d)
selectedKψPointwiseLinearity d =
  stateOperatorToWaveFunctionOperatorPointwiseLinearity
    (G3Concrete.selectedK d)

operatorCompose :
  WaveFunctionOperator →
  WaveFunctionOperator →
  WaveFunctionOperator
operatorCompose A B ψ =
  A (B ψ)

waveFunctionOperatorSubtraction :
  WaveFunctionOperator →
  WaveFunctionOperator →
  WaveFunctionOperator
waveFunctionOperatorSubtraction A B ψ =
  A ψ -ψ B ψ

operatorCommutator :
  WaveFunctionOperator →
  WaveFunctionOperator →
  WaveFunctionOperator
operatorCommutator A B =
  waveFunctionOperatorSubtraction
    (operatorCompose A B)
    (operatorCompose B A)

operatorCommutatorAntisymPointwise :
  (A B : WaveFunctionOperator) →
  (ψ : WaveFunction) →
  (v : SelectedG3State) →
  operatorCommutator A B ψ v
  ≡
  (0ℚ -ℚ operatorCommutator B A ψ v)
operatorCommutatorAntisymPointwise A B ψ v =
  solve 2
    (λ x y → x :- y := con 0ℚ :- (y :- x))
    refl
    (A (B ψ) v)
    (B (A ψ) v)

operatorCommutatorJacobiPointwise :
  (A B C : WaveFunctionOperator) →
  WaveFunctionOperatorPointwiseLinearity A →
  WaveFunctionOperatorPointwiseLinearity B →
  WaveFunctionOperatorPointwiseLinearity C →
  (ψ : WaveFunction) →
  (v : SelectedG3State) →
  ( operatorCommutator A (operatorCommutator B C) ψ
    +ψ
    ( operatorCommutator B (operatorCommutator C A) ψ
      +ψ
      operatorCommutator C (operatorCommutator A B) ψ
    )
  ) v
  ≡
  0ℚ
operatorCommutatorJacobiPointwise A B C linA linB linC ψ v
  rewrite
    WaveFunctionOperatorPointwiseLinearity.preserves--ψ
      linA (operatorCompose B C ψ) (operatorCompose C B ψ) v
  | WaveFunctionOperatorPointwiseLinearity.preserves--ψ
      linB (operatorCompose C A ψ) (operatorCompose A C ψ) v
  | WaveFunctionOperatorPointwiseLinearity.preserves--ψ
      linC (operatorCompose A B ψ) (operatorCompose B A ψ) v =
  solve 6
    (λ a b c d e f →
      (((a :- b) :- (c :- f)) :+
       (((c :- d) :- (e :- b)) :+
        ((e :- f) :- (a :- d))))
      :=
      con 0ℚ)
    refl
    (A (B (C ψ)) v)
    (A (C (B ψ)) v)
    (B (C (A ψ)) v)
    (B (A (C ψ)) v)
    (C (A (B ψ)) v)
    (C (B (A ψ)) v)

record G3CommutatorPointwiseLieLaws : Setω where
  field
    bracket :
      WaveFunctionOperator →
      WaveFunctionOperator →
      WaveFunctionOperator

    bracketIsOperatorCommutator :
      bracket ≡ operatorCommutator

    antisym :
      (A B : WaveFunctionOperator) →
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      bracket A B ψ v
      ≡
      (0ℚ -ℚ bracket B A ψ v)

    jacobiForPointwiseLinearOperators :
      (A B C : WaveFunctionOperator) →
      WaveFunctionOperatorPointwiseLinearity A →
      WaveFunctionOperatorPointwiseLinearity B →
      WaveFunctionOperatorPointwiseLinearity C →
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      ( bracket A (bracket B C) ψ
        +ψ
        ( bracket B (bracket C A) ψ
          +ψ
          bracket C (bracket A B) ψ
        )
      ) v
      ≡
      0ℚ

canonicalG3CommutatorPointwiseLieLaws :
  G3CommutatorPointwiseLieLaws
canonicalG3CommutatorPointwiseLieLaws =
  record
    { bracket =
        operatorCommutator
    ; bracketIsOperatorCommutator =
        refl
    ; antisym =
        operatorCommutatorAntisymPointwise
    ; jacobiForPointwiseLinearOperators =
        operatorCommutatorJacobiPointwise
    }

CCRWaveFunctionOperator :
  Set (lsuc lzero)
CCRWaveFunctionOperator =
  CCR.Op WaveFunction lzero

toCCRWaveFunctionOperator :
  WaveFunctionOperator →
  CCRWaveFunctionOperator
toCCRWaveFunctionOperator A =
  record { apply = A }

fromCCRWaveFunctionOperator :
  CCRWaveFunctionOperator →
  WaveFunctionOperator
fromCCRWaveFunctionOperator A =
  CCR.Op.apply A

waveFunctionCommutator :
  CCRWaveFunctionOperator →
  CCRWaveFunctionOperator →
  CCRWaveFunctionOperator
waveFunctionCommutator =
  CCR._commutator_ _-ψ_

selectedPψCCR :
  G3Concrete.G3SpatialDirection →
  CCRWaveFunctionOperator
selectedPψCCR d =
  toCCRWaveFunctionOperator (selectedPψ d)

selectedHψCCR :
  CCRWaveFunctionOperator
selectedHψCCR =
  toCCRWaveFunctionOperator selectedHψ

selectedKψCCR :
  G3Concrete.G3SpatialDirection →
  CCRWaveFunctionOperator
selectedKψCCR d =
  toCCRWaveFunctionOperator (selectedKψ d)

selectedPψHψCommutator :
  G3Concrete.G3SpatialDirection →
  CCRWaveFunctionOperator
selectedPψHψCommutator d =
  waveFunctionCommutator (selectedPψCCR d) selectedHψCCR

selectedPψPψCommutesPointwise :
  (d e : G3Concrete.G3SpatialDirection) →
  (ψ : WaveFunction) →
  (v : SelectedG3State) →
  selectedPψ d (selectedPψ e ψ) v
    ≡
  selectedPψ e (selectedPψ d ψ) v
selectedPψPψCommutesPointwise d e ψ v =
  cong ψ (G3Concrete.selectedPPCommutes e d v)

selectedHψPψCommutesPointwise :
  (d : G3Concrete.G3SpatialDirection) →
  (ψ : WaveFunction) →
  (v : SelectedG3State) →
  selectedHψ (selectedPψ d ψ) v
    ≡
  selectedPψ d (selectedHψ ψ) v
selectedHψPψCommutesPointwise d ψ v =
  cong ψ (sym (G3Concrete.selectedHPCommutes d v))

selectedPψHψCommutatorZeroPointwise :
  (d : G3Concrete.G3SpatialDirection) →
  (ψ : WaveFunction) →
  (v : SelectedG3State) →
  CCR.Op.apply (selectedPψHψCommutator d) ψ v ≡ 0ℚ
selectedPψHψCommutatorZeroPointwise d ψ v
  rewrite G3Concrete.selectedHPCommutes d v =
  Rₚ.+-inverseʳ
    (ψ (G3Concrete.selectedP d (G3Concrete.selectedH v)))

record G3SelectedCommutatorPointwiseLaws : Setω where
  field
    selectedPψPψCommutes :
      (d e : G3Concrete.G3SpatialDirection) →
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      selectedPψ d (selectedPψ e ψ) v
        ≡
      selectedPψ e (selectedPψ d ψ) v

    selectedHψPψCommutes :
      (d : G3Concrete.G3SpatialDirection) →
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      selectedHψ (selectedPψ d ψ) v
        ≡
      selectedPψ d (selectedHψ ψ) v

    selectedPψHψCommutatorZero :
      (d : G3Concrete.G3SpatialDirection) →
      (ψ : WaveFunction) →
      (v : SelectedG3State) →
      CCR.Op.apply (selectedPψHψCommutator d) ψ v ≡ 0ℚ

    commutatorPointwiseLieLaws :
      G3CommutatorPointwiseLieLaws

    remainingLieLawGaps :
      List G3WaveFunctionOperatorAlgebraGap

canonicalG3SelectedCommutatorPointwiseLaws :
  G3SelectedCommutatorPointwiseLaws
canonicalG3SelectedCommutatorPointwiseLaws =
  record
    { selectedPψPψCommutes =
        selectedPψPψCommutesPointwise
    ; selectedHψPψCommutes =
        selectedHψPψCommutesPointwise
    ; selectedPψHψCommutatorZero =
        selectedPψHψCommutatorZeroPointwise
    ; commutatorPointwiseLieLaws =
        canonicalG3CommutatorPointwiseLieLaws
    ; remainingLieLawGaps =
        []
    }

------------------------------------------------------------------------
-- Selected p2-filtered bracket compatibility.
--
-- This is the narrow filtered-bracket layer for the selected G3
-- wave-function/operator algebra.  It does not identify the associated
-- graded Galilei carrier and it does not state a contraction-parameter
-- limit.  It records the degree calculus needed by those downstream
-- obligations: selected P has p2-degree 0, selected H and K have p2-degree
-- 1, and the commutator bracket respects degree addition.

data SelectedOperatorP2Degree :
  WaveFunctionOperator →
  Nat →
  Set where
  selectedIdentityDegreeZero :
    SelectedOperatorP2Degree (λ ψ → ψ) natZero

  selectedPψDegreeZero :
    (d : G3Concrete.G3SpatialDirection) →
    SelectedOperatorP2Degree (selectedPψ d) natZero

  selectedHψDegreeOne :
    SelectedOperatorP2Degree selectedHψ (natSuc natZero)

  selectedKψDegreeOne :
    (d : G3Concrete.G3SpatialDirection) →
    SelectedOperatorP2Degree (selectedKψ d) (natSuc natZero)

  selectedCommutatorDegree :
    {A B : WaveFunctionOperator} →
    {m n : Nat} →
    SelectedOperatorP2Degree A m →
    SelectedOperatorP2Degree B n →
    SelectedOperatorP2Degree (operatorCommutator A B) (m + n)

selectedBracketRespectsP2Degree :
  {A B : WaveFunctionOperator} →
  {m n : Nat} →
  SelectedOperatorP2Degree A m →
  SelectedOperatorP2Degree B n →
  SelectedOperatorP2Degree (operatorCommutator A B) (m + n)
selectedBracketRespectsP2Degree degA degB =
  selectedCommutatorDegree degA degB

record G3SelectedFilteredBracketCompatibility : Setω where
  field
    degree :
      WaveFunctionOperator →
      Nat →
      Set

    degreeIsSelectedP2Degree :
      degree ≡ SelectedOperatorP2Degree

    pHasDegreeZero :
      (d : G3Concrete.G3SpatialDirection) →
      degree (selectedPψ d) natZero

    hHasDegreeOne :
      degree selectedHψ (natSuc natZero)

    kHasDegreeOne :
      (d : G3Concrete.G3SpatialDirection) →
      degree (selectedKψ d) (natSuc natZero)

    bracketRespectsDegree :
      {A B : WaveFunctionOperator} →
      {m n : Nat} →
      degree A m →
      degree B n →
      degree (operatorCommutator A B) (m + n)

    exactSemanticBoundary :
      List String

canonicalG3SelectedFilteredBracketCompatibility :
  G3SelectedFilteredBracketCompatibility
canonicalG3SelectedFilteredBracketCompatibility =
  record
    { degree =
        SelectedOperatorP2Degree
    ; degreeIsSelectedP2Degree =
        refl
    ; pHasDegreeZero =
        selectedPψDegreeZero
    ; hHasDegreeOne =
        selectedHψDegreeOne
    ; kHasDegreeOne =
        selectedKψDegreeOne
    ; bracketRespectsDegree =
        selectedBracketRespectsP2Degree
    ; exactSemanticBoundary =
        "Typed filtered bracket compatibility only: selected P has p2-degree 0; selected H and K have p2-degree 1"
        ∷ "The commutator bracket is closed under p2-degree addition by selectedCommutatorDegree"
        ∷ "No associated-graded Galilei identification is claimed here"
        ∷ "No contraction-parameter or Schrodinger Poincare-to-Galilei carrier is claimed here"
        ∷ []
    }

------------------------------------------------------------------------
-- Selected associated-graded Galilei evidence.
--
-- This is the first associated-graded layer that is available from the
-- selected wave-function/operator algebra: it identifies the selected
-- Galilei generators by p2 degree and proves that the selected bracket
-- calculus sends those generators to the expected graded slots.
--
-- It deliberately does not construct the quotient carrier
-- gr(F) = ⊕ F_n / F_{n-1}, a projection into that quotient, or the
-- Schrodinger-scope SES contraction carrier.  Those are still the exact
-- first missing pieces for full G3 promotion.

data G3SelectedAssociatedGradedGenerator : Set where
  selectedSpatialMomentumGenerator :
    G3Concrete.G3SpatialDirection →
    G3SelectedAssociatedGradedGenerator

  selectedHamiltonianGenerator :
    G3SelectedAssociatedGradedGenerator

  selectedBoostGenerator :
    G3Concrete.G3SpatialDirection →
    G3SelectedAssociatedGradedGenerator

  selectedMassCentralSlot :
    G3SelectedAssociatedGradedGenerator

selectedGeneratorOperator :
  G3SelectedAssociatedGradedGenerator →
  WaveFunctionOperator
selectedGeneratorOperator (selectedSpatialMomentumGenerator d) =
  selectedPψ d
selectedGeneratorOperator selectedHamiltonianGenerator =
  selectedHψ
selectedGeneratorOperator (selectedBoostGenerator d) =
  selectedKψ d
selectedGeneratorOperator selectedMassCentralSlot =
  λ ψ → ψ

selectedGeneratorDegree :
  G3SelectedAssociatedGradedGenerator →
  Nat
selectedGeneratorDegree (selectedSpatialMomentumGenerator d) =
  natZero
selectedGeneratorDegree selectedHamiltonianGenerator =
  natSuc natZero
selectedGeneratorDegree (selectedBoostGenerator d) =
  natSuc natZero
selectedGeneratorDegree selectedMassCentralSlot =
  natZero

selectedGeneratorHasDegree :
  (g : G3SelectedAssociatedGradedGenerator) →
  SelectedOperatorP2Degree
    (selectedGeneratorOperator g)
    (selectedGeneratorDegree g)
selectedGeneratorHasDegree (selectedSpatialMomentumGenerator d) =
  selectedPψDegreeZero d
selectedGeneratorHasDegree selectedHamiltonianGenerator =
  selectedHψDegreeOne
selectedGeneratorHasDegree (selectedBoostGenerator d) =
  selectedKψDegreeOne d
selectedGeneratorHasDegree selectedMassCentralSlot =
  selectedIdentityDegreeZero

record G3SelectedAssociatedGradedGalileiEvidence : Setω where
  field
    filteredBracketCompatibility :
      G3SelectedFilteredBracketCompatibility

    generator :
      Set

    generatorIsSelected :
      generator ≡ G3SelectedAssociatedGradedGenerator

    generatorOperator :
      G3SelectedAssociatedGradedGenerator →
      WaveFunctionOperator

    generatorOperatorIsSelected :
      generatorOperator ≡ selectedGeneratorOperator

    generatorDegree :
      G3SelectedAssociatedGradedGenerator →
      Nat

    generatorDegreeIsSelected :
      generatorDegree ≡ selectedGeneratorDegree

    generatorHasDegree :
      (g : G3SelectedAssociatedGradedGenerator) →
      SelectedOperatorP2Degree
        (generatorOperator g)
        (generatorDegree g)

    ppBracketDegreeZero :
      (d e : G3Concrete.G3SpatialDirection) →
      SelectedOperatorP2Degree
        (operatorCommutator (selectedPψ d) (selectedPψ e))
        natZero

    hpBracketDegreeOne :
      (d : G3Concrete.G3SpatialDirection) →
      SelectedOperatorP2Degree
        (operatorCommutator selectedHψ (selectedPψ d))
        (natSuc natZero)

    kpBracketDegreeOne :
      (d e : G3Concrete.G3SpatialDirection) →
      SelectedOperatorP2Degree
        (operatorCommutator (selectedKψ d) (selectedPψ e))
        (natSuc natZero)

    exactFirstMissingForFullAssociatedGraded :
      List String

canonicalG3SelectedAssociatedGradedGalileiEvidence :
  G3SelectedAssociatedGradedGalileiEvidence
canonicalG3SelectedAssociatedGradedGalileiEvidence =
  record
    { filteredBracketCompatibility =
        canonicalG3SelectedFilteredBracketCompatibility
    ; generator =
        G3SelectedAssociatedGradedGenerator
    ; generatorIsSelected =
        refl
    ; generatorOperator =
        selectedGeneratorOperator
    ; generatorOperatorIsSelected =
        refl
    ; generatorDegree =
        selectedGeneratorDegree
    ; generatorDegreeIsSelected =
        refl
    ; generatorHasDegree =
        selectedGeneratorHasDegree
    ; ppBracketDegreeZero =
        λ d e →
          selectedBracketRespectsP2Degree
            (selectedPψDegreeZero d)
            (selectedPψDegreeZero e)
    ; hpBracketDegreeOne =
        λ d →
          selectedBracketRespectsP2Degree
            selectedHψDegreeOne
            (selectedPψDegreeZero d)
    ; kpBracketDegreeOne =
        λ d e →
          selectedBracketRespectsP2Degree
            (selectedKψDegreeOne d)
            (selectedPψDegreeZero e)
    ; exactFirstMissingForFullAssociatedGraded =
        "Missing quotient carrier gr(F) = direct sum F_n / F_{n-1}; this file only identifies selected generators and degree/bracket slots"
        ∷ "Missing projection/quotient map from selected wave-function operators into the associated-graded carrier"
        ∷ "Missing p2-indexed Poincare-at-p2 carrier and isomorphism required by the Schrodinger SES target"
        ∷ "Missing contraction-parameter law; no 1/c -> 0 or p2-adic limit certificate is claimed"
        ∷ []
    }

SelectedScalarField :
  Set
SelectedScalarField =
  Energy.ScalarField.Scalar ScalarQ.scalarFieldℚ

selectedScalarFieldIsQ :
  SelectedScalarField ≡ ℚ
selectedScalarFieldIsQ =
  refl

record G3WaveFunctionModuleSurface : Setω where
  field
    scalarField :
      Energy.ScalarField

    scalarFieldIsQ :
      scalarField ≡ ScalarQ.scalarFieldℚ

    scalarLaws :
      Energy.ScalarLaws scalarField

    waveFunction :
      Set

    waveFunctionIsSelectedStateToQ :
      waveFunction ≡ WaveFunction

    add :
      waveFunction →
      waveFunction →
      waveFunction

    sub :
      waveFunction →
      waveFunction →
      waveFunction

    mul :
      waveFunction →
      waveFunction →
      waveFunction

    zero :
      waveFunction

    one :
      waveFunction

    scale :
      ℚ →
      waveFunction →
      waveFunction

    pointwiseModuleLaws :
      G3WaveFunctionPointwiseModuleLaws

    remainingModuleLawGaps :
      List G3WaveFunctionOperatorAlgebraGap

canonicalG3WaveFunctionModuleSurface :
  G3WaveFunctionModuleSurface
canonicalG3WaveFunctionModuleSurface =
  record
    { scalarField =
        ScalarQ.scalarFieldℚ
    ; scalarFieldIsQ =
        refl
    ; scalarLaws =
        ScalarQ.scalarLawsℚ
    ; waveFunction =
        WaveFunction
    ; waveFunctionIsSelectedStateToQ =
        refl
    ; add =
        _+ψ_
    ; sub =
        _-ψ_
    ; mul =
        _*ψ_
    ; zero =
        zeroψ
    ; one =
        oneψ
    ; scale =
        scaleψ
    ; pointwiseModuleLaws =
        canonicalG3WaveFunctionPointwiseModuleLaws
    ; remainingModuleLawGaps =
        []
    }

record G3SelectedWaveFunctionOperatorAlgebra : Setω where
  field
    status :
      G3WaveFunctionOperatorAlgebraStatus

    selectedConcreteOperators :
      G3Concrete.G3SelectedConcreteOperatorPackage

    selectedState :
      Set

    selectedStateIsConcrete :
      selectedState ≡ G3Concrete.SelectedG3State

    waveFunctionModule :
      G3WaveFunctionModuleSurface

    waveFunctionOperator :
      Set

    waveFunctionOperatorIsEndomorphism :
      waveFunctionOperator ≡ WaveFunctionOperator

    pOperator :
      G3Concrete.G3SpatialDirection →
      waveFunctionOperator

    hOperator :
      waveFunctionOperator

    kOperator :
      G3Concrete.G3SpatialDirection →
      waveFunctionOperator

    pOperatorLinearity :
      (d : G3Concrete.G3SpatialDirection) →
      WaveFunctionOperatorPointwiseLinearity (selectedPψ d)

    hOperatorLinearity :
      WaveFunctionOperatorPointwiseLinearity selectedHψ

    kOperatorLinearity :
      (d : G3Concrete.G3SpatialDirection) →
      WaveFunctionOperatorPointwiseLinearity (selectedKψ d)

    ccrOperatorSurface :
      Set (lsuc lzero)

    ccrOperatorSurfaceIsExact :
      ccrOperatorSurface ≡ CCRWaveFunctionOperator

    ccrCommutator :
      CCRWaveFunctionOperator →
      CCRWaveFunctionOperator →
      CCRWaveFunctionOperator

    ccrCommutatorIsExact :
      ccrCommutator ≡ waveFunctionCommutator

    pHCommutator :
      G3Concrete.G3SpatialDirection →
      CCRWaveFunctionOperator

    selectedCommutatorPointwiseLaws :
      G3SelectedCommutatorPointwiseLaws

    filteredBracketCompatibility :
      G3SelectedFilteredBracketCompatibility

    associatedGradedGalileiEvidence :
      G3SelectedAssociatedGradedGalileiEvidence

    exactSchrodingerContractionCarrierTarget :
      Set

    exactSchrodingerContractionCarrierTargetIsExact :
      exactSchrodingerContractionCarrierTarget
      ≡
      G3Contraction.SchrodingerPoincareToGalileiContractionCarrier

    exactDerivedContractionTheoremTarget :
      Set

    exactDerivedContractionTheoremTargetIsExact :
      exactDerivedContractionTheoremTarget
      ≡
      G3Contraction.SchrodingerPoincareToGalileiContractionDerived

    remainingGaps :
      List G3WaveFunctionOperatorAlgebraGap

    nonPromotionBoundary :
      List String

canonicalG3SelectedWaveFunctionOperatorAlgebra :
  G3SelectedWaveFunctionOperatorAlgebra
canonicalG3SelectedWaveFunctionOperatorAlgebra =
  record
    { status =
        selectedWaveFunctionOperatorAlgebraNoContractionPromotion
    ; selectedConcreteOperators =
        G3Concrete.canonicalG3SelectedConcreteOperatorPackage
    ; selectedState =
        SelectedG3State
    ; selectedStateIsConcrete =
        refl
    ; waveFunctionModule =
        canonicalG3WaveFunctionModuleSurface
    ; waveFunctionOperator =
        WaveFunctionOperator
    ; waveFunctionOperatorIsEndomorphism =
        refl
    ; pOperator =
        selectedPψ
    ; hOperator =
        selectedHψ
    ; kOperator =
        selectedKψ
    ; pOperatorLinearity =
        selectedPψPointwiseLinearity
    ; hOperatorLinearity =
        selectedHψPointwiseLinearity
    ; kOperatorLinearity =
        selectedKψPointwiseLinearity
    ; ccrOperatorSurface =
        CCRWaveFunctionOperator
    ; ccrOperatorSurfaceIsExact =
        refl
    ; ccrCommutator =
        waveFunctionCommutator
    ; ccrCommutatorIsExact =
        refl
    ; pHCommutator =
        selectedPψHψCommutator
    ; selectedCommutatorPointwiseLaws =
        canonicalG3SelectedCommutatorPointwiseLaws
    ; filteredBracketCompatibility =
        canonicalG3SelectedFilteredBracketCompatibility
    ; associatedGradedGalileiEvidence =
        canonicalG3SelectedAssociatedGradedGalileiEvidence
    ; exactSchrodingerContractionCarrierTarget =
        G3Contraction.SchrodingerPoincareToGalileiContractionCarrier
    ; exactSchrodingerContractionCarrierTargetIsExact =
        refl
    ; exactDerivedContractionTheoremTarget =
        G3Contraction.SchrodingerPoincareToGalileiContractionDerived
    ; exactDerivedContractionTheoremTargetIsExact =
        refl
    ; remainingGaps =
        missingAssociatedGradedGalileiIdentification
        ∷ missingContractionParameterLaw
        ∷ missingSchrodingerPoincareToGalileiContractionCarrier
        ∷ []
    ; nonPromotionBoundary =
        "Concrete selected G3 wave functions are SelectedG3State -> ℚ"
        ∷ "The scalar field and scalar laws are the existing DASHI.Geometry.ScalarLawsQ witnesses"
        ∷ "P, H, and K are lifted from selected state endomorphisms by precomposition"
        ∷ "Pointwise wave-function module laws and P/H/K pointwise linearity over +ψ and scaleψ are inhabited"
        ∷ "The CCR commutator is available over pointwise wave-function subtraction"
        ∷ "Pointwise commutator antisymmetry and Jacobi for pointwise-linear wave-function operators are inhabited"
        ∷ "Selected P/H commutator vanishes pointwise from selectedHPCommutes"
        ∷ "Selected p2-filtered bracket compatibility is inhabited as a typed degree-addition surface"
        ∷ "Selected associated-graded Galilei generator evidence is inhabited, but the quotient carrier gr(F), projection map, p2 Poincare isomorphism, contraction parameter law, and Schrodinger Poincare-to-Galilei carrier are not claimed"
        ∷ []
    }

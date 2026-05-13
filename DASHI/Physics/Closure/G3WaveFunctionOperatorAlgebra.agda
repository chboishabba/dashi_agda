module DASHI.Physics.Closure.G3WaveFunctionOperatorAlgebra where

open import Agda.Primitive using (Set; Setω; lzero; lsuc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

import DASHI.Algebra.CCR as CCR
open import DASHI.Core.Q using (ℚ; _+ℚ_; _-ℚ_; _*ℚ_; 0ℚ; 1ℚ)
import DASHI.Geometry.EnergyAdditivityProof as Energy
import DASHI.Geometry.ScalarLawsQ as ScalarQ
import DASHI.Physics.Closure.G3ConcreteOperators as G3Concrete
import DASHI.Physics.Closure.G3ContractionCarrier as G3Contraction
import Data.Rational.Properties as Rₚ

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
    ; remainingModuleLawGaps =
        missingWaveFunctionModuleLaws
        ∷ []
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
    ; exactSchrodingerContractionCarrierTarget =
        G3Contraction.SchrodingerPoincareToGalileiContractionCarrier
    ; exactSchrodingerContractionCarrierTargetIsExact =
        refl
    ; exactDerivedContractionTheoremTarget =
        G3Contraction.SchrodingerPoincareToGalileiContractionDerived
    ; exactDerivedContractionTheoremTargetIsExact =
        refl
    ; remainingGaps =
        missingWaveFunctionModuleLaws
        ∷ missingOperatorLinearityProofs
        ∷ missingCommutatorLieLaws
        ∷ missingFilteredBracketCompatibility
        ∷ missingAssociatedGradedGalileiIdentification
        ∷ missingContractionParameterLaw
        ∷ missingSchrodingerPoincareToGalileiContractionCarrier
        ∷ []
    ; nonPromotionBoundary =
        "Concrete selected G3 wave functions are SelectedG3State -> ℚ"
        ∷ "The scalar field and scalar laws are the existing DASHI.Geometry.ScalarLawsQ witnesses"
        ∷ "P, H, and K are lifted from selected state endomorphisms by precomposition"
        ∷ "The CCR commutator is available over pointwise wave-function subtraction"
        ∷ "No function extensionality, wave-function module laws, operator linearity, Lie laws, filtered bracket compatibility, associated graded carrier, Galilei identification, contraction parameter law, or Schrodinger Poincare-to-Galilei carrier is claimed"
        ∷ []
    }

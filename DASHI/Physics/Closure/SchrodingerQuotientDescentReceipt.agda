module DASHI.Physics.Closure.SchrodingerQuotientDescentReceipt where

open import Agda.Primitive using (Level; Setω; lzero; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Foundations.QuotientSetoidSurface as QS
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Schrödinger quotient descent receipt.
--
-- This module is an obligation surface only.  It records the shape needed
-- to descend a Schrödinger-facing wave-state norm through a quotient
-- relation.  It does not construct a self-adjoint Hamiltonian, unitary
-- evolution, Stone theorem route, spectral theorem, or Schrödinger closure.

data SchrodingerQuotientDescentStatus : Set where
  quotientDescentReceiptOnlyNoPromotion :
    SchrodingerQuotientDescentStatus

data SchrodingerQuotientDescentFirstMissingTheorem : Set where
  missingPhysicalTraversalOperation :
    SchrodingerQuotientDescentFirstMissingTheorem

  missingEvolutionRespectsKernelEquivalence :
    SchrodingerQuotientDescentFirstMissingTheorem

  missingQuotientTraversalOperation :
    SchrodingerQuotientDescentFirstMissingTheorem

  missingHamiltonianDescendsToQuotient :
    SchrodingerQuotientDescentFirstMissingTheorem

  missingSelfAdjointHamiltonianOnQuotient :
    SchrodingerQuotientDescentFirstMissingTheorem

  missingUnitaryEvolutionOnQuotient :
    SchrodingerQuotientDescentFirstMissingTheorem

  missingSchrodingerEquationOnQuotient :
    SchrodingerQuotientDescentFirstMissingTheorem

defaultSchrodingerQuotientDescentFirstMissingTheorem :
  SchrodingerQuotientDescentFirstMissingTheorem
defaultSchrodingerQuotientDescentFirstMissingTheorem =
  missingPhysicalTraversalOperation

sym≡ :
  {ℓ : Level} →
  {A : Set ℓ} →
  {x y : A} →
  x ≡ y →
  y ≡ x
sym≡ refl = refl

trans≡ :
  {ℓ : Level} →
  {A : Set ℓ} →
  {x y z : A} →
  x ≡ y →
  y ≡ z →
  x ≡ z
trans≡ refl refl = refl

cong≡ :
  {ℓa ℓb : Level} →
  {A : Set ℓa} →
  {B : Set ℓb} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong≡ f refl = refl

equalitySetoidSurface :
  {ℓ : Level} →
  Set ℓ →
  QS.SetoidSurface ℓ ℓ
equalitySetoidSurface A =
  record
    { Carrier =
        A
    ; _≈_ =
        _≡_
    ; isEquivalence =
        record
          { refl≈ =
              λ _ → refl
          ; sym≈ =
              sym≡
          ; trans≈ =
              trans≡
          }
    }

equalityUnaryOperationSurface :
  {ℓ : Level} →
  {A : Set ℓ} →
  (A → A) →
  QS.SetoidUnaryOperationSurface (equalitySetoidSurface A)
equalityUnaryOperationSurface f =
  record
    { unaryOperation =
        f
    ; unaryOperationRespects≈ =
        cong≡ f
    }

shiftPhaseWaveAdvanceEqualityTraversal :
  QS.SetoidUnaryOperationSurface
    (equalitySetoidSurface SPWSI.ShiftWavePhaseState)
shiftPhaseWaveAdvanceEqualityTraversal =
  equalityUnaryOperationSurface SPWSI.advanceWavePhaseState

record AdvanceWavePhaseKernelEqualityAdapter
  {ℓr : Level}
  : Setω where
  field
    kernelEquivalence :
      SPWSI.ShiftWavePhaseState →
      SPWSI.ShiftWavePhaseState →
      Set ℓr

    kernelEquivalenceIsEquivalence :
      QS.IsEquivalence kernelEquivalence

    kernelEquivalenceImpliesEquality :
      {ψ χ : SPWSI.ShiftWavePhaseState} →
      kernelEquivalence ψ χ →
      ψ ≡ χ

    adapterBoundary :
      List String

open AdvanceWavePhaseKernelEqualityAdapter public

advanceWavePhasePropositionalEqualityKernelAdapter :
  AdvanceWavePhaseKernelEqualityAdapter {lzero}
advanceWavePhasePropositionalEqualityKernelAdapter =
  record
    { kernelEquivalence =
        _≡_
    ; kernelEquivalenceIsEquivalence =
        record
          { refl≈ =
              λ _ → refl
          ; sym≈ =
              sym≡
          ; trans≈ =
              trans≡
          }
    ; kernelEquivalenceImpliesEquality =
        λ eq → eq
    ; adapterBoundary =
        "Concrete fallback only: the kernel relation is propositional equality on ShiftWavePhaseState"
        ∷ "This proves that advanceWavePhaseState respects equality, not a physical observational kernel"
        ∷ "No Hilbert quotient, Stone route, self-adjoint generator, or unitary evolution is promoted"
        ∷ []
    }

advanceWavePhaseKernelRespectsEquivalence :
  {ℓr : Level} →
  (adapter : AdvanceWavePhaseKernelEqualityAdapter {ℓr}) →
  {ψ χ : SPWSI.ShiftWavePhaseState} →
  AdvanceWavePhaseKernelEqualityAdapter.kernelEquivalence adapter ψ χ →
  AdvanceWavePhaseKernelEqualityAdapter.kernelEquivalence adapter
    (SPWSI.advanceWavePhaseState ψ)
    (SPWSI.advanceWavePhaseState χ)
advanceWavePhaseKernelRespectsEquivalence adapter eq
  rewrite AdvanceWavePhaseKernelEqualityAdapter.kernelEquivalenceImpliesEquality
    adapter
    eq =
  QS.IsEquivalence.refl≈
    (AdvanceWavePhaseKernelEqualityAdapter.kernelEquivalenceIsEquivalence
      adapter)
    _

advanceWavePhasePhysicalKernelSetoid :
  {ℓr : Level} →
  AdvanceWavePhaseKernelEqualityAdapter {ℓr} →
  QS.SetoidSurface lzero ℓr
advanceWavePhasePhysicalKernelSetoid adapter =
  record
    { Carrier =
        SPWSI.ShiftWavePhaseState
    ; _≈_ =
        AdvanceWavePhaseKernelEqualityAdapter.kernelEquivalence adapter
    ; isEquivalence =
        AdvanceWavePhaseKernelEqualityAdapter.kernelEquivalenceIsEquivalence
          adapter
    }

advanceWavePhasePhysicalKernelTraversal :
  {ℓr : Level} →
  (adapter : AdvanceWavePhaseKernelEqualityAdapter {ℓr}) →
  QS.SetoidUnaryOperationSurface
    (advanceWavePhasePhysicalKernelSetoid adapter)
advanceWavePhasePhysicalKernelTraversal adapter =
  record
    { unaryOperation =
        SPWSI.advanceWavePhaseState
    ; unaryOperationRespects≈ =
        advanceWavePhaseKernelRespectsEquivalence adapter
    }

advanceWavePhaseKernelSetoidFrom :
  {ℓr : Level} →
  (kernelEquivalence :
    SPWSI.ShiftWavePhaseState →
    SPWSI.ShiftWavePhaseState →
    Set ℓr) →
  QS.IsEquivalence kernelEquivalence →
  QS.SetoidSurface lzero ℓr
advanceWavePhaseKernelSetoidFrom
  kernelEquivalence
  kernelEquivalenceIsEquivalence =
  record
    { Carrier =
        SPWSI.ShiftWavePhaseState
    ; _≈_ =
        kernelEquivalence
    ; isEquivalence =
        kernelEquivalenceIsEquivalence
    }

record AdvanceWavePhasePhysicalKernelQuotientAdapter
  {ℓr ℓq : Level}
  : Setω where
  field
    kernelEquivalence :
      SPWSI.ShiftWavePhaseState →
      SPWSI.ShiftWavePhaseState →
      Set ℓr

    kernelEquivalenceIsEquivalence :
      QS.IsEquivalence kernelEquivalence

    advanceWavePhaseKernelExtensionality :
      {ψ χ : SPWSI.ShiftWavePhaseState} →
      kernelEquivalence ψ χ →
      kernelEquivalence
        (SPWSI.advanceWavePhaseState ψ)
        (SPWSI.advanceWavePhaseState χ)

    quotientSurface :
      QS.SetoidQuotientSurface
        (advanceWavePhaseKernelSetoidFrom
          kernelEquivalence
          kernelEquivalenceIsEquivalence)
        ℓq

    adapterBoundary :
      List String

open AdvanceWavePhasePhysicalKernelQuotientAdapter public

record ShiftWavePhaseObservationKernelPrimitive
  {ℓi ℓo : Level}
  : Setω where
  field
    ObservationIndex :
      Set ℓi

    ObservationValue :
      Set ℓo

    observe :
      ObservationIndex →
      SPWSI.ShiftWavePhaseState →
      ObservationValue

    pushedObservationAfterAdvance :
      ObservationIndex →
      ObservationValue →
      ObservationValue

    advanceWavePhaseObservationNaturality :
      (i : ObservationIndex) →
      (ψ : SPWSI.ShiftWavePhaseState) →
      observe i (SPWSI.advanceWavePhaseState ψ)
      ≡
      pushedObservationAfterAdvance i (observe i ψ)

    primitiveBoundary :
      List String

open ShiftWavePhaseObservationKernelPrimitive public

record ShiftWavePhaseLinearPhaseObservationKernelPrimitive
  {ℓi ℓo ℓlin ℓphase : Level}
  : Setω where
  field
    ObservationIndex :
      Set ℓi

    ObservationValue :
      Set ℓo

    observe :
      ObservationIndex →
      SPWSI.ShiftWavePhaseState →
      ObservationValue

    pushedObservationAfterAdvance :
      ObservationIndex →
      ObservationValue →
      ObservationValue

    IsLinearObservation :
      ObservationIndex →
      Set ℓlin

    IsPhaseHomogeneousObservation :
      ObservationIndex →
      Set ℓphase

    selectedObservationLinear :
      (i : ObservationIndex) →
      IsLinearObservation i

    selectedObservationPhaseHomogeneous :
      (i : ObservationIndex) →
      IsPhaseHomogeneousObservation i

    linearPhaseHomogeneousAdvanceNaturality :
      (i : ObservationIndex) →
      (ψ : SPWSI.ShiftWavePhaseState) →
      observe i (SPWSI.advanceWavePhaseState ψ)
      ≡
      pushedObservationAfterAdvance i (observe i ψ)

    primitiveBoundary :
      List String

open ShiftWavePhaseLinearPhaseObservationKernelPrimitive public

data ShiftWavePhaseSelectedObservationIndex : Set where
  selectedAmplitudeObservation :
    ShiftWavePhaseSelectedObservationIndex

  selectedPhaseObservation :
    ShiftWavePhaseSelectedObservationIndex

shiftWavePhaseSelectedObserve :
  ShiftWavePhaseSelectedObservationIndex →
  SPWSI.ShiftWavePhaseState →
  Nat
shiftWavePhaseSelectedObserve selectedAmplitudeObservation ψ =
  SPWSI.shiftPhaseWaveAmplitude ψ
shiftWavePhaseSelectedObserve selectedPhaseObservation ψ =
  SPWSI.shiftPhaseWavePhase ψ

advanceSelectedAmplitudeProxy :
  Nat →
  Nat
advanceSelectedAmplitudeProxy zero =
  suc zero
advanceSelectedAmplitudeProxy (suc zero) =
  suc (suc zero)
advanceSelectedAmplitudeProxy (suc (suc zero)) =
  suc (suc (suc zero))
advanceSelectedAmplitudeProxy (suc (suc (suc n))) =
  suc (suc (suc n))

advanceSelectedPhaseProxy :
  Nat →
  Nat
advanceSelectedPhaseProxy zero =
  zero
advanceSelectedPhaseProxy (suc n) =
  n

shiftWavePhaseSelectedPushedObservationAfterAdvance :
  ShiftWavePhaseSelectedObservationIndex →
  Nat →
  Nat
shiftWavePhaseSelectedPushedObservationAfterAdvance
  selectedAmplitudeObservation =
  advanceSelectedAmplitudeProxy
shiftWavePhaseSelectedPushedObservationAfterAdvance
  selectedPhaseObservation =
  advanceSelectedPhaseProxy

shiftWavePhaseSelectedObservationNaturality :
  (i : ShiftWavePhaseSelectedObservationIndex) →
  (ψ : SPWSI.ShiftWavePhaseState) →
  shiftWavePhaseSelectedObserve i (SPWSI.advanceWavePhaseState ψ)
  ≡
  shiftWavePhaseSelectedPushedObservationAfterAdvance
    i
    (shiftWavePhaseSelectedObserve i ψ)
shiftWavePhaseSelectedObservationNaturality
  selectedAmplitudeObservation
  ψ
  rewrite SPWSI.ShiftWavePhaseState.amplitude-agrees ψ
        | SPWSI.ShiftWavePhaseState.amplitude-agrees
            (SPWSI.advanceWavePhaseState ψ)
  with SPWSI.ShiftWavePhaseState.carrier ψ
... | SPTI.shiftStartPoint =
  refl
... | SPTI.shiftNextPoint =
  refl
... | SPTI.shiftHeldExitPoint =
  refl
shiftWavePhaseSelectedObservationNaturality
  selectedPhaseObservation
  ψ
  rewrite SPWSI.ShiftWavePhaseState.phase-agrees ψ
        | SPWSI.ShiftWavePhaseState.phase-agrees
            (SPWSI.advanceWavePhaseState ψ)
  with SPWSI.ShiftWavePhaseState.carrier ψ
... | SPTI.shiftStartPoint =
  refl
... | SPTI.shiftNextPoint =
  refl
... | SPTI.shiftHeldExitPoint =
  refl

shiftWavePhaseSelectedObservationKernelPrimitive :
  ShiftWavePhaseObservationKernelPrimitive {lzero} {lzero}
shiftWavePhaseSelectedObservationKernelPrimitive =
  record
    { ObservationIndex =
        ShiftWavePhaseSelectedObservationIndex
    ; ObservationValue =
        Nat
    ; observe =
        shiftWavePhaseSelectedObserve
    ; pushedObservationAfterAdvance =
        shiftWavePhaseSelectedPushedObservationAfterAdvance
    ; advanceWavePhaseObservationNaturality =
        shiftWavePhaseSelectedObservationNaturality
    ; primitiveBoundary =
        "Selected coordinate observations are amplitude and phase Nat proxies on ShiftWavePhaseState"
        ∷ "Their pushed observations are finite successor/saturation and predecessor tables matching advanceWavePhaseState on the inspected carrier"
        ∷ "advanceWavePhaseObservationNaturality is typechecked for these two coordinate observations by case analysis"
        ∷ "This is not a Hilbert projection family, not an inner-product observation, and not a physical observational quotient"
        ∷ []
    }

record ShiftWavePhaseScalarPhaseObservationEvidenceSurface
  (i : ShiftWavePhaseSelectedObservationIndex)
  : Set₁ where
  field
    Scalar :
      Set

    Phase :
      Set

    addState :
      SPWSI.ShiftWavePhaseState →
      SPWSI.ShiftWavePhaseState →
      SPWSI.ShiftWavePhaseState

    scaleState :
      Scalar →
      SPWSI.ShiftWavePhaseState →
      SPWSI.ShiftWavePhaseState

    phaseActState :
      Phase →
      SPWSI.ShiftWavePhaseState →
      SPWSI.ShiftWavePhaseState

    addObservation :
      Nat →
      Nat →
      Nat

    scaleObservation :
      Scalar →
      Nat →
      Nat

    phaseActObservation :
      Phase →
      Nat →
      Nat

    linear-add :
      (ψ χ : SPWSI.ShiftWavePhaseState) →
      shiftWavePhaseSelectedObserve i (addState ψ χ)
      ≡
      addObservation
        (shiftWavePhaseSelectedObserve i ψ)
        (shiftWavePhaseSelectedObserve i χ)

    linear-scale :
      (k : Scalar) →
      (ψ : SPWSI.ShiftWavePhaseState) →
      shiftWavePhaseSelectedObserve i (scaleState k ψ)
      ≡
      scaleObservation k (shiftWavePhaseSelectedObserve i ψ)

    phase-homogeneous :
      (φ : Phase) →
      (ψ : SPWSI.ShiftWavePhaseState) →
      shiftWavePhaseSelectedObserve i (phaseActState φ ψ)
      ≡
      phaseActObservation φ (shiftWavePhaseSelectedObserve i ψ)

    evidenceBoundary :
      List String

open ShiftWavePhaseScalarPhaseObservationEvidenceSurface public

shiftWavePhaseCoordinateAddState :
  SPWSI.ShiftWavePhaseState →
  SPWSI.ShiftWavePhaseState →
  SPWSI.ShiftWavePhaseState
shiftWavePhaseCoordinateAddState ψ χ =
  ψ

shiftWavePhaseCoordinateScaleState :
  ⊤ →
  SPWSI.ShiftWavePhaseState →
  SPWSI.ShiftWavePhaseState
shiftWavePhaseCoordinateScaleState tt ψ =
  ψ

shiftWavePhaseCoordinatePhaseActState :
  SPTI4.Phase4 →
  SPWSI.ShiftWavePhaseState →
  SPWSI.ShiftWavePhaseState
shiftWavePhaseCoordinatePhaseActState φ ψ =
  ψ

shiftWavePhaseCoordinateAddObservation :
  Nat →
  Nat →
  Nat
shiftWavePhaseCoordinateAddObservation x y =
  x

shiftWavePhaseCoordinateScaleObservation :
  ⊤ →
  Nat →
  Nat
shiftWavePhaseCoordinateScaleObservation tt x =
  x

shiftWavePhaseCoordinatePhaseActObservation :
  SPTI4.Phase4 →
  Nat →
  Nat
shiftWavePhaseCoordinatePhaseActObservation φ x =
  x

shiftWavePhaseSelectedScalarPhaseObservationEvidence :
  (i : ShiftWavePhaseSelectedObservationIndex) →
  ShiftWavePhaseScalarPhaseObservationEvidenceSurface i
shiftWavePhaseSelectedScalarPhaseObservationEvidence i =
  record
    { Scalar =
        ⊤
    ; Phase =
        SPTI4.Phase4
    ; addState =
        shiftWavePhaseCoordinateAddState
    ; scaleState =
        shiftWavePhaseCoordinateScaleState
    ; phaseActState =
        shiftWavePhaseCoordinatePhaseActState
    ; addObservation =
        shiftWavePhaseCoordinateAddObservation
    ; scaleObservation =
        shiftWavePhaseCoordinateScaleObservation
    ; phaseActObservation =
        shiftWavePhaseCoordinatePhaseActObservation
    ; linear-add =
        λ ψ χ → refl
    ; linear-scale =
        λ k ψ → refl
    ; phase-homogeneous =
        λ φ ψ → refl
    ; evidenceBoundary =
        "Degenerate selected-coordinate algebra only: addState is left projection, scaleState is identity over unit scalars, and phaseActState is identity over finite Phase4"
        ∷ "Observation-side operations mirror those state operations, so linear-add, linear-scale, and phase-homogeneous laws typecheck by refl"
        ∷ "This supplies a compact evidence surface for the finite selected amplitude/phase coordinate family only"
        ∷ "It is not a nontrivial vector-space structure, not a Hilbert scalar action, and not a physical U(1) phase action on ShiftWavePhaseState"
        ∷ "No self-adjoint, Stone, unitary, spectral, or Schrodinger-equation promotion follows from this evidence"
        ∷ []
    }

IsSelectedLinearObservation :
  ShiftWavePhaseSelectedObservationIndex →
  Set₁
IsSelectedLinearObservation i =
  ShiftWavePhaseScalarPhaseObservationEvidenceSurface i

IsSelectedPhaseHomogeneousObservation :
  ShiftWavePhaseSelectedObservationIndex →
  Set₁
IsSelectedPhaseHomogeneousObservation i =
  ShiftWavePhaseScalarPhaseObservationEvidenceSurface i

record ShiftWavePhaseSelectedLinearPhaseEvidenceRequest : Setω where
  field
    selectedObservationKernelPrimitive :
      ShiftWavePhaseObservationKernelPrimitive {lzero} {lzero}

    narrowedIsLinearObservation :
      ShiftWavePhaseSelectedObservationIndex →
      Set₁

    narrowedIsPhaseHomogeneousObservation :
      ShiftWavePhaseSelectedObservationIndex →
      Set₁

    selectedLinearityEvidenceConstructed :
      Bool

    selectedLinearityEvidenceConstructed-v :
      selectedLinearityEvidenceConstructed ≡ true

    selectedPhaseHomogeneityEvidenceConstructed :
      Bool

    selectedPhaseHomogeneityEvidenceConstructed-v :
      selectedPhaseHomogeneityEvidenceConstructed ≡ true

    selectedLinearPhasePrimitiveConstructed :
      Bool

    selectedLinearPhasePrimitiveConstructed-v :
      selectedLinearPhasePrimitiveConstructed ≡ true

    exactRemainingBlocker :
      List String

open ShiftWavePhaseSelectedLinearPhaseEvidenceRequest public

shiftWavePhaseSelectedLinearPhaseEvidenceRequest :
  ShiftWavePhaseSelectedLinearPhaseEvidenceRequest
shiftWavePhaseSelectedLinearPhaseEvidenceRequest =
  record
    { selectedObservationKernelPrimitive =
        shiftWavePhaseSelectedObservationKernelPrimitive
    ; narrowedIsLinearObservation =
        IsSelectedLinearObservation
    ; narrowedIsPhaseHomogeneousObservation =
        IsSelectedPhaseHomogeneousObservation
    ; selectedLinearityEvidenceConstructed =
        true
    ; selectedLinearityEvidenceConstructed-v =
        refl
    ; selectedPhaseHomogeneityEvidenceConstructed =
        true
    ; selectedPhaseHomogeneityEvidenceConstructed-v =
        refl
    ; selectedLinearPhasePrimitiveConstructed =
        true
    ; selectedLinearPhasePrimitiveConstructed-v =
        refl
    ; exactRemainingBlocker =
        "advanceWavePhaseObservationNaturality is already typechecked for the selected amplitude/phase coordinate observations"
        ∷ "ShiftWavePhaseScalarPhaseObservationEvidenceSurface is inhabited for each selected coordinate by the degenerate coordinate algebra: left-projection addState, unit-scalar identity scaleState, and identity Phase4 action"
        ∷ "This is sufficient to fill selectedObservationLinear, selectedObservationPhaseHomogeneous, and the selected linear/phase primitive without postulating laws"
        ∷ "The remaining blocker is physical strength: no inspected local ShiftWavePhaseState API supplies nontrivial additive state structure, nontrivial scalar scaling, or nontrivial phase action compatible with the coordinate observations"
        ∷ "The selected observation quotient surface is still supplied authority; this module does not construct the physical quotient"
        ∷ "The inhabited evidence is fail-closed and does not promote Hilbert, Stone, self-adjoint, unitary, or Schrodinger-equation claims"
        ∷ []
    }

shiftWavePhaseSelectedLinearPhaseObservationKernelPrimitive :
  ShiftWavePhaseLinearPhaseObservationKernelPrimitive
    {lzero}
    {lzero}
    {lsuc lzero}
    {lsuc lzero}
shiftWavePhaseSelectedLinearPhaseObservationKernelPrimitive =
  record
    { ObservationIndex =
        ShiftWavePhaseSelectedObservationIndex
    ; ObservationValue =
        Nat
    ; observe =
        shiftWavePhaseSelectedObserve
    ; pushedObservationAfterAdvance =
        shiftWavePhaseSelectedPushedObservationAfterAdvance
    ; IsLinearObservation =
        IsSelectedLinearObservation
    ; IsPhaseHomogeneousObservation =
        IsSelectedPhaseHomogeneousObservation
    ; selectedObservationLinear =
        shiftWavePhaseSelectedScalarPhaseObservationEvidence
    ; selectedObservationPhaseHomogeneous =
        shiftWavePhaseSelectedScalarPhaseObservationEvidence
    ; linearPhaseHomogeneousAdvanceNaturality =
        shiftWavePhaseSelectedObservationNaturality
    ; primitiveBoundary =
        "Selected amplitude/phase coordinate observation primitive with typed degenerate linear and phase-homogeneous evidence"
        ∷ "Linearity evidence is the ShiftWavePhaseScalarPhaseObservationEvidenceSurface inhabited by left-projection addition and identity unit scaling"
        ∷ "Phase-homogeneity evidence is the same surface with identity finite Phase4 action on ShiftWavePhaseState and Nat observations"
        ∷ "The naturality law is the already typechecked finite coordinate advance law"
        ∷ "This primitive remains below physical projection/Hilbert structure and does not promote self-adjoint evolution"
        ∷ []
    }

linearPhaseObservationKernelPrimitiveToObservationKernelPrimitive :
  {ℓi ℓo ℓlin ℓphase : Level} →
  ShiftWavePhaseLinearPhaseObservationKernelPrimitive
    {ℓi}
    {ℓo}
    {ℓlin}
    {ℓphase} →
  ShiftWavePhaseObservationKernelPrimitive {ℓi} {ℓo}
linearPhaseObservationKernelPrimitiveToObservationKernelPrimitive
  linearPhaseKernel =
  record
    { ObservationIndex =
        ShiftWavePhaseLinearPhaseObservationKernelPrimitive.ObservationIndex
          linearPhaseKernel
    ; ObservationValue =
        ShiftWavePhaseLinearPhaseObservationKernelPrimitive.ObservationValue
          linearPhaseKernel
    ; observe =
        ShiftWavePhaseLinearPhaseObservationKernelPrimitive.observe
          linearPhaseKernel
    ; pushedObservationAfterAdvance =
        ShiftWavePhaseLinearPhaseObservationKernelPrimitive.pushedObservationAfterAdvance
          linearPhaseKernel
    ; advanceWavePhaseObservationNaturality =
        ShiftWavePhaseLinearPhaseObservationKernelPrimitive.linearPhaseHomogeneousAdvanceNaturality
          linearPhaseKernel
    ; primitiveBoundary =
        "Observation primitive supplied through the linear/phase-homogeneous narrowed lane"
        ∷ "Linearity and phase-homogeneity evidence are retained on the source primitive, but this compiler consumes only the resulting naturality law"
        ∷ ShiftWavePhaseLinearPhaseObservationKernelPrimitive.primitiveBoundary
          linearPhaseKernel
    }

advanceWavePhaseObservationKernelEquivalence :
  {ℓi ℓo : Level} →
  ShiftWavePhaseObservationKernelPrimitive {ℓi} {ℓo} →
  SPWSI.ShiftWavePhaseState →
  SPWSI.ShiftWavePhaseState →
  Set (ℓi ⊔ ℓo)
advanceWavePhaseObservationKernelEquivalence obsKernel ψ χ =
  (i : ShiftWavePhaseObservationKernelPrimitive.ObservationIndex obsKernel) →
  ShiftWavePhaseObservationKernelPrimitive.observe obsKernel i ψ
  ≡
  ShiftWavePhaseObservationKernelPrimitive.observe obsKernel i χ

advanceWavePhaseObservationKernelIsEquivalence :
  {ℓi ℓo : Level} →
  (obsKernel : ShiftWavePhaseObservationKernelPrimitive {ℓi} {ℓo}) →
  QS.IsEquivalence
    (advanceWavePhaseObservationKernelEquivalence obsKernel)
advanceWavePhaseObservationKernelIsEquivalence obsKernel =
  record
    { refl≈ =
        λ ψ i → refl
    ; sym≈ =
        λ ψ≈χ i → sym≡ (ψ≈χ i)
    ; trans≈ =
        λ ψ≈χ χ≈φ i → trans≡ (ψ≈χ i) (χ≈φ i)
    }

advanceWavePhaseObservationKernelSetoid :
  {ℓi ℓo : Level} →
  ShiftWavePhaseObservationKernelPrimitive {ℓi} {ℓo} →
  QS.SetoidSurface lzero (ℓi ⊔ ℓo)
advanceWavePhaseObservationKernelSetoid obsKernel =
  record
    { Carrier =
        SPWSI.ShiftWavePhaseState
    ; _≈_ =
        advanceWavePhaseObservationKernelEquivalence obsKernel
    ; isEquivalence =
        advanceWavePhaseObservationKernelIsEquivalence obsKernel
    }

advanceWavePhaseObservationKernelExtensionality :
  {ℓi ℓo : Level} →
  (obsKernel : ShiftWavePhaseObservationKernelPrimitive {ℓi} {ℓo}) →
  {ψ χ : SPWSI.ShiftWavePhaseState} →
  advanceWavePhaseObservationKernelEquivalence obsKernel ψ χ →
  advanceWavePhaseObservationKernelEquivalence obsKernel
    (SPWSI.advanceWavePhaseState ψ)
    (SPWSI.advanceWavePhaseState χ)
advanceWavePhaseObservationKernelExtensionality obsKernel {ψ} {χ} ψ≈χ i =
  trans≡
    (ShiftWavePhaseObservationKernelPrimitive.advanceWavePhaseObservationNaturality
      obsKernel
      i
      ψ)
    (trans≡
      (cong≡
        (ShiftWavePhaseObservationKernelPrimitive.pushedObservationAfterAdvance
          obsKernel
          i)
        (ψ≈χ i))
      (sym≡
        (ShiftWavePhaseObservationKernelPrimitive.advanceWavePhaseObservationNaturality
          obsKernel
          i
          χ)))

shiftWavePhaseCanonicalSelectedObservationEquivalent :
  (ψ : SPWSI.ShiftWavePhaseState) →
  advanceWavePhaseObservationKernelEquivalence
    shiftWavePhaseSelectedObservationKernelPrimitive
    (SPWSI.canonicalWavePhaseState
      (SPWSI.ShiftWavePhaseState.carrier ψ))
    ψ
shiftWavePhaseCanonicalSelectedObservationEquivalent
  ψ
  selectedAmplitudeObservation =
  sym≡ (SPWSI.ShiftWavePhaseState.amplitude-agrees ψ)
shiftWavePhaseCanonicalSelectedObservationEquivalent
  ψ
  selectedPhaseObservation =
  sym≡ (SPWSI.ShiftWavePhaseState.phase-agrees ψ)

shiftWavePhaseSelectedHeldPotentialSound :
  {ψ χ : SPWSI.ShiftWavePhaseState} →
  advanceWavePhaseObservationKernelEquivalence
    shiftWavePhaseSelectedObservationKernelPrimitive
    ψ
    χ →
  DDSI.shiftHeldPotential (SPWSI.ShiftWavePhaseState.carrier ψ)
  ≡
  DDSI.shiftHeldPotential (SPWSI.ShiftWavePhaseState.carrier χ)
shiftWavePhaseSelectedHeldPotentialSound {ψ} {χ} ψ≈χ =
  trans≡
    (sym≡ (SPWSI.ShiftWavePhaseState.phase-agrees ψ))
    (trans≡
      (ψ≈χ selectedPhaseObservation)
      (SPWSI.ShiftWavePhaseState.phase-agrees χ))

shiftPressurePointByHeldPotential :
  (a b : SPTI.ShiftPressurePoint) →
  DDSI.shiftHeldPotential a
  ≡
  DDSI.shiftHeldPotential b →
  a ≡ b
shiftPressurePointByHeldPotential
  SPTI.shiftStartPoint
  SPTI.shiftStartPoint
  eq =
  refl
shiftPressurePointByHeldPotential
  SPTI.shiftStartPoint
  SPTI.shiftNextPoint
  ()
shiftPressurePointByHeldPotential
  SPTI.shiftStartPoint
  SPTI.shiftHeldExitPoint
  ()
shiftPressurePointByHeldPotential
  SPTI.shiftNextPoint
  SPTI.shiftStartPoint
  ()
shiftPressurePointByHeldPotential
  SPTI.shiftNextPoint
  SPTI.shiftNextPoint
  eq =
  refl
shiftPressurePointByHeldPotential
  SPTI.shiftNextPoint
  SPTI.shiftHeldExitPoint
  ()
shiftPressurePointByHeldPotential
  SPTI.shiftHeldExitPoint
  SPTI.shiftStartPoint
  ()
shiftPressurePointByHeldPotential
  SPTI.shiftHeldExitPoint
  SPTI.shiftNextPoint
  ()
shiftPressurePointByHeldPotential
  SPTI.shiftHeldExitPoint
  SPTI.shiftHeldExitPoint
  eq =
  refl

shiftWavePhaseSelectedObservationCarrierSound :
  {ψ χ : SPWSI.ShiftWavePhaseState} →
  advanceWavePhaseObservationKernelEquivalence
    shiftWavePhaseSelectedObservationKernelPrimitive
    ψ
    χ →
  SPWSI.ShiftWavePhaseState.carrier ψ
  ≡
  SPWSI.ShiftWavePhaseState.carrier χ
shiftWavePhaseSelectedObservationCarrierSound {ψ} {χ} ψ≈χ =
  shiftPressurePointByHeldPotential
    (SPWSI.ShiftWavePhaseState.carrier ψ)
    (SPWSI.ShiftWavePhaseState.carrier χ)
    (shiftWavePhaseSelectedHeldPotentialSound ψ≈χ)

shiftWavePhaseSelectedObservationQuotientElim-β :
  {ℓp : Level} →
  (P : SPTI.ShiftPressurePoint → Set ℓp) →
  (f :
    (x : SPWSI.ShiftWavePhaseState) →
    P (SPWSI.ShiftWavePhaseState.carrier x)) →
  ((x y : SPWSI.ShiftWavePhaseState) →
    (eq :
      advanceWavePhaseObservationKernelEquivalence
        shiftWavePhaseSelectedObservationKernelPrimitive
        x
        y) →
    QS.subst P (shiftWavePhaseSelectedObservationCarrierSound eq) (f x)
    ≡
    f y) →
  (ψ : SPWSI.ShiftWavePhaseState) →
  f
    (SPWSI.canonicalWavePhaseState
      (SPWSI.ShiftWavePhaseState.carrier ψ))
  ≡
  f ψ
shiftWavePhaseSelectedObservationQuotientElim-β
  P
  f
  resp
  (SPWSI.mkShiftWavePhaseState
    SPTI.shiftStartPoint
    .(DDSI.shiftPointDensity SPTI.shiftStartPoint)
    .(DDSI.shiftHeldPotential SPTI.shiftStartPoint)
    refl
    refl) =
  resp
    (SPWSI.canonicalWavePhaseState SPTI.shiftStartPoint)
    (SPWSI.canonicalWavePhaseState SPTI.shiftStartPoint)
    (shiftWavePhaseCanonicalSelectedObservationEquivalent
      (SPWSI.canonicalWavePhaseState SPTI.shiftStartPoint))
shiftWavePhaseSelectedObservationQuotientElim-β
  P
  f
  resp
  (SPWSI.mkShiftWavePhaseState
    SPTI.shiftNextPoint
    .(DDSI.shiftPointDensity SPTI.shiftNextPoint)
    .(DDSI.shiftHeldPotential SPTI.shiftNextPoint)
    refl
    refl) =
  resp
    (SPWSI.canonicalWavePhaseState SPTI.shiftNextPoint)
    (SPWSI.canonicalWavePhaseState SPTI.shiftNextPoint)
    (shiftWavePhaseCanonicalSelectedObservationEquivalent
      (SPWSI.canonicalWavePhaseState SPTI.shiftNextPoint))
shiftWavePhaseSelectedObservationQuotientElim-β
  P
  f
  resp
  (SPWSI.mkShiftWavePhaseState
    SPTI.shiftHeldExitPoint
    .(DDSI.shiftPointDensity SPTI.shiftHeldExitPoint)
    .(DDSI.shiftHeldPotential SPTI.shiftHeldExitPoint)
    refl
    refl) =
  resp
    (SPWSI.canonicalWavePhaseState SPTI.shiftHeldExitPoint)
    (SPWSI.canonicalWavePhaseState SPTI.shiftHeldExitPoint)
    (shiftWavePhaseCanonicalSelectedObservationEquivalent
      (SPWSI.canonicalWavePhaseState SPTI.shiftHeldExitPoint))

shiftWavePhaseSelectedObservationQuotientSurface :
  QS.SetoidQuotientSurface
    (advanceWavePhaseObservationKernelSetoid
      shiftWavePhaseSelectedObservationKernelPrimitive)
    lzero
shiftWavePhaseSelectedObservationQuotientSurface =
  record
    { QuotientCarrier =
        SPTI.ShiftPressurePoint
    ; quotientClass =
        SPWSI.ShiftWavePhaseState.carrier
    ; quotientSound =
        shiftWavePhaseSelectedObservationCarrierSound
    ; quotientRec =
        λ B f resp q →
          f (SPWSI.canonicalWavePhaseState q)
    ; quotientRec-β =
        λ B f resp ψ →
          resp
            (SPWSI.canonicalWavePhaseState
              (SPWSI.ShiftWavePhaseState.carrier ψ))
            ψ
            (shiftWavePhaseCanonicalSelectedObservationEquivalent ψ)
    ; quotientElim =
        λ P f resp q →
          f (SPWSI.canonicalWavePhaseState q)
    ; quotientElim-β =
      λ P f resp ψ →
          shiftWavePhaseSelectedObservationQuotientElim-β
            P
            f
            resp
            ψ
    }

record ShiftWavePhaseObservationKernelQuotientPrimitive
  {ℓi ℓo ℓq : Level}
  : Setω where
  field
    observationKernelPrimitive :
      ShiftWavePhaseObservationKernelPrimitive {ℓi} {ℓo}

    quotientSurface :
      QS.SetoidQuotientSurface
        (advanceWavePhaseObservationKernelSetoid
          observationKernelPrimitive)
        ℓq

    quotientPrimitiveBoundary :
      List String

open ShiftWavePhaseObservationKernelQuotientPrimitive public

shiftWavePhaseSelectedObservationKernelQuotientPrimitive :
  ShiftWavePhaseObservationKernelQuotientPrimitive {lzero} {lzero} {lzero}
shiftWavePhaseSelectedObservationKernelQuotientPrimitive =
  record
    { observationKernelPrimitive =
        shiftWavePhaseSelectedObservationKernelPrimitive
    ; quotientSurface =
        shiftWavePhaseSelectedObservationQuotientSurface
    ; quotientPrimitiveBoundary =
        "Finite selected coordinate quotient only: quotient carrier is ShiftPressurePoint, and quotientClass forgets to the carrier point"
        ∷ "quotientSound is proved from the selected phase observation, whose finite table separates the three local carrier points"
        ∷ "quotientRec and quotientElim choose canonicalWavePhaseState as representative for each carrier point"
        ∷ "The beta laws use selected observation equivalence between any state and its canonical representative"
        ∷ "This is not a Hilbert quotient, not a physical projection quotient, and not a self-adjoint/unitary/Schrodinger promotion"
        ∷ []
    }

advanceWavePhaseObservationKernelQuotientAdapter :
  {ℓi ℓo ℓq : Level} →
  ShiftWavePhaseObservationKernelQuotientPrimitive {ℓi} {ℓo} {ℓq} →
  AdvanceWavePhasePhysicalKernelQuotientAdapter {ℓi ⊔ ℓo} {ℓq}
advanceWavePhaseObservationKernelQuotientAdapter obsKernelQuotient =
  record
    { kernelEquivalence =
        advanceWavePhaseObservationKernelEquivalence
          (ShiftWavePhaseObservationKernelQuotientPrimitive.observationKernelPrimitive
            obsKernelQuotient)
    ; kernelEquivalenceIsEquivalence =
        advanceWavePhaseObservationKernelIsEquivalence
          (ShiftWavePhaseObservationKernelQuotientPrimitive.observationKernelPrimitive
            obsKernelQuotient)
    ; advanceWavePhaseKernelExtensionality =
        advanceWavePhaseObservationKernelExtensionality
          (ShiftWavePhaseObservationKernelQuotientPrimitive.observationKernelPrimitive
            obsKernelQuotient)
    ; quotientSurface =
        ShiftWavePhaseObservationKernelQuotientPrimitive.quotientSurface
          obsKernelQuotient
    ; adapterBoundary =
        "Physical kernel is pointwise equality over the supplied observation family"
        ∷ "advanceWavePhaseKernelExtensionality is derived from advanceWavePhaseObservationNaturality"
        ∷ "The quotient surface is still supplied authority; this module does not construct a HIT or quotient implementation"
        ∷ "This adapter does not promote Hilbert, Stone, self-adjoint, unitary, or Schrodinger closure"
        ∷ ShiftWavePhaseObservationKernelPrimitive.primitiveBoundary
          (ShiftWavePhaseObservationKernelQuotientPrimitive.observationKernelPrimitive
            obsKernelQuotient)
    }

record AdvanceWavePhaseLinearPhaseObservationNaturalityRequest : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    firstMissingPrimitiveName :
      String

    selectedProjectionFamilyConstructed :
      Bool

    selectedProjectionFamilyConstructed-v :
      selectedProjectionFamilyConstructed ≡ true

    linearObservationInterfaceConstructed :
      Bool

    linearObservationInterfaceConstructed-v :
      linearObservationInterfaceConstructed ≡ true

    phaseHomogeneousObservationInterfaceConstructed :
      Bool

    phaseHomogeneousObservationInterfaceConstructed-v :
      phaseHomogeneousObservationInterfaceConstructed ≡ true

    linearPhaseNaturalityConstructed :
      Bool

    linearPhaseNaturalityConstructed-v :
      linearPhaseNaturalityConstructed ≡ true

    selectedLinearPhaseEvidenceRequest :
      ShiftWavePhaseSelectedLinearPhaseEvidenceRequest

    requestBoundary :
      List String

open AdvanceWavePhaseLinearPhaseObservationNaturalityRequest public

advanceWavePhaseLinearPhaseObservationNaturalityRequest :
  AdvanceWavePhaseLinearPhaseObservationNaturalityRequest
advanceWavePhaseLinearPhaseObservationNaturalityRequest =
  record
    { requestedInterfaceName =
        "ShiftWavePhaseLinearPhaseObservationKernelPrimitive"
    ; exactRequiredFields =
        "ObservationIndex : Set ell-i"
        ∷ "ObservationValue : Set ell-o"
        ∷ "observe : ObservationIndex -> ShiftWavePhaseState -> ObservationValue"
        ∷ "pushedObservationAfterAdvance : ObservationIndex -> ObservationValue -> ObservationValue"
        ∷ "IsLinearObservation : ObservationIndex -> Set ell-linear"
        ∷ "IsPhaseHomogeneousObservation : ObservationIndex -> Set ell-phase"
        ∷ "selectedObservationLinear : (i : ObservationIndex) -> IsLinearObservation i"
        ∷ "selectedObservationPhaseHomogeneous : (i : ObservationIndex) -> IsPhaseHomogeneousObservation i"
        ∷ "linearPhaseHomogeneousAdvanceNaturality : observe i (advanceWavePhaseState psi) == pushedObservationAfterAdvance i (observe i psi)"
        ∷ []
    ; firstMissingPrimitiveName =
        "Nondegenerate physical projection algebra or quotient surface for the selected observation family"
    ; selectedProjectionFamilyConstructed =
        true
    ; selectedProjectionFamilyConstructed-v =
        refl
    ; linearObservationInterfaceConstructed =
        true
    ; linearObservationInterfaceConstructed-v =
        refl
    ; phaseHomogeneousObservationInterfaceConstructed =
        true
    ; phaseHomogeneousObservationInterfaceConstructed-v =
        refl
    ; linearPhaseNaturalityConstructed =
        true
    ; linearPhaseNaturalityConstructed-v =
        refl
    ; selectedLinearPhaseEvidenceRequest =
        shiftWavePhaseSelectedLinearPhaseEvidenceRequest
    ; requestBoundary =
        "This is the narrowed Paper-3 observation lane: selected observations must carry linearity and phase-homogeneity evidence"
        ∷ "The selected amplitude/phase coordinate observations now have a typechecked observation naturality primitive"
        ∷ "A degenerate coordinate algebra now fills selectedObservationLinear and selectedObservationPhaseHomogeneous without postulates"
        ∷ "The linearPhaseHomogeneousAdvanceNaturality law is the already typechecked finite coordinate naturality law"
        ∷ "No inspected local ShiftWavePhaseState surface exposes nontrivial scalar structure, additive state structure, scale action, or phase action for a physical projection algebra"
        ∷ "The compiler back to ShiftWavePhaseObservationKernelPrimitive is available, but it does not synthesize naturality"
        ∷ []
    }

data NondegeneratePhysicalProjectionAlgebraTheoremField : Set where
  selectedCoordinateQuotientCarrierField :
    NondegeneratePhysicalProjectionAlgebraTheoremField

  physicalNondegenerateProjectionScalarLawsField :
    NondegeneratePhysicalProjectionAlgebraTheoremField

  quotientInnerProductWellDefinednessField :
    NondegeneratePhysicalProjectionAlgebraTheoremField

  globalPhysicalQuotientInnerProductWellDefinednessField :
    NondegeneratePhysicalProjectionAlgebraTheoremField

  acceptedHilbertCompletionField :
    NondegeneratePhysicalProjectionAlgebraTheoremField

canonicalNondegeneratePhysicalProjectionAlgebraTheoremFields :
  List NondegeneratePhysicalProjectionAlgebraTheoremField
canonicalNondegeneratePhysicalProjectionAlgebraTheoremFields =
  selectedCoordinateQuotientCarrierField
  ∷ physicalNondegenerateProjectionScalarLawsField
  ∷ quotientInnerProductWellDefinednessField
  ∷ globalPhysicalQuotientInnerProductWellDefinednessField
  ∷ acceptedHilbertCompletionField
  ∷ []

canonicalNondegeneratePhysicalProjectionAlgebraRemainingFieldsAfterFirstMissing :
  List NondegeneratePhysicalProjectionAlgebraTheoremField
canonicalNondegeneratePhysicalProjectionAlgebraRemainingFieldsAfterFirstMissing =
  quotientInnerProductWellDefinednessField
  ∷ globalPhysicalQuotientInnerProductWellDefinednessField
  ∷ acceptedHilbertCompletionField
  ∷ []

record NondegeneratePhysicalProjectionAlgebraRequest : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    selectedFiniteCoordinateQuotientConstructed :
      Bool

    selectedFiniteCoordinateQuotientConstructed-v :
      selectedFiniteCoordinateQuotientConstructed ≡ true

    degenerateCoordinateAlgebraConstructed :
      Bool

    degenerateCoordinateAlgebraConstructed-v :
      degenerateCoordinateAlgebraConstructed ≡ true

    nondegenerateProjectionAlgebraConstructed :
      Bool

    nondegenerateProjectionAlgebraConstructed-v :
      nondegenerateProjectionAlgebraConstructed ≡ false

    quotientInnerProductWellDefinednessConstructed :
      Bool

    quotientInnerProductWellDefinednessConstructed-v :
      quotientInnerProductWellDefinednessConstructed ≡ false

    completionConstructed :
      Bool

    completionConstructed-v :
      completionConstructed ≡ false

    requiredTheoremFields :
      List NondegeneratePhysicalProjectionAlgebraTheoremField

    requiredTheoremFieldsAreCanonical :
      requiredTheoremFields
      ≡
      canonicalNondegeneratePhysicalProjectionAlgebraTheoremFields

    firstMissingTheoremField :
      NondegeneratePhysicalProjectionAlgebraTheoremField

    firstMissingTheoremFieldIsProjectionScalarLaws :
      firstMissingTheoremField
      ≡
      physicalNondegenerateProjectionScalarLawsField

    remainingTheoremFieldsAfterFirstMissing :
      List NondegeneratePhysicalProjectionAlgebraTheoremField

    remainingTheoremFieldsAfterFirstMissingAreCanonical :
      remainingTheoremFieldsAfterFirstMissing
      ≡
      canonicalNondegeneratePhysicalProjectionAlgebraRemainingFieldsAfterFirstMissing

    firstMissingPrimitiveName :
      String

    requestBoundary :
      List String

open NondegeneratePhysicalProjectionAlgebraRequest public

nondegeneratePhysicalProjectionAlgebraRequest :
  NondegeneratePhysicalProjectionAlgebraRequest
nondegeneratePhysicalProjectionAlgebraRequest =
  record
    { requestedInterfaceName =
        "NondegeneratePhysicalProjectionAlgebraForShiftWavePhaseQuotient"
    ; exactRequiredFields =
        "ProjectionIndex : Set ell-i"
        ∷ "ProjectionValue : Set ell-o"
        ∷ "project : ProjectionIndex -> ShiftWavePhaseState -> ProjectionValue"
        ∷ "kernelEquivalence : psi ~ chi iff all project i psi == project i chi"
        ∷ "kernelEquivalenceIsEquivalence : IsEquivalence kernelEquivalence"
        ∷ "advanceWavePhaseProjectionNaturality : project i (advanceWavePhaseState psi) == pushedProjectionAfterAdvance i (project i psi)"
        ∷ "addState and scaleState with nontrivial vector-space laws on the selected wave states"
        ∷ "phaseActState with nontrivial physical phase action compatible with the projections"
        ∷ "nondegenerateProjectionSeparation : projections separate the intended physical quotient without collapsing to propositional equality"
        ∷ "quotientInnerProduct : quotientCarrier -> quotientCarrier -> InnerValue"
        ∷ "quotientInnerProductWellDefined : kernel-equivalent representatives give the same inner product"
        ∷ "completion : accepted Hilbert completion or completed HilbertSpace carrier for the quotient"
        ∷ []
    ; selectedFiniteCoordinateQuotientConstructed =
        true
    ; selectedFiniteCoordinateQuotientConstructed-v =
        refl
    ; degenerateCoordinateAlgebraConstructed =
        true
    ; degenerateCoordinateAlgebraConstructed-v =
        refl
    ; nondegenerateProjectionAlgebraConstructed =
        false
    ; nondegenerateProjectionAlgebraConstructed-v =
        refl
    ; quotientInnerProductWellDefinednessConstructed =
        false
    ; quotientInnerProductWellDefinednessConstructed-v =
        refl
    ; completionConstructed =
        false
    ; completionConstructed-v =
        refl
    ; requiredTheoremFields =
        canonicalNondegeneratePhysicalProjectionAlgebraTheoremFields
    ; requiredTheoremFieldsAreCanonical =
        refl
    ; firstMissingTheoremField =
        physicalNondegenerateProjectionScalarLawsField
    ; firstMissingTheoremFieldIsProjectionScalarLaws =
        refl
    ; remainingTheoremFieldsAfterFirstMissing =
        canonicalNondegeneratePhysicalProjectionAlgebraRemainingFieldsAfterFirstMissing
    ; remainingTheoremFieldsAfterFirstMissingAreCanonical =
        refl
    ; firstMissingPrimitiveName =
        "Nondegenerate physical projection algebra plus quotient inner-product well-definedness, global physical witness, and completion"
    ; requestBoundary =
        "The finite selected coordinate quotient is inhabited with ShiftPressurePoint as quotient carrier"
        ∷ "The current linear/phase evidence is deliberately degenerate: left-projection addition, unit-scalar identity scaling, and identity finite Phase4 action"
        ∷ "That evidence is enough for selected coordinate bookkeeping but not enough for physical projection, Hilbert quotient, Stone, or Schrodinger promotion"
        ∷ "The canonical first missing theorem field is physicalNondegenerateProjectionScalarLawsField"
        ∷ "After that first field, the remaining canonical fields are quotientInnerProductWellDefinednessField, globalPhysicalQuotientInnerProductWellDefinednessField, and acceptedHilbertCompletionField"
        ∷ "A nondegenerate route must supply a projection family whose kernel is the intended physical equivalence, plus advanceWavePhaseState naturality for that family"
        ∷ "The same route must supply quotient inner-product well-definedness, a global physical witness for that well-definedness, and an accepted completion before any Hilbert carrier can be promoted"
        ∷ []
    }

record AdvanceWavePhaseObservationKernelPrimitiveRequest : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    firstMissingPrimitiveName :
      String

    linearPhaseObservationNaturalityRequest :
      AdvanceWavePhaseLinearPhaseObservationNaturalityRequest

    selectedObservationKernelQuotientPrimitive :
      ShiftWavePhaseObservationKernelQuotientPrimitive {lzero} {lzero} {lzero}

    selectedObservationKernelQuotientConstructed :
      Bool

    selectedObservationKernelQuotientConstructed-v :
      selectedObservationKernelQuotientConstructed ≡ true

    observationKernelCompilerAvailable :
      Bool

    observationKernelCompilerAvailable-v :
      observationKernelCompilerAvailable ≡ true

    physicalObservationKernelPrimitiveConstructed :
      Bool

    physicalObservationKernelPrimitiveConstructed-v :
      physicalObservationKernelPrimitiveConstructed ≡ false

    quotientSurfaceConstructed :
      Bool

    quotientSurfaceConstructed-v :
      quotientSurfaceConstructed ≡ true

    requestBoundary :
      List String

open AdvanceWavePhaseObservationKernelPrimitiveRequest public

advanceWavePhaseObservationKernelPrimitiveRequest :
  AdvanceWavePhaseObservationKernelPrimitiveRequest
advanceWavePhaseObservationKernelPrimitiveRequest =
  record
    { requestedInterfaceName =
        "ShiftWavePhaseObservationKernelQuotientPrimitive"
    ; exactRequiredFields =
        "ObservationIndex : Set ell-i"
        ∷ "ObservationValue : Set ell-o"
        ∷ "observe : ObservationIndex -> ShiftWavePhaseState -> ObservationValue"
        ∷ "pushedObservationAfterAdvance : ObservationIndex -> ObservationValue -> ObservationValue"
        ∷ "advanceWavePhaseObservationNaturality : observe i (advanceWavePhaseState psi) == pushedObservationAfterAdvance i (observe i psi)"
        ∷ "Narrowed lane: ShiftWavePhaseLinearPhaseObservationKernelPrimitive with IsLinearObservation and IsPhaseHomogeneousObservation evidence"
        ∷ "quotientSurface : SetoidQuotientSurface for pointwise equality over observe"
        ∷ []
    ; firstMissingPrimitiveName =
        "Nondegenerate physical projection algebra beyond the finite selected coordinate quotient"
    ; linearPhaseObservationNaturalityRequest =
        advanceWavePhaseLinearPhaseObservationNaturalityRequest
    ; selectedObservationKernelQuotientPrimitive =
        shiftWavePhaseSelectedObservationKernelQuotientPrimitive
    ; selectedObservationKernelQuotientConstructed =
        true
    ; selectedObservationKernelQuotientConstructed-v =
        refl
    ; observationKernelCompilerAvailable =
        true
    ; observationKernelCompilerAvailable-v =
        refl
    ; physicalObservationKernelPrimitiveConstructed =
        false
    ; physicalObservationKernelPrimitiveConstructed-v =
        refl
    ; quotientSurfaceConstructed =
        true
    ; quotientSurfaceConstructed-v =
        refl
    ; requestBoundary =
        "The compiler from observation-kernel primitives to AdvanceWavePhasePhysicalKernelQuotientAdapter is inhabited"
        ∷ "The selected coordinate observation kernel primitive is inhabited for amplitude/phase Nat proxies, including advanceWavePhaseObservationNaturality"
        ∷ "The selected linear/phase observation primitive is now inhabited by a degenerate coordinate algebra with typechecked laws"
        ∷ "A SetoidQuotientSurface for that finite selected coordinate kernel is now inhabited with ShiftPressurePoint as quotient carrier"
        ∷ "The quotient eliminators use canonicalWavePhaseState representatives, and the beta laws use selected observation equivalence to each representative"
        ∷ "NondegeneratePhysicalProjectionAlgebraRequest names the exact missing upgrade: physical projections, nondegeneracy, quotient inner-product well-definedness, and completion"
        ∷ "A selected physical kernel remains pointwise equality over supplied physical observations/projections"
        ∷ "The exact narrowed blocker is now any required upgrade from degenerate coordinate algebra to a nontrivial physical projection algebra"
        ∷ "For inner-product projections, that law should come from linearity or unitarity of advanceWavePhaseState against the selected test projections"
        ∷ "No inspected local surface exposes the projection family, scalar/phase action, advanceWavePhaseState linearity, or advanceWavePhaseState unitarity needed to instantiate that law"
        ∷ "The constructed quotient is finite-coordinate only and does not construct Hilbert, Stone, self-adjoint, unitary, or Schrodinger-equation structure"
        ∷ []
    }

advanceWavePhasePhysicalKernelQuotientSetoid :
  {ℓr ℓq : Level} →
  AdvanceWavePhasePhysicalKernelQuotientAdapter {ℓr} {ℓq} →
  QS.SetoidSurface lzero ℓr
advanceWavePhasePhysicalKernelQuotientSetoid adapter =
  advanceWavePhaseKernelSetoidFrom
    (AdvanceWavePhasePhysicalKernelQuotientAdapter.kernelEquivalence adapter)
    (AdvanceWavePhasePhysicalKernelQuotientAdapter.kernelEquivalenceIsEquivalence
      adapter)

advanceWavePhasePhysicalKernelQuotientTraversal :
  {ℓr ℓq : Level} →
  (adapter : AdvanceWavePhasePhysicalKernelQuotientAdapter {ℓr} {ℓq}) →
  QS.SetoidUnaryOperationSurface
    (advanceWavePhasePhysicalKernelQuotientSetoid adapter)
advanceWavePhasePhysicalKernelQuotientTraversal adapter =
  record
    { unaryOperation =
        SPWSI.advanceWavePhaseState
    ; unaryOperationRespects≈ =
        AdvanceWavePhasePhysicalKernelQuotientAdapter.advanceWavePhaseKernelExtensionality
          adapter
    }

advanceWavePhaseKernelEquivalenceImpliesQuotientEquality :
  {ℓr ℓq : Level} →
  (adapter : AdvanceWavePhasePhysicalKernelQuotientAdapter {ℓr} {ℓq}) →
  {ψ χ : SPWSI.ShiftWavePhaseState} →
  AdvanceWavePhasePhysicalKernelQuotientAdapter.kernelEquivalence adapter ψ χ →
  QS.quotientClass
    (AdvanceWavePhasePhysicalKernelQuotientAdapter.quotientSurface adapter)
    ψ
  ≡
  QS.quotientClass
    (AdvanceWavePhasePhysicalKernelQuotientAdapter.quotientSurface adapter)
    χ
advanceWavePhaseKernelEquivalenceImpliesQuotientEquality adapter eq =
  QS.quotientSound
    (AdvanceWavePhasePhysicalKernelQuotientAdapter.quotientSurface adapter)
    eq

record AdvanceWavePhasePhysicalKernelExtensionalityRequest : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    equalityKernelFallbackConstructed :
      Bool

    equalityKernelFallbackConstructed-v :
      equalityKernelFallbackConstructed ≡ true

    physicalKernelQuotientBridgeConstructed :
      Bool

    physicalKernelQuotientBridgeConstructed-v :
      physicalKernelQuotientBridgeConstructed ≡ false

    observationKernelPrimitiveRequest :
      AdvanceWavePhaseObservationKernelPrimitiveRequest

    requestBoundary :
      List String

open AdvanceWavePhasePhysicalKernelExtensionalityRequest public

advanceWavePhasePhysicalKernelExtensionalityRequest :
  AdvanceWavePhasePhysicalKernelExtensionalityRequest
advanceWavePhasePhysicalKernelExtensionalityRequest =
  record
    { requestedInterfaceName =
        "AdvanceWavePhasePhysicalKernelQuotientAdapter"
    ; exactRequiredFields =
        "kernelEquivalence : ShiftWavePhaseState -> ShiftWavePhaseState -> Set ell-r"
        ∷ "kernelEquivalenceIsEquivalence : IsEquivalence kernelEquivalence"
        ∷ "advanceWavePhaseKernelExtensionality : kernelEquivalence psi chi -> kernelEquivalence (advanceWavePhaseState psi) (advanceWavePhaseState chi)"
        ∷ "quotientSurface : SetoidQuotientSurface (ShiftWavePhaseState / kernelEquivalence)"
        ∷ "quotient equality then follows from quotientSound, not from kernelEquivalenceImpliesEquality"
        ∷ []
    ; equalityKernelFallbackConstructed =
        true
    ; equalityKernelFallbackConstructed-v =
        refl
    ; physicalKernelQuotientBridgeConstructed =
        false
    ; physicalKernelQuotientBridgeConstructed-v =
        refl
    ; observationKernelPrimitiveRequest =
        advanceWavePhaseObservationKernelPrimitiveRequest
    ; requestBoundary =
        "advanceWavePhasePropositionalEqualityKernelAdapter is inhabited, but it is only the equality fallback"
        ∷ "A physical observational kernel should not be forced to collapse to propositional equality"
        ∷ "For a selected observation/projection kernel, advanceWavePhaseKernelExtensionality now follows from advanceWavePhaseObservationNaturality"
        ∷ "The selected linear and phase-homogeneous observation interface is inhabited only by a degenerate coordinate algebra, not by a nontrivial physical projection algebra"
        ∷ "Once that primitive and a quotient surface are supplied, quotientSound gives kernelEquivalence -> quotientClass psi == quotientClass chi"
        ∷ "This request does not construct Hilbert space, self-adjointness, Stone data, or physical Schrodinger closure"
        ∷ []
    }

record PhysicalSchrodingerTraversalAdapter
  {ℓw ℓr : Level}
  : Setω where
  field
    WaveState :
      Set ℓw

    kernelEquivalence :
      WaveState →
      WaveState →
      Set ℓr

    kernelEquivalenceIsEquivalence :
      QS.IsEquivalence kernelEquivalence

    physicalTraversal :
      WaveState →
      WaveState

    physicalTraversalRespectsKernelEquivalence :
      {ψ χ : WaveState} →
      kernelEquivalence ψ χ →
      kernelEquivalence (physicalTraversal ψ) (physicalTraversal χ)

    selectedSetoid :
      QS.SetoidSurface ℓw ℓr

    selectedSetoidCarrierIsWaveState :
      QS.Carrier selectedSetoid ≡ WaveState

    traversalSurface :
      QS.SetoidUnaryOperationSurface selectedSetoid

    adapterBoundary :
      List String

open PhysicalSchrodingerTraversalAdapter public

physicalSchrodingerTraversalAdapterToSetoidOperation :
  {ℓw ℓr : Level} →
  (adapter : PhysicalSchrodingerTraversalAdapter {ℓw} {ℓr}) →
  QS.SetoidUnaryOperationSurface
    (PhysicalSchrodingerTraversalAdapter.selectedSetoid adapter)
physicalSchrodingerTraversalAdapterToSetoidOperation adapter =
  PhysicalSchrodingerTraversalAdapter.traversalSurface adapter

advanceWavePhaseKernelEqualityAdapterToPhysicalTraversalAdapter :
  {ℓr : Level} →
  AdvanceWavePhaseKernelEqualityAdapter {ℓr} →
  PhysicalSchrodingerTraversalAdapter {lzero} {ℓr}
advanceWavePhaseKernelEqualityAdapterToPhysicalTraversalAdapter adapter =
  record
    { WaveState =
        SPWSI.ShiftWavePhaseState
    ; kernelEquivalence =
        AdvanceWavePhaseKernelEqualityAdapter.kernelEquivalence adapter
    ; kernelEquivalenceIsEquivalence =
        AdvanceWavePhaseKernelEqualityAdapter.kernelEquivalenceIsEquivalence
          adapter
    ; physicalTraversal =
        SPWSI.advanceWavePhaseState
    ; physicalTraversalRespectsKernelEquivalence =
        advanceWavePhaseKernelRespectsEquivalence adapter
    ; selectedSetoid =
        advanceWavePhasePhysicalKernelSetoid adapter
    ; selectedSetoidCarrierIsWaveState =
        refl
    ; traversalSurface =
        advanceWavePhasePhysicalKernelTraversal adapter
    ; adapterBoundary =
        "Concrete traversal is DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance.advanceWavePhaseState"
        ∷ "Physical kernel equivalence is supplied externally on ShiftWavePhaseState"
        ∷ "The required bridge is kernelEquivalenceImpliesEquality, so the equality-setoid traversal can discharge preservation"
        ∷ "This adapter constructs only a kernel-respecting setoid traversal; it does not promote Hilbert, Stone, self-adjoint, or unitary structure"
        ∷ AdvanceWavePhaseKernelEqualityAdapter.adapterBoundary adapter
    }

record PhysicalSchrodingerTraversalAdapterRequest : Set where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    inspectedConcreteTraversal :
      String

    equalityTraversalSurfaceAvailable :
      Bool

    equalityTraversalSurfaceAvailable-v :
      equalityTraversalSurfaceAvailable ≡ true

    physicalKernelTraversalSurfaceConstructed :
      Bool

    physicalKernelTraversalSurfaceConstructed-v :
      physicalKernelTraversalSurfaceConstructed ≡ false

    requestBoundary :
      List String

open PhysicalSchrodingerTraversalAdapterRequest public

physicalSchrodingerTraversalAdapterRequest :
  PhysicalSchrodingerTraversalAdapterRequest
physicalSchrodingerTraversalAdapterRequest =
  record
    { requestedInterfaceName =
        "PhysicalSchrodingerTraversalAdapter"
    ; exactRequiredFields =
        "WaveState : Set ell-w"
        ∷ "kernelEquivalence : WaveState -> WaveState -> Set ell-r"
        ∷ "kernelEquivalenceIsEquivalence : IsEquivalence kernelEquivalence"
        ∷ "physicalTraversal : WaveState -> WaveState"
        ∷ "physicalTraversalRespectsKernelEquivalence : kernelEquivalence psi chi -> kernelEquivalence (physicalTraversal psi) (physicalTraversal chi)"
        ∷ "selectedSetoid : SetoidSurface ell-w ell-r"
        ∷ "selectedSetoidCarrierIsWaveState : Carrier selectedSetoid == WaveState"
        ∷ "traversalSurface : SetoidUnaryOperationSurface selectedSetoid"
        ∷ "For concrete advanceWavePhaseState fallback: kernelEquivalenceImpliesEquality : kernelEquivalence psi chi -> psi == chi"
        ∷ "For non-collapsing advanceWavePhaseState quotient route: advanceWavePhaseKernelExtensionality plus SetoidQuotientSurface"
        ∷ []
    ; inspectedConcreteTraversal =
        "DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance.advanceWavePhaseState"
    ; equalityTraversalSurfaceAvailable =
        true
    ; equalityTraversalSurfaceAvailable-v =
        refl
    ; physicalKernelTraversalSurfaceConstructed =
        false
    ; physicalKernelTraversalSurfaceConstructed-v =
        refl
    ; requestBoundary =
        "advanceWavePhaseState packages as a SetoidUnaryOperationSurface only over propositional equality"
        ∷ "No inspected Schrodinger-facing module supplies a physical kernel equivalence on ShiftWavePhaseState"
        ∷ "No inspected module supplies a proof that advanceWavePhaseState respects a physical Schrodinger kernel"
        ∷ "If the supplied physical kernel collapses to equality on ShiftWavePhaseState, AdvanceWavePhaseKernelEqualityAdapter bridges it to the concrete equality traversal"
        ∷ "If the supplied physical kernel does not collapse to equality, AdvanceWavePhasePhysicalKernelQuotientAdapter requests exactly kernel extensionality plus quotientSound"
        ∷ "The adapter must provide the kernel setoid and the traversal respect proof before quotient descent can be physical"
        ∷ []
    }

record KernelPreservingEvolutionDescent
  {ℓw ℓr ℓq : Level}
  {S : QS.SetoidSurface ℓw ℓr}
  (Q : QS.SetoidQuotientSurface S ℓq)
  : Setω where
  field
    prequotientEvolution :
      QS.SetoidUnaryOperationSurface S

    quotientEvolution :
      QS.QuotientCarrier Q →
      QS.QuotientCarrier Q

    quotientEvolution-β :
      (ψ : QS.Carrier S) →
      quotientEvolution (QS.quotientClass Q ψ)
      ≡
      QS.quotientClass Q
        (QS.SetoidUnaryOperationSurface.unaryOperation
          prequotientEvolution
          ψ)

    kernelPreservation :
      {ψ χ : QS.Carrier S} →
      QS._≈_ S ψ χ →
      QS._≈_ S
        (QS.SetoidUnaryOperationSurface.unaryOperation
          prequotientEvolution
          ψ)
        (QS.SetoidUnaryOperationSurface.unaryOperation
          prequotientEvolution
          χ)

open KernelPreservingEvolutionDescent public

setoidKernelPreservingEvolutionDescent :
  {ℓw ℓr ℓq : Level} →
  {S : QS.SetoidSurface ℓw ℓr} →
  (Q : QS.SetoidQuotientSurface S ℓq) →
  (E : QS.SetoidUnaryOperationSurface S) →
  KernelPreservingEvolutionDescent Q
setoidKernelPreservingEvolutionDescent Q E =
  record
    { prequotientEvolution =
        E
    ; quotientEvolution =
        QS.quotientRec Q
          _
          (λ ψ →
            QS.quotientClass Q
              (QS.SetoidUnaryOperationSurface.unaryOperation E ψ))
          (λ ψ χ ψ≈χ →
            QS.quotientSound Q
              (QS.SetoidUnaryOperationSurface.unaryOperationRespects≈
                E
                ψ≈χ))
    ; quotientEvolution-β =
        λ ψ →
          QS.quotientRec-β Q
            _
            (λ χ →
              QS.quotientClass Q
                (QS.SetoidUnaryOperationSurface.unaryOperation E χ))
            (λ χ χ′ χ≈χ′ →
              QS.quotientSound Q
                (QS.SetoidUnaryOperationSurface.unaryOperationRespects≈
                  E
                  χ≈χ′))
            ψ
    ; kernelPreservation =
        λ ψ≈χ →
          QS.SetoidUnaryOperationSurface.unaryOperationRespects≈
            E
            ψ≈χ
    }

advanceWavePhasePhysicalKernelQuotientDescent :
  {ℓr ℓq : Level} →
  (adapter : AdvanceWavePhasePhysicalKernelQuotientAdapter {ℓr} {ℓq}) →
  KernelPreservingEvolutionDescent
    (AdvanceWavePhasePhysicalKernelQuotientAdapter.quotientSurface adapter)
advanceWavePhasePhysicalKernelQuotientDescent adapter =
  setoidKernelPreservingEvolutionDescent
    (AdvanceWavePhasePhysicalKernelQuotientAdapter.quotientSurface adapter)
    (advanceWavePhasePhysicalKernelQuotientTraversal adapter)

selectedFiniteQuotientAdvanceTraversal :
  QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
  QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface
selectedFiniteQuotientAdvanceTraversal =
  DDSI.shiftPressureAdvance

selectedFiniteQuotientAdvanceTraversal-β :
  (ψ : SPWSI.ShiftWavePhaseState) →
  selectedFiniteQuotientAdvanceTraversal
    (QS.quotientClass shiftWavePhaseSelectedObservationQuotientSurface ψ)
  ≡
  QS.quotientClass
    shiftWavePhaseSelectedObservationQuotientSurface
    (SPWSI.advanceWavePhaseState ψ)
selectedFiniteQuotientAdvanceTraversal-β ψ =
  refl

selectedFiniteQuotientAdvanceMovesStart :
  selectedFiniteQuotientAdvanceTraversal SPTI.shiftStartPoint
  ≡
  SPTI.shiftNextPoint
selectedFiniteQuotientAdvanceMovesStart =
  refl

selectedFiniteQuotientAdvanceMovesNext :
  selectedFiniteQuotientAdvanceTraversal SPTI.shiftNextPoint
  ≡
  SPTI.shiftHeldExitPoint
selectedFiniteQuotientAdvanceMovesNext =
  refl

selectedFiniteQuotientAdvanceFixesHeld :
  selectedFiniteQuotientAdvanceTraversal SPTI.shiftHeldExitPoint
  ≡
  SPTI.shiftHeldExitPoint
selectedFiniteQuotientAdvanceFixesHeld =
  refl

selectedFiniteQuotientAdvanceNoPreimageOfStart :
  (q :
    QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
  selectedFiniteQuotientAdvanceTraversal q
  ≡
  SPTI.shiftStartPoint →
  ⊥
selectedFiniteQuotientAdvanceNoPreimageOfStart SPTI.shiftStartPoint ()
selectedFiniteQuotientAdvanceNoPreimageOfStart SPTI.shiftNextPoint ()
selectedFiniteQuotientAdvanceNoPreimageOfStart SPTI.shiftHeldExitPoint ()

selectedFinitePhaseSpaceAmplitude :
  QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
  Nat
selectedFinitePhaseSpaceAmplitude =
  DDSI.shiftPointDensity

selectedFinitePhaseSpacePhase :
  QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
  Nat
selectedFinitePhaseSpacePhase =
  DDSI.shiftHeldPotential

selectedFinitePhaseSpaceInterferenceCharge :
  QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
  Nat
selectedFinitePhaseSpaceInterferenceCharge q =
  selectedFinitePhaseSpaceAmplitude q
  + selectedFinitePhaseSpacePhase q

selectedFinitePhaseSpaceAmplitudeAdvance :
  (q : QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
  selectedFinitePhaseSpaceAmplitude
    (selectedFiniteQuotientAdvanceTraversal q)
  ≡
  advanceSelectedAmplitudeProxy
    (selectedFinitePhaseSpaceAmplitude q)
selectedFinitePhaseSpaceAmplitudeAdvance SPTI.shiftStartPoint =
  refl
selectedFinitePhaseSpaceAmplitudeAdvance SPTI.shiftNextPoint =
  refl
selectedFinitePhaseSpaceAmplitudeAdvance SPTI.shiftHeldExitPoint =
  refl

selectedFinitePhaseSpacePhaseAdvance :
  (q : QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
  selectedFinitePhaseSpacePhase
    (selectedFiniteQuotientAdvanceTraversal q)
  ≡
  advanceSelectedPhaseProxy
    (selectedFinitePhaseSpacePhase q)
selectedFinitePhaseSpacePhaseAdvance SPTI.shiftStartPoint =
  refl
selectedFinitePhaseSpacePhaseAdvance SPTI.shiftNextPoint =
  refl
selectedFinitePhaseSpacePhaseAdvance SPTI.shiftHeldExitPoint =
  refl

selectedFinitePhaseSpaceInterferenceChargeTransport :
  (q : QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
  selectedFinitePhaseSpaceInterferenceCharge q
  ≡
  selectedFinitePhaseSpaceInterferenceCharge
    (selectedFiniteQuotientAdvanceTraversal q)
selectedFinitePhaseSpaceInterferenceChargeTransport SPTI.shiftStartPoint =
  refl
selectedFinitePhaseSpaceInterferenceChargeTransport SPTI.shiftNextPoint =
  refl
selectedFinitePhaseSpaceInterferenceChargeTransport SPTI.shiftHeldExitPoint =
  refl

record FinitePhaseSpaceReversibleTraversalCandidate : Set where
  field
    reverseTraversal :
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface

    leftInverse :
      (q :
        QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
      reverseTraversal (selectedFiniteQuotientAdvanceTraversal q)
      ≡
      q

    rightInverse :
      (q :
        QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
      selectedFiniteQuotientAdvanceTraversal (reverseTraversal q)
      ≡
      q

open FinitePhaseSpaceReversibleTraversalCandidate public

selectedFinitePhaseSpaceNoReversibleTraversal :
  FinitePhaseSpaceReversibleTraversalCandidate →
  ⊥
selectedFinitePhaseSpaceNoReversibleTraversal candidate =
  selectedFiniteQuotientAdvanceNoPreimageOfStart
    (FinitePhaseSpaceReversibleTraversalCandidate.reverseTraversal
      candidate
      SPTI.shiftStartPoint)
    (FinitePhaseSpaceReversibleTraversalCandidate.rightInverse
      candidate
      SPTI.shiftStartPoint)

record SelectedFinitePhaseSpaceReversibleTraversalObstruction : Setω where
  field
    quotientCarrier :
      Set

    quotientCarrierIsSelectedFiniteCoordinateCarrier :
      quotientCarrier
      ≡
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface

    amplitudeCoordinate :
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      Nat

    phaseCoordinate :
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      Nat

    interferenceCharge :
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      Nat

    amplitudeAdvanceLaw :
      (q :
        QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
      amplitudeCoordinate (selectedFiniteQuotientAdvanceTraversal q)
      ≡
      advanceSelectedAmplitudeProxy (amplitudeCoordinate q)

    phaseAdvanceLaw :
      (q :
        QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
      phaseCoordinate (selectedFiniteQuotientAdvanceTraversal q)
      ≡
      advanceSelectedPhaseProxy (phaseCoordinate q)

    interferenceChargeTransportLaw :
      (q :
        QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
      interferenceCharge q
      ≡
      interferenceCharge (selectedFiniteQuotientAdvanceTraversal q)

    reversibleTraversalCandidateShape :
      Set

    reversibleTraversalCandidateShape-v :
      reversibleTraversalCandidateShape
      ≡
      FinitePhaseSpaceReversibleTraversalCandidate

    noReversibleTraversalExtendingCurrentAdvance :
      FinitePhaseSpaceReversibleTraversalCandidate →
      ⊥

    finiteAmplitudePhaseDefinitionsAvailable :
      Bool

    finiteAmplitudePhaseDefinitionsAvailable-v :
      finiteAmplitudePhaseDefinitionsAvailable ≡ true

    finitePhaseSpaceTransportConstructed :
      Bool

    finitePhaseSpaceTransportConstructed-v :
      finitePhaseSpaceTransportConstructed ≡ true

    reversibleTraversalConstructedFromCurrentData :
      Bool

    reversibleTraversalConstructedFromCurrentData-v :
      reversibleTraversalConstructedFromCurrentData ≡ false

    firstMissingPrimitiveName :
      String

    absenceLedger :
      List String

open SelectedFinitePhaseSpaceReversibleTraversalObstruction public

selectedFinitePhaseSpaceReversibleTraversalObstruction :
  SelectedFinitePhaseSpaceReversibleTraversalObstruction
selectedFinitePhaseSpaceReversibleTraversalObstruction =
  record
    { quotientCarrier =
        QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface
    ; quotientCarrierIsSelectedFiniteCoordinateCarrier =
        refl
    ; amplitudeCoordinate =
        selectedFinitePhaseSpaceAmplitude
    ; phaseCoordinate =
        selectedFinitePhaseSpacePhase
    ; interferenceCharge =
        selectedFinitePhaseSpaceInterferenceCharge
    ; amplitudeAdvanceLaw =
        selectedFinitePhaseSpaceAmplitudeAdvance
    ; phaseAdvanceLaw =
        selectedFinitePhaseSpacePhaseAdvance
    ; interferenceChargeTransportLaw =
        selectedFinitePhaseSpaceInterferenceChargeTransport
    ; reversibleTraversalCandidateShape =
        FinitePhaseSpaceReversibleTraversalCandidate
    ; reversibleTraversalCandidateShape-v =
        refl
    ; noReversibleTraversalExtendingCurrentAdvance =
        selectedFinitePhaseSpaceNoReversibleTraversal
    ; finiteAmplitudePhaseDefinitionsAvailable =
        true
    ; finiteAmplitudePhaseDefinitionsAvailable-v =
        refl
    ; finitePhaseSpaceTransportConstructed =
        true
    ; finitePhaseSpaceTransportConstructed-v =
        refl
    ; reversibleTraversalConstructedFromCurrentData =
        false
    ; reversibleTraversalConstructedFromCurrentData-v =
        refl
    ; firstMissingPrimitiveName =
        "Reversible physical phase-space traversal extending the finite amplitude/phase advance"
    ; absenceLedger =
        "Existing finite phase-space data are only amplitude, phase, and conserved amplitude-plus-phase on the selected quotient carrier"
        ∷ "The induced finite table moves amplitude 1 -> 2 -> 3 and phase 2 -> 1 -> 0, then fixes the held endpoint"
        ∷ "The selected quotient advance is not reversible: rightInverse at shiftStartPoint would require a preimage of shiftStartPoint, but no quotient point maps there"
        ∷ "Therefore the finite amplitude/phase transport is a directed convergence step, not a reversible phase-space traversal"
        ∷ "A Stone upgrade must supply additional physical time and invertible traversal data; it cannot be obtained from the current finite table alone"
        ∷ "No Hilbert, Stone, self-adjoint, unitary, or Schrodinger-equation promotion follows from this phase-space obstruction"
        ∷ []
    }

record PhysicalPhaseSpaceStateSurface : Setω where
  field
    PhysicalPhaseSpace :
      Set

    toWavePhaseState :
      PhysicalPhaseSpace →
      SPWSI.ShiftWavePhaseState

    finiteShadow :
      PhysicalPhaseSpace →
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface

    finiteShadowAgreesWithWave :
      (x : PhysicalPhaseSpace) →
      finiteShadow x
      ≡
      QS.quotientClass
        shiftWavePhaseSelectedObservationQuotientSurface
        (toWavePhaseState x)

    phaseSpaceAmplitude :
      PhysicalPhaseSpace →
      Nat

    phaseSpacePhase :
      PhysicalPhaseSpace →
      Nat

    phaseSpaceInterferenceCharge :
      PhysicalPhaseSpace →
      Nat

    amplitudeMatchesFiniteShadow :
      (x : PhysicalPhaseSpace) →
      phaseSpaceAmplitude x
      ≡
      selectedFinitePhaseSpaceAmplitude (finiteShadow x)

    phaseMatchesFiniteShadow :
      (x : PhysicalPhaseSpace) →
      phaseSpacePhase x
      ≡
      selectedFinitePhaseSpacePhase (finiteShadow x)

    interferenceChargeMatchesFiniteShadow :
      (x : PhysicalPhaseSpace) →
      phaseSpaceInterferenceCharge x
      ≡
      selectedFinitePhaseSpaceInterferenceCharge (finiteShadow x)

    StateScalar :
      Set

    quotientInnerProduct :
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      StateScalar

    quotientInnerProductWellDefined :
      Set

    nondegenerateProjectionSeparation :
      Set

    hilbertCompletionCarrier :
      Set

    stateSurfaceBoundary :
      List String

open PhysicalPhaseSpaceStateSurface public

record PhysicalPhaseSpaceStateSurfaceRequest : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    selectedFiniteCoordinateQuotientConstructed :
      Bool

    selectedFiniteCoordinateQuotientConstructed-v :
      selectedFiniteCoordinateQuotientConstructed ≡ true

    finiteAmplitudePhaseStateSurfaceAvailable :
      Bool

    finiteAmplitudePhaseStateSurfaceAvailable-v :
      finiteAmplitudePhaseStateSurfaceAvailable ≡ true

    physicalPhaseSpaceStateSurfaceSupplied :
      Bool

    physicalPhaseSpaceStateSurfaceSupplied-v :
      physicalPhaseSpaceStateSurfaceSupplied ≡ false

    nondegenerateProjectionSeparationSupplied :
      Bool

    nondegenerateProjectionSeparationSupplied-v :
      nondegenerateProjectionSeparationSupplied ≡ false

    quotientInnerProductWellDefinednessSupplied :
      Bool

    quotientInnerProductWellDefinednessSupplied-v :
      quotientInnerProductWellDefinednessSupplied ≡ false

    hilbertCompletionCarrierSupplied :
      Bool

    hilbertCompletionCarrierSupplied-v :
      hilbertCompletionCarrierSupplied ≡ false

    firstMissingPrimitiveName :
      String

    requestBoundary :
      List String

open PhysicalPhaseSpaceStateSurfaceRequest public

physicalPhaseSpaceStateSurfaceRequest :
  PhysicalPhaseSpaceStateSurfaceRequest
physicalPhaseSpaceStateSurfaceRequest =
  record
    { requestedInterfaceName =
        "PhysicalPhaseSpaceStateSurface"
    ; exactRequiredFields =
        "PhysicalPhaseSpace : Set"
        ∷ "toWavePhaseState : PhysicalPhaseSpace -> ShiftWavePhaseState"
        ∷ "finiteShadow : PhysicalPhaseSpace -> selected finite quotient carrier"
        ∷ "finiteShadowAgreesWithWave : finiteShadow x == quotientClass (toWavePhaseState x)"
        ∷ "phase-space amplitude, phase, and interference-charge coordinates matching the finite shadow"
        ∷ "StateScalar : Set"
        ∷ "quotientInnerProduct : quotientCarrier -> quotientCarrier -> StateScalar"
        ∷ "quotientInnerProductWellDefined : Set"
        ∷ "nondegenerateProjectionSeparation : Set"
        ∷ "hilbertCompletionCarrier : Set"
        ∷ []
    ; selectedFiniteCoordinateQuotientConstructed =
        true
    ; selectedFiniteCoordinateQuotientConstructed-v =
        refl
    ; finiteAmplitudePhaseStateSurfaceAvailable =
        true
    ; finiteAmplitudePhaseStateSurfaceAvailable-v =
        refl
    ; physicalPhaseSpaceStateSurfaceSupplied =
        false
    ; physicalPhaseSpaceStateSurfaceSupplied-v =
        refl
    ; nondegenerateProjectionSeparationSupplied =
        false
    ; nondegenerateProjectionSeparationSupplied-v =
        refl
    ; quotientInnerProductWellDefinednessSupplied =
        false
    ; quotientInnerProductWellDefinednessSupplied-v =
        refl
    ; hilbertCompletionCarrierSupplied =
        false
    ; hilbertCompletionCarrierSupplied-v =
        refl
    ; firstMissingPrimitiveName =
        "Physical phase-space state surface with nondegenerate projection separation and quotient inner-product well-definedness"
    ; requestBoundary =
        "The selected finite quotient already exposes amplitude, phase, and conserved amplitude-plus-phase coordinates"
        ∷ "PhysicalPhaseSpaceStateSurface is a supplied interface for a physical state carrier mapped to ShiftWavePhaseState and shadowed into the finite quotient"
        ∷ "The surface deliberately separates finite coordinate bookkeeping from nondegenerate physical projection separation"
        ∷ "The quotient inner product is only a requested field with a well-definedness witness; no scalar or topology API is invented here"
        ∷ "No Hilbert quotient, Stone bundle, self-adjoint generator, unitary group, or Schrodinger-equation promotion follows from this request"
        ∷ []
    }

record PhaseSpaceReversibleTraversalSuppliedInterface : Setω where
  field
    quotientCarrier :
      Set

    quotientCarrierIsSelectedFiniteCoordinateCarrier :
      quotientCarrier
      ≡
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface

    suppliedReversibleTraversalCandidate :
      FinitePhaseSpaceReversibleTraversalCandidate

    forwardTraversal :
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface

    forwardTraversalIsSelectedAdvance :
      forwardTraversal
      ≡
      selectedFiniteQuotientAdvanceTraversal

    inverseTraversal :
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface

    leftInverseLaw :
      (q :
        QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
      inverseTraversal (forwardTraversal q)
      ≡
      q

    rightInverseLaw :
      (q :
        QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
      forwardTraversal (inverseTraversal q)
      ≡
      q

    suppliedInterfaceWouldGiveFiniteTraversalGroup :
      Bool

    suppliedInterfaceWouldGiveFiniteTraversalGroup-v :
      suppliedInterfaceWouldGiveFiniteTraversalGroup ≡ true

    constructedFromCurrentAdvance :
      Bool

    constructedFromCurrentAdvance-v :
      constructedFromCurrentAdvance ≡ false

    interfaceBoundary :
      List String

open PhaseSpaceReversibleTraversalSuppliedInterface public

phaseSpaceReversibleTraversalSuppliedInterface :
  FinitePhaseSpaceReversibleTraversalCandidate →
  PhaseSpaceReversibleTraversalSuppliedInterface
phaseSpaceReversibleTraversalSuppliedInterface candidate =
  record
    { quotientCarrier =
        QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface
    ; quotientCarrierIsSelectedFiniteCoordinateCarrier =
        refl
    ; suppliedReversibleTraversalCandidate =
        candidate
    ; forwardTraversal =
        selectedFiniteQuotientAdvanceTraversal
    ; forwardTraversalIsSelectedAdvance =
        refl
    ; inverseTraversal =
        FinitePhaseSpaceReversibleTraversalCandidate.reverseTraversal
          candidate
    ; leftInverseLaw =
        FinitePhaseSpaceReversibleTraversalCandidate.leftInverse
          candidate
    ; rightInverseLaw =
        FinitePhaseSpaceReversibleTraversalCandidate.rightInverse
          candidate
    ; suppliedInterfaceWouldGiveFiniteTraversalGroup =
        true
    ; suppliedInterfaceWouldGiveFiniteTraversalGroup-v =
        refl
    ; constructedFromCurrentAdvance =
        false
    ; constructedFromCurrentAdvance-v =
        refl
    ; interfaceBoundary =
        "This is only the supplied-interface route: if an external FinitePhaseSpaceReversibleTraversalCandidate is supplied, its reverseTraversal and inverse laws are exposed as the finite traversal-group surface"
        ∷ "The current selected advance does not supply such a candidate; selectedFinitePhaseSpaceNoReversibleTraversal refutes any candidate extending the current finite table"
        ∷ "The interface is therefore conditional and fail-closed, not a construction from local quotient data"
        ∷ "No Hilbert quotient, Stone bundle, self-adjoint generator, unitary group, or Schrodinger-equation promotion follows from this wrapper"
        ∷ []
    }

record PhysicalReversiblePhaseSpaceTraversalSurface : Setω where
  field
    PhysicalPhaseSpace :
      Set

    physicalForwardTraversal :
      PhysicalPhaseSpace →
      PhysicalPhaseSpace

    physicalInverseTraversal :
      PhysicalPhaseSpace →
      PhysicalPhaseSpace

    physicalLeftInverseLaw :
      (x : PhysicalPhaseSpace) →
      physicalInverseTraversal (physicalForwardTraversal x)
      ≡
      x

    physicalRightInverseLaw :
      (x : PhysicalPhaseSpace) →
      physicalForwardTraversal (physicalInverseTraversal x)
      ≡
      x

    finiteShadow :
      PhysicalPhaseSpace →
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface

    finiteShadowForwardLaw :
      (x : PhysicalPhaseSpace) →
      finiteShadow (physicalForwardTraversal x)
      ≡
      selectedFiniteQuotientAdvanceTraversal (finiteShadow x)

    finiteShadowInverseClaimed :
      Bool

    finiteShadowInverseClaimed-v :
      finiteShadowInverseClaimed ≡ false

    constructedFromCurrentAdvance :
      Bool

    constructedFromCurrentAdvance-v :
      constructedFromCurrentAdvance ≡ false

    traversalBoundary :
      List String

open PhysicalReversiblePhaseSpaceTraversalSurface public

record SelectedFiniteAdvanceTraversalSemigroupObstruction : Setω where
  field
    quotientCarrier :
      Set

    quotientCarrierIsSelectedFiniteCoordinateCarrier :
      quotientCarrier
      ≡
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface

    quotientTraversal :
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface

    quotientTraversalIsAdvance :
      quotientTraversal
      ≡
      selectedFiniteQuotientAdvanceTraversal

    quotientTraversal-β :
      (ψ : SPWSI.ShiftWavePhaseState) →
      quotientTraversal
        (QS.quotientClass shiftWavePhaseSelectedObservationQuotientSurface ψ)
      ≡
      QS.quotientClass
        shiftWavePhaseSelectedObservationQuotientSurface
        (SPWSI.advanceWavePhaseState ψ)

    startMoves :
      quotientTraversal SPTI.shiftStartPoint
      ≡
      SPTI.shiftNextPoint

    nextMoves :
      quotientTraversal SPTI.shiftNextPoint
      ≡
      SPTI.shiftHeldExitPoint

    heldFixed :
      quotientTraversal SPTI.shiftHeldExitPoint
      ≡
      SPTI.shiftHeldExitPoint

    noPreimageOfStart :
      (q : QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface) →
      quotientTraversal q
      ≡
      SPTI.shiftStartPoint →
      ⊥

    finiteAdvanceTraversalConstructed :
      Bool

    finiteAdvanceTraversalConstructed-v :
      finiteAdvanceTraversalConstructed ≡ true

    nontrivialFiniteTraversalConstructed :
      Bool

    nontrivialFiniteTraversalConstructed-v :
      nontrivialFiniteTraversalConstructed ≡ true

    finiteTraversalGroupConstructed :
      Bool

    finiteTraversalGroupConstructed-v :
      finiteTraversalGroupConstructed ≡ false

    firstGroupBlockerName :
      String

    obstructionBoundary :
      List String

open SelectedFiniteAdvanceTraversalSemigroupObstruction public

selectedFiniteAdvanceTraversalSemigroupObstruction :
  SelectedFiniteAdvanceTraversalSemigroupObstruction
selectedFiniteAdvanceTraversalSemigroupObstruction =
  record
    { quotientCarrier =
        QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface
    ; quotientCarrierIsSelectedFiniteCoordinateCarrier =
        refl
    ; quotientTraversal =
        selectedFiniteQuotientAdvanceTraversal
    ; quotientTraversalIsAdvance =
        refl
    ; quotientTraversal-β =
        selectedFiniteQuotientAdvanceTraversal-β
    ; startMoves =
        selectedFiniteQuotientAdvanceMovesStart
    ; nextMoves =
        selectedFiniteQuotientAdvanceMovesNext
    ; heldFixed =
        selectedFiniteQuotientAdvanceFixesHeld
    ; noPreimageOfStart =
        selectedFiniteQuotientAdvanceNoPreimageOfStart
    ; finiteAdvanceTraversalConstructed =
        true
    ; finiteAdvanceTraversalConstructed-v =
        refl
    ; nontrivialFiniteTraversalConstructed =
        true
    ; nontrivialFiniteTraversalConstructed-v =
        refl
    ; finiteTraversalGroupConstructed =
        false
    ; finiteTraversalGroupConstructed-v =
        refl
    ; firstGroupBlockerName =
        "advanceWavePhaseState descends to a non-invertible finite traversal: shiftStartPoint has no preimage"
    ; obstructionBoundary =
        "The selected finite quotient traversal induced by advanceWavePhaseState is inhabited and nontrivial"
        ∷ "Its table is shiftStartPoint -> shiftNextPoint, shiftNextPoint -> shiftHeldExitPoint, and shiftHeldExitPoint -> shiftHeldExitPoint"
        ∷ "That table is not a finite group action or automorphism: no quotient point maps to shiftStartPoint"
        ∷ "The current concrete advance is therefore an irreversible convergence/semigroup step, not a one-parameter Stone traversal group"
        ∷ "A physical Stone route must supply additional invertible one-parameter traversal data instead of reusing this finite advance as a group generator"
        ∷ "No Hilbert, Stone, self-adjoint, unitary, or Schrodinger-equation promotion follows from this finite traversal"
        ∷ []
    }

record ReversibleIntegerPhaseSpaceAndQuotientInnerProductSurface : Setω where
  field
    PhysicalPhaseSpace :
      Set

    StateScalar :
      Set

    quotientInnerProduct :
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface →
      StateScalar

    quotientInnerProductWellDefined :
      Set

    integerIdentity :
      ℤ

    integerStep :
      ℤ

    integerCompose :
      ℤ →
      ℤ →
      ℤ

    integerInverse :
      ℤ →
      ℤ

    integerLeftInverseLaw :
      (t : ℤ) →
      integerCompose (integerInverse t) t
      ≡
      integerIdentity

    integerRightInverseLaw :
      (t : ℤ) →
      integerCompose t (integerInverse t)
      ≡
      integerIdentity

    integerAction :
      ℤ →
      PhysicalPhaseSpace →
      PhysicalPhaseSpace

    integerActionIdentityLaw :
      (x : PhysicalPhaseSpace) →
      integerAction integerIdentity x
      ≡
      x

    integerActionCompositionLaw :
      (s t : ℤ) →
      (x : PhysicalPhaseSpace) →
      integerAction (integerCompose s t) x
      ≡
      integerAction s (integerAction t x)

    integerActionLeftInverseLaw :
      (t : ℤ) →
      (x : PhysicalPhaseSpace) →
      integerAction (integerInverse t) (integerAction t x)
      ≡
      x

    integerActionRightInverseLaw :
      (t : ℤ) →
      (x : PhysicalPhaseSpace) →
      integerAction t (integerAction (integerInverse t) x)
      ≡
      x

    finiteShadow :
      PhysicalPhaseSpace →
      QS.QuotientCarrier shiftWavePhaseSelectedObservationQuotientSurface

    integerStepFiniteShadowLaw :
      (x : PhysicalPhaseSpace) →
      finiteShadow (integerAction integerStep x)
      ≡
      selectedFiniteQuotientAdvanceTraversal (finiteShadow x)

    finiteShadowInverseClaimed :
      Bool

    finiteShadowInverseClaimed-v :
      finiteShadowInverseClaimed ≡ false

    selectedFiniteAdvancePromotedToIntegerAction :
      Bool

    selectedFiniteAdvancePromotedToIntegerAction-v :
      selectedFiniteAdvancePromotedToIntegerAction ≡ false

    surfaceBoundary :
      List String

open ReversibleIntegerPhaseSpaceAndQuotientInnerProductSurface public

record ReversibleIntegerPhaseSpaceAndQuotientInnerProductRequest : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    selectedFiniteSemigroupObstruction :
      SelectedFiniteAdvanceTraversalSemigroupObstruction

    suppliedSurfaceWouldExposeStepComparison :
      ReversibleIntegerPhaseSpaceAndQuotientInnerProductSurface →
      Set

    quotientInnerProductSupplied :
      Bool

    quotientInnerProductSupplied-v :
      quotientInnerProductSupplied ≡ false

    quotientInnerProductWellDefinednessSupplied :
      Bool

    quotientInnerProductWellDefinednessSupplied-v :
      quotientInnerProductWellDefinednessSupplied ≡ false

    reversibleIntegerActionSupplied :
      Bool

    reversibleIntegerActionSupplied-v :
      reversibleIntegerActionSupplied ≡ false

    integerActionFiniteStepComparisonSupplied :
      Bool

    integerActionFiniteStepComparisonSupplied-v :
      integerActionFiniteStepComparisonSupplied ≡ false

    selectedFiniteAdvancePromotedToIntegerAction :
      Bool

    selectedFiniteAdvancePromotedToIntegerAction-v :
      selectedFiniteAdvancePromotedToIntegerAction ≡ false

    firstMissingPrimitiveName :
      String

    requestBoundary :
      List String

open ReversibleIntegerPhaseSpaceAndQuotientInnerProductRequest public

reversibleIntegerPhaseSpaceAndQuotientInnerProductRequest :
  ReversibleIntegerPhaseSpaceAndQuotientInnerProductRequest
reversibleIntegerPhaseSpaceAndQuotientInnerProductRequest =
  record
    { requestedInterfaceName =
        "ReversibleIntegerPhaseSpaceAndQuotientInnerProductSurface"
    ; exactRequiredFields =
        "PhysicalPhaseSpace : Set"
        ∷ "StateScalar : Set"
        ∷ "quotientInnerProduct : selected finite quotient carrier -> selected finite quotient carrier -> StateScalar"
        ∷ "quotientInnerProductWellDefined : Set"
        ∷ "integerIdentity, integerStep, integerCompose, and integerInverse over Data.Integer.ℤ"
        ∷ "integer left/right inverse laws"
        ∷ "integerAction : ℤ -> PhysicalPhaseSpace -> PhysicalPhaseSpace"
        ∷ "integerAction identity, composition, and inverse laws"
        ∷ "finiteShadow : PhysicalPhaseSpace -> selected finite quotient carrier"
        ∷ "integerStepFiniteShadowLaw comparing the supplied reversible integer step with selectedFiniteQuotientAdvanceTraversal"
        ∷ "finiteShadowInverseClaimed fixed false unless a separate accepted finite inverse is proved"
        ∷ "selectedFiniteAdvancePromotedToIntegerAction fixed false"
        ∷ []
    ; selectedFiniteSemigroupObstruction =
        selectedFiniteAdvanceTraversalSemigroupObstruction
    ; suppliedSurfaceWouldExposeStepComparison =
        λ surface →
          (x :
            ReversibleIntegerPhaseSpaceAndQuotientInnerProductSurface.PhysicalPhaseSpace
              surface) →
          ReversibleIntegerPhaseSpaceAndQuotientInnerProductSurface.finiteShadow
            surface
            (ReversibleIntegerPhaseSpaceAndQuotientInnerProductSurface.integerAction
              surface
              (ReversibleIntegerPhaseSpaceAndQuotientInnerProductSurface.integerStep
                surface)
              x)
          ≡
          selectedFiniteQuotientAdvanceTraversal
            (ReversibleIntegerPhaseSpaceAndQuotientInnerProductSurface.finiteShadow
              surface
              x)
    ; quotientInnerProductSupplied =
        false
    ; quotientInnerProductSupplied-v =
        refl
    ; quotientInnerProductWellDefinednessSupplied =
        false
    ; quotientInnerProductWellDefinednessSupplied-v =
        refl
    ; reversibleIntegerActionSupplied =
        false
    ; reversibleIntegerActionSupplied-v =
        refl
    ; integerActionFiniteStepComparisonSupplied =
        false
    ; integerActionFiniteStepComparisonSupplied-v =
        refl
    ; selectedFiniteAdvancePromotedToIntegerAction =
        false
    ; selectedFiniteAdvancePromotedToIntegerAction-v =
        refl
    ; firstMissingPrimitiveName =
        "Quotient inner product plus reversible ℤ action with finite-shadow step comparison"
    ; requestBoundary =
        "This request is the exact fail-closed supply ledger for tying an integer phase-space action to the selected quotient carrier"
        ∷ "The selected finite advance remains irreversible: SelectedFiniteAdvanceTraversalSemigroupObstruction still records no preimage for shiftStartPoint"
        ∷ "A supplied ℤ action may compare its integerStep shadow with selectedFiniteQuotientAdvanceTraversal, but no inverse for the selected finite table is claimed"
        ∷ "The quotient inner product and well-definedness proof are required fields, not derived from the finite amplitude/phase table"
        ∷ "No Hilbert, Stone, self-adjoint, unitary, or Schrodinger-equation promotion follows from this request"
        ∷ []
    }

record PhysicalReversiblePhaseSpaceTraversalSurfaceRequest : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    selectedFiniteObstruction :
      SelectedFinitePhaseSpaceReversibleTraversalObstruction

    selectedFiniteSemigroupObstruction :
      SelectedFiniteAdvanceTraversalSemigroupObstruction

    suppliedSurfaceWouldExposePhysicalInverse :
      PhysicalReversiblePhaseSpaceTraversalSurface →
      Set

    finiteAmplitudePhaseDefinitionsAvailable :
      Bool

    finiteAmplitudePhaseDefinitionsAvailable-v :
      finiteAmplitudePhaseDefinitionsAvailable ≡ true

    finiteAdvanceConstructed :
      Bool

    finiteAdvanceConstructed-v :
      finiteAdvanceConstructed ≡ true

    physicalReversibleTraversalSupplied :
      Bool

    physicalReversibleTraversalSupplied-v :
      physicalReversibleTraversalSupplied ≡ false

    finiteAdvancePromotedToInvertible :
      Bool

    finiteAdvancePromotedToInvertible-v :
      finiteAdvancePromotedToInvertible ≡ false

    firstMissingPrimitiveName :
      String

    requestBoundary :
      List String

open PhysicalReversiblePhaseSpaceTraversalSurfaceRequest public

physicalReversiblePhaseSpaceTraversalSurfaceRequest :
  PhysicalReversiblePhaseSpaceTraversalSurfaceRequest
physicalReversiblePhaseSpaceTraversalSurfaceRequest =
  record
    { requestedInterfaceName =
        "PhysicalReversiblePhaseSpaceTraversalSurface"
    ; exactRequiredFields =
        "PhysicalPhaseSpace : Set"
        ∷ "physicalForwardTraversal : PhysicalPhaseSpace -> PhysicalPhaseSpace"
        ∷ "physicalInverseTraversal : PhysicalPhaseSpace -> PhysicalPhaseSpace"
        ∷ "physicalLeftInverseLaw and physicalRightInverseLaw for the physical traversal"
        ∷ "finiteShadow : PhysicalPhaseSpace -> selected finite quotient carrier"
        ∷ "finiteShadowForwardLaw comparing the physical forward step with selectedFiniteQuotientAdvanceTraversal"
        ∷ "finiteShadowInverseClaimed fixed false unless an accepted finite inverse is separately proved"
        ∷ []
    ; selectedFiniteObstruction =
        selectedFinitePhaseSpaceReversibleTraversalObstruction
    ; selectedFiniteSemigroupObstruction =
        selectedFiniteAdvanceTraversalSemigroupObstruction
    ; suppliedSurfaceWouldExposePhysicalInverse =
        λ surface →
          (x : PhysicalReversiblePhaseSpaceTraversalSurface.PhysicalPhaseSpace
                 surface) →
          PhysicalReversiblePhaseSpaceTraversalSurface.physicalInverseTraversal
            surface
            (PhysicalReversiblePhaseSpaceTraversalSurface.physicalForwardTraversal
              surface
              x)
          ≡
          x
    ; finiteAmplitudePhaseDefinitionsAvailable =
        true
    ; finiteAmplitudePhaseDefinitionsAvailable-v =
        refl
    ; finiteAdvanceConstructed =
        true
    ; finiteAdvanceConstructed-v =
        refl
    ; physicalReversibleTraversalSupplied =
        false
    ; physicalReversibleTraversalSupplied-v =
        refl
    ; finiteAdvancePromotedToInvertible =
        false
    ; finiteAdvancePromotedToInvertible-v =
        refl
    ; firstMissingPrimitiveName =
        "External physical reversible phase-space traversal with finite-shadow comparison"
    ; requestBoundary =
        "This request deliberately separates an invertible physical traversal from the current selected finite advance"
        ∷ "The finite shadow may compare one forward physical step with the selected quotient advance"
        ∷ "It does not assert that the selected finite advance has an inverse; SelectedFiniteAdvanceTraversalSemigroupObstruction keeps that promotion false"
        ∷ "Without a supplied PhysicalReversiblePhaseSpaceTraversalSurface, only the finite amplitude/phase directed transport is available"
        ∷ "No Hilbert, Stone, self-adjoint, unitary, or Schrodinger-equation promotion follows from this request"
        ∷ []
    }

record TraversalPreservesEquivalenceReceipt
  {ℓw ℓr ℓq : Level}
  {S : QS.SetoidSurface ℓw ℓr}
  (Q : QS.SetoidQuotientSurface S ℓq)
  (E : QS.SetoidUnaryOperationSurface S)
  : Setω where
  field
    traversalOperation :
      QS.SetoidUnaryOperationSurface S

    traversalOperationIsSupplied :
      traversalOperation ≡ E

    preservesKernelEquivalence :
      {ψ χ : QS.Carrier S} →
      QS._≈_ S ψ χ →
      QS._≈_ S
        (QS.SetoidUnaryOperationSurface.unaryOperation
          traversalOperation
          ψ)
        (QS.SetoidUnaryOperationSurface.unaryOperation
          traversalOperation
          χ)

    quotientTraversal :
      QS.QuotientCarrier Q →
      QS.QuotientCarrier Q

    quotientTraversalIsFromSuppliedTraversal :
      quotientTraversal
      ≡
      KernelPreservingEvolutionDescent.quotientEvolution
        (setoidKernelPreservingEvolutionDescent Q E)

    quotientTraversal-β :
      (ψ : QS.Carrier S) →
      quotientTraversal (QS.quotientClass Q ψ)
      ≡
      QS.quotientClass Q
        (QS.SetoidUnaryOperationSurface.unaryOperation E ψ)

    preservationPromotedFromPhysicalSchrodingerTraversal :
      Bool

    preservationPromotedFromPhysicalSchrodingerTraversal-v :
      preservationPromotedFromPhysicalSchrodingerTraversal ≡ false

    receiptBoundary :
      List String

open TraversalPreservesEquivalenceReceipt public

traversalPreservesEquivalenceReceipt :
  {ℓw ℓr ℓq : Level} →
  {S : QS.SetoidSurface ℓw ℓr} →
  (Q : QS.SetoidQuotientSurface S ℓq) →
  (E : QS.SetoidUnaryOperationSurface S) →
  TraversalPreservesEquivalenceReceipt Q E
traversalPreservesEquivalenceReceipt Q E =
  record
    { traversalOperation =
        E
    ; traversalOperationIsSupplied =
        refl
    ; preservesKernelEquivalence =
        QS.SetoidUnaryOperationSurface.unaryOperationRespects≈ E
    ; quotientTraversal =
        KernelPreservingEvolutionDescent.quotientEvolution
          (setoidKernelPreservingEvolutionDescent Q E)
    ; quotientTraversalIsFromSuppliedTraversal =
        refl
    ; quotientTraversal-β =
        KernelPreservingEvolutionDescent.quotientEvolution-β
          (setoidKernelPreservingEvolutionDescent Q E)
    ; preservationPromotedFromPhysicalSchrodingerTraversal =
        false
    ; preservationPromotedFromPhysicalSchrodingerTraversal-v =
        refl
    ; receiptBoundary =
        "A supplied SetoidUnaryOperationSurface discharges traversal-preserves-equivalence by its respects field"
        ∷ "The quotient traversal is obtained by quotientRec and quotientSound from the supplied setoid operation"
        ∷ "This is not a construction of the physical Schrodinger traversal operation"
        ∷ "No Hamiltonian, Hilbert quotient, self-adjointness, Stone route, or unitary evolution is promoted"
        ∷ []
    }

record PhysicalTraversalOperationObstruction
  {ℓw ℓr : Level}
  (S : QS.SetoidSurface ℓw ℓr)
  : Setω where
  field
    firstMissingTheorem :
      SchrodingerQuotientDescentFirstMissingTheorem

    firstMissingTheoremIsPhysicalTraversal :
      firstMissingTheorem ≡ missingPhysicalTraversalOperation

    requiredTraversalSurface :
      Set _

    requiredTraversalSurfaceIsSetoidUnaryOperationSurface :
      requiredTraversalSurface
      ≡
      QS.SetoidUnaryOperationSurface S

    preservesEquivalenceWouldBeFieldOfRequiredSurface :
      Bool

    preservesEquivalenceWouldBeFieldOfRequiredSurface-v :
      preservesEquivalenceWouldBeFieldOfRequiredSurface ≡ true

    equalityTraversalAttempt :
      QS.SetoidUnaryOperationSurface
        (equalitySetoidSurface SPWSI.ShiftWavePhaseState)

    equalityTraversalAttemptIsAdvanceWavePhaseState :
      QS.SetoidUnaryOperationSurface.unaryOperation
        equalityTraversalAttempt
      ≡
      SPWSI.advanceWavePhaseState

    exactAdapterRequest :
      PhysicalSchrodingerTraversalAdapterRequest

    obstructionBoundary :
      List String

open PhysicalTraversalOperationObstruction public

physicalTraversalOperationObstruction :
  {ℓw ℓr : Level} →
  (S : QS.SetoidSurface ℓw ℓr) →
  PhysicalTraversalOperationObstruction S
physicalTraversalOperationObstruction S =
  record
    { firstMissingTheorem =
        missingPhysicalTraversalOperation
    ; firstMissingTheoremIsPhysicalTraversal =
        refl
    ; requiredTraversalSurface =
        QS.SetoidUnaryOperationSurface S
    ; requiredTraversalSurfaceIsSetoidUnaryOperationSurface =
        refl
    ; preservesEquivalenceWouldBeFieldOfRequiredSurface =
        true
    ; preservesEquivalenceWouldBeFieldOfRequiredSurface-v =
        refl
    ; equalityTraversalAttempt =
        shiftPhaseWaveAdvanceEqualityTraversal
    ; equalityTraversalAttemptIsAdvanceWavePhaseState =
        refl
    ; exactAdapterRequest =
        physicalSchrodingerTraversalAdapterRequest
    ; obstructionBoundary =
        "First missing Paper-3 theorem: construct the physical Schrodinger traversal as a SetoidUnaryOperationSurface on the selected kernel setoid"
        ∷ "Local search found advanceWavePhaseState, which is packageable only over propositional equality without a physical kernel"
        ∷ "PhysicalSchrodingerTraversalAdapterRequest is the machine-visible request for the exact missing kernel/setoid/traversal fields"
        ∷ "Once that surface is supplied, unaryOperationRespects≈ gives traversal-preserves-equivalence"
        ∷ "Then quotientRec gives the quotient traversal and quotientRec-β gives the class-level computation rule"
        ∷ "This obstruction is fail-closed: it does not invent the physical traversal or its kernel-respect proof"
        ∷ []
    }

record SchrodingerQuotientDescentReceipt
  {ℓw ℓr ℓq ℓn : Level}
  : Setω where
  field
    WaveState :
      Set ℓw

    NormValue :
      Set ℓn

    quotientCarrier :
      Set ℓq

    kernelEquivalence :
      WaveState →
      WaveState →
      Set ℓr

    quotientClass :
      WaveState →
      quotientCarrier

    prequotientNorm :
      WaveState →
      NormValue

    descendedNorm :
      quotientCarrier →
      NormValue

    normPreservation :
      (ψ : WaveState) →
      descendedNorm (quotientClass ψ) ≡ prequotientNorm ψ

    physicalPhaseSpaceStateSurfaceRequestReceipt :
      PhysicalPhaseSpaceStateSurfaceRequest

    reversibleIntegerPhaseSpaceAndQuotientInnerProductRequestReceipt :
      ReversibleIntegerPhaseSpaceAndQuotientInnerProductRequest

    firstMissingTheorem :
      SchrodingerQuotientDescentFirstMissingTheorem

    receiptStatus :
      SchrodingerQuotientDescentStatus

    nonPromotionBoundary :
      List String

open SchrodingerQuotientDescentReceipt public

setoidSchrodingerQuotientDescentReceipt :
  {ℓw ℓr ℓq ℓn : Level} →
  {S : QS.SetoidSurface ℓw ℓr} →
  {NormValue : Set ℓn} →
  (Q : QS.SetoidQuotientSurface S ℓq) →
  (N : QS.SetoidNormSurface S NormValue) →
  SchrodingerQuotientDescentFirstMissingTheorem →
  SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}
setoidSchrodingerQuotientDescentReceipt {S = S} {NormValue = NormValue}
  Q N firstMissing =
  record
    { WaveState =
        QS.Carrier S
    ; NormValue =
        NormValue
    ; quotientCarrier =
        QS.QuotientCarrier Q
    ; kernelEquivalence =
        QS._≈_ S
    ; quotientClass =
        QS.quotientClass Q
    ; prequotientNorm =
        QS.SetoidNormSurface.norm N
    ; descendedNorm =
        QS.quotientNorm Q N
    ; normPreservation =
        QS.quotientNorm-β Q N
    ; physicalPhaseSpaceStateSurfaceRequestReceipt =
        physicalPhaseSpaceStateSurfaceRequest
    ; reversibleIntegerPhaseSpaceAndQuotientInnerProductRequestReceipt =
        reversibleIntegerPhaseSpaceAndQuotientInnerProductRequest
    ; firstMissingTheorem =
        firstMissing
    ; receiptStatus =
        quotientDescentReceiptOnlyNoPromotion
    ; nonPromotionBoundary =
        "SchrodingerQuotientDescentReceipt is a quotient/norm descent obligation surface only"
        ∷ "kernelEquivalence is the supplied quotient relation, not a derived physical gauge kernel"
        ∷ "descendedNorm is supplied by the setoid quotient norm eliminator when a quotient surface is supplied"
        ∷ "KernelPreservingEvolutionDescent now proves that any supplied setoid unary operation descends through the quotient"
        ∷ "TraversalPreservesEquivalenceReceipt records the strongest admissible theorem: a supplied SetoidUnaryOperationSurface preserves equivalence and descends"
        ∷ "PhysicalPhaseSpaceStateSurfaceRequest now names the supplied state surface needed to connect finite shadows to physical phase-space coordinates and quotient inner products"
        ∷ "ReversibleIntegerPhaseSpaceAndQuotientInnerProductRequest names the exact missing quotient inner product and reversible ℤ action surface without promoting the selected finite advance to an invertible action"
        ∷ "The first missing physical theorem is construction of that Schrodinger traversal operation for the selected kernel setoid"
        ∷ "normPreservation records descent to quotient classes only; it is not unitary evolution"
        ∷ "No self-adjoint Hamiltonian, Stone theorem route, spectral theorem, or Schrodinger closure is promoted"
        ∷ []
    }

defaultSetoidSchrodingerQuotientDescentReceipt :
  {ℓw ℓr ℓq ℓn : Level} →
  {S : QS.SetoidSurface ℓw ℓr} →
  {NormValue : Set ℓn} →
  (Q : QS.SetoidQuotientSurface S ℓq) →
  (N : QS.SetoidNormSurface S NormValue) →
  SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}
defaultSetoidSchrodingerQuotientDescentReceipt Q N =
  setoidSchrodingerQuotientDescentReceipt
    Q
    N
    defaultSchrodingerQuotientDescentFirstMissingTheorem

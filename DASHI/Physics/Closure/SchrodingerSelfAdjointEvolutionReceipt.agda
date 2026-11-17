module DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Algebra.Trit using (Trit; inv; inv-invol)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (z≤n; s≤s)
open import Data.Product using (_,_)

import DASHI.Foundations.QuotientSetoidSurface as QS
import DASHI.Quantum.Stone as Stone
import DASHI.Unifier as U
import DASHI.Physics.Closure.SchrodingerQuotientDescentReceipt as SQD
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Schrödinger self-adjoint evolution receipt.
--
-- This module is an obligation surface only.  It consumes the quotient
-- descent receipt and records the remaining target route to Hilbert
-- quotient evolution.  It does not construct Schrödinger closure, a
-- self-adjoint Hamiltonian, Stone theorem, spectral theorem, or unitary
-- evolution.

data SchrodingerSelfAdjointEvolutionPromotionAuthorityToken : Set where

data SchrodingerSelfAdjointEvolutionStatus : Set where
  selfAdjointEvolutionReceiptOnlyNoPromotion :
    SchrodingerSelfAdjointEvolutionStatus

data SchrodingerSelfAdjointEvolutionOpenTarget : Set where
  openHilbertQuotient :
    SchrodingerSelfAdjointEvolutionOpenTarget

  openOneParameterTraversalAutomorphismGroup :
    SchrodingerSelfAdjointEvolutionOpenTarget

  openTritTimeReversalToTraversalCompatibility :
    SchrodingerSelfAdjointEvolutionOpenTarget

  openSelfAdjointGenerator :
    SchrodingerSelfAdjointEvolutionOpenTarget

  openStoneBundleFromTraversal :
    SchrodingerSelfAdjointEvolutionOpenTarget

  openStoneTheoremRoute :
    SchrodingerSelfAdjointEvolutionOpenTarget

  openExponentialEvolutionFormula :
    SchrodingerSelfAdjointEvolutionOpenTarget

  openSchrodingerEquationTarget :
    SchrodingerSelfAdjointEvolutionOpenTarget

data SchrodingerSelfAdjointEvolutionFirstMissingTheorem : Set where
  missingHilbertQuotientCarrier :
    SchrodingerSelfAdjointEvolutionFirstMissingTheorem

  missingOneParameterTraversalAutomorphismGroup :
    SchrodingerSelfAdjointEvolutionFirstMissingTheorem

  missingTritTimeReversalToTraversalCompatibility :
    SchrodingerSelfAdjointEvolutionFirstMissingTheorem

  missingStoneBundleFromQuotientTraversal :
    SchrodingerSelfAdjointEvolutionFirstMissingTheorem

  missingSchrodingerEquationFromStoneRoute :
    SchrodingerSelfAdjointEvolutionFirstMissingTheorem

defaultSchrodingerSelfAdjointEvolutionFirstMissingTheorem :
  SchrodingerSelfAdjointEvolutionFirstMissingTheorem
defaultSchrodingerSelfAdjointEvolutionFirstMissingTheorem =
  missingHilbertQuotientCarrier

defaultSchrodingerSelfAdjointEvolutionOpenTargets :
  List SchrodingerSelfAdjointEvolutionOpenTarget
defaultSchrodingerSelfAdjointEvolutionOpenTargets =
  openHilbertQuotient
  ∷ openOneParameterTraversalAutomorphismGroup
  ∷ openTritTimeReversalToTraversalCompatibility
  ∷ openSelfAdjointGenerator
  ∷ openStoneBundleFromTraversal
  ∷ openStoneTheoremRoute
  ∷ openExponentialEvolutionFormula
  ∷ openSchrodingerEquationTarget
  ∷ []

record TritTimeReversalCandidate : Set where
  field
    timeReversalOnTrit :
      Trit →
      Trit

    timeReversalOnTritIsInv :
      timeReversalOnTrit ≡ inv

    timeReversalInvolutive :
      (t : Trit) →
      timeReversalOnTrit (timeReversalOnTrit t) ≡ t

    candidateBoundary :
      List String

open TritTimeReversalCandidate public

tritTimeReversalCandidate :
  TritTimeReversalCandidate
tritTimeReversalCandidate =
  record
    { timeReversalOnTrit =
        inv
    ; timeReversalOnTritIsInv =
        refl
    ; timeReversalInvolutive =
        inv-invol
    ; candidateBoundary =
        "Trit time reversal is only the involution inv : neg <-> pos, zer fixed"
        ∷ "This is not a traversal automorphism group on the Schrodinger quotient"
        ∷ "No antiunitary Hilbert-space action or Hamiltonian self-adjointness follows without a bridge"
        ∷ []
    }

record StoneBundleSelfAdjointRoute
  (Tow : U.Tower)
  (HS : U.HilbertSpace)
  : Setω where
  field
    stoneBundle :
      Stone.StoneBundle Tow HS

    stoneConsequences :
      Stone.StoneConsequences stoneBundle

    selfAdjointGenerator :
      Stone.StoneSelfAdjoint
        HS
        (Stone.StoneBundle.generator stoneBundle)

open StoneBundleSelfAdjointRoute public

stoneBundleSelfAdjointRoute :
  (Tow : U.Tower) →
  (HS : U.HilbertSpace) →
  (bundle : Stone.StoneBundle Tow HS) →
  StoneBundleSelfAdjointRoute Tow HS
stoneBundleSelfAdjointRoute Tow HS bundle =
  record
    { stoneBundle =
        bundle
    ; stoneConsequences =
        Stone.Stone-theorem bundle
    ; selfAdjointGenerator =
        Stone.StoneConsequences.stone-self-adjoint
          (Stone.Stone-theorem bundle)
    }

selectedFiniteQuotientCarrier :
  Set
selectedFiniteQuotientCarrier =
  QS.QuotientCarrier SQD.shiftWavePhaseSelectedObservationQuotientSurface

cong2 :
  {A B C : Set} →
  (f : A → B → C) →
  {x x′ : A} →
  {y y′ : B} →
  x ≡ x′ →
  y ≡ y′ →
  f x y ≡ f x′ y′
cong2 f refl refl =
  refl

selectedFiniteQuotientTower :
  U.Tower
selectedFiniteQuotientTower =
  record
    { S =
        λ _ → selectedFiniteQuotientCarrier
    ; R =
        λ q → q
    ; P =
        λ q → q
    ; C =
        λ q → q
    }

selectedFiniteQuotientHilbertSpace :
  U.HilbertSpace
selectedFiniteQuotientHilbertSpace =
  record
    { H =
        selectedFiniteQuotientCarrier
    ; ⟨_,_⟩ =
        λ _ _ → U.toℝ 0
    }

selectedQuotientPointFromPrecursorBool :
  Bool →
  selectedFiniteQuotientCarrier
selectedQuotientPointFromPrecursorBool true =
  SPTI.shiftStartPoint
selectedQuotientPointFromPrecursorBool false =
  SPTI.shiftHeldExitPoint

selectedFiniteQuotientProjectionInner :
  selectedFiniteQuotientCarrier →
  selectedFiniteQuotientCarrier →
  U.ℝ
selectedFiniteQuotientProjectionInner
  SPTI.shiftStartPoint
  SPTI.shiftStartPoint =
  U.toℝ 1
selectedFiniteQuotientProjectionInner
  SPTI.shiftStartPoint
  SPTI.shiftNextPoint =
  U.toℝ 0
selectedFiniteQuotientProjectionInner
  SPTI.shiftStartPoint
  SPTI.shiftHeldExitPoint =
  U.toℝ 0
selectedFiniteQuotientProjectionInner
  SPTI.shiftNextPoint
  SPTI.shiftStartPoint =
  U.toℝ 0
selectedFiniteQuotientProjectionInner
  SPTI.shiftNextPoint
  SPTI.shiftNextPoint =
  U.toℝ 1
selectedFiniteQuotientProjectionInner
  SPTI.shiftNextPoint
  SPTI.shiftHeldExitPoint =
  U.toℝ 0
selectedFiniteQuotientProjectionInner
  SPTI.shiftHeldExitPoint
  SPTI.shiftStartPoint =
  U.toℝ 0
selectedFiniteQuotientProjectionInner
  SPTI.shiftHeldExitPoint
  SPTI.shiftNextPoint =
  U.toℝ 0
selectedFiniteQuotientProjectionInner
  SPTI.shiftHeldExitPoint
  SPTI.shiftHeldExitPoint =
  U.toℝ 1

selectedFiniteQuotientProjection :
  selectedFiniteQuotientCarrier →
  selectedFiniteQuotientCarrier
selectedFiniteQuotientProjection q =
  q

selectedFiniteQuotientProjectionInnerWellDefined :
  {ψ ψ′ χ χ′ :
    QS.Carrier
      (SQD.advanceWavePhaseObservationKernelSetoid
        SQD.shiftWavePhaseSelectedObservationKernelPrimitive)} →
  QS._≈_
    (SQD.advanceWavePhaseObservationKernelSetoid
      SQD.shiftWavePhaseSelectedObservationKernelPrimitive)
    ψ
    ψ′ →
  QS._≈_
    (SQD.advanceWavePhaseObservationKernelSetoid
      SQD.shiftWavePhaseSelectedObservationKernelPrimitive)
    χ
    χ′ →
  selectedFiniteQuotientProjectionInner
    (QS.quotientClass
      SQD.shiftWavePhaseSelectedObservationQuotientSurface
      ψ)
    (QS.quotientClass
      SQD.shiftWavePhaseSelectedObservationQuotientSurface
      χ)
  ≡
  selectedFiniteQuotientProjectionInner
    (QS.quotientClass
      SQD.shiftWavePhaseSelectedObservationQuotientSurface
      ψ′)
    (QS.quotientClass
      SQD.shiftWavePhaseSelectedObservationQuotientSurface
      χ′)
selectedFiniteQuotientProjectionInnerWellDefined ψ≈ψ′ χ≈χ′ =
  cong2
    selectedFiniteQuotientProjectionInner
    (QS.quotientSound
      SQD.shiftWavePhaseSelectedObservationQuotientSurface
      ψ≈ψ′)
    (QS.quotientSound
      SQD.shiftWavePhaseSelectedObservationQuotientSurface
      χ≈χ′)

record SelectedQuotientProjectionInnerProductSurface : Setω where
  field
    precursor :
      Stone.NoncollapsedProjectionAlgebraPrecursor

    precursorIsTwoPoint :
      precursor ≡ Stone.twoPointNoncollapsedProjectionAlgebraPrecursor

    quotientCarrier :
      Set

    quotientCarrierIsSelected :
      quotientCarrier ≡ selectedFiniteQuotientCarrier

    precursorToQuotient :
      Bool →
      selectedFiniteQuotientCarrier

    precursorToQuotientAgreesWithTwoPointEmbedding :
      (b : Bool) →
      precursorToQuotient b
      ≡
      selectedQuotientPointFromPrecursorBool b

    quotientProjection :
      selectedFiniteQuotientCarrier →
      selectedFiniteQuotientCarrier

    quotientProjectionIdempotent :
      (q : selectedFiniteQuotientCarrier) →
      quotientProjection (quotientProjection q)
      ≡
      quotientProjection q

    quotientInnerProduct :
      selectedFiniteQuotientCarrier →
      selectedFiniteQuotientCarrier →
      U.ℝ

    quotientProjectionSelfAdjoint :
      (q r : selectedFiniteQuotientCarrier) →
      quotientInnerProduct (quotientProjection q) r
      ≡
      quotientInnerProduct q (quotientProjection r)

    quotientKeptState :
      selectedFiniteQuotientCarrier

    quotientOrthogonalState :
      selectedFiniteQuotientCarrier

    quotientKeptNormWitness :
      quotientInnerProduct quotientKeptState quotientKeptState
      ≡
      U.toℝ 1

    quotientOrthogonalSeparationWitness :
      quotientInnerProduct quotientKeptState quotientOrthogonalState
      ≡
      U.toℝ 0

    precursorInnerProductTransport :
      (b c : Bool) →
      quotientInnerProduct
        (precursorToQuotient b)
        (precursorToQuotient c)
      ≡
      Stone.twoPointProjectionInner b c

    quotientInnerProductWellDefined :
      {ψ ψ′ χ χ′ :
        QS.Carrier
          (SQD.advanceWavePhaseObservationKernelSetoid
            SQD.shiftWavePhaseSelectedObservationKernelPrimitive)} →
      QS._≈_
        (SQD.advanceWavePhaseObservationKernelSetoid
          SQD.shiftWavePhaseSelectedObservationKernelPrimitive)
        ψ
        ψ′ →
      QS._≈_
        (SQD.advanceWavePhaseObservationKernelSetoid
          SQD.shiftWavePhaseSelectedObservationKernelPrimitive)
        χ
        χ′ →
      quotientInnerProduct
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          ψ)
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          χ)
      ≡
      quotientInnerProduct
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          ψ′)
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          χ′)

    selectedQuotientProjectionAlgebraSupplied :
      Bool

    selectedQuotientProjectionAlgebraSupplied-v :
      selectedQuotientProjectionAlgebraSupplied ≡ true

    selectedQuotientInnerProductWellDefinednessSupplied :
      Bool

    selectedQuotientInnerProductWellDefinednessSupplied-v :
      selectedQuotientInnerProductWellDefinednessSupplied ≡ true

    physicalHilbertCompletionPromoted :
      Bool

    physicalHilbertCompletionPromoted-v :
      physicalHilbertCompletionPromoted ≡ false

    physicalStoneTraversalPromoted :
      Bool

    physicalStoneTraversalPromoted-v :
      physicalStoneTraversalPromoted ≡ false

    surfaceBoundary :
      List String

open SelectedQuotientProjectionInnerProductSurface public

selectedQuotientProjectionInnerProductSurface :
  SelectedQuotientProjectionInnerProductSurface
selectedQuotientProjectionInnerProductSurface =
  record
    { precursor =
        Stone.twoPointNoncollapsedProjectionAlgebraPrecursor
    ; precursorIsTwoPoint =
        refl
    ; quotientCarrier =
        selectedFiniteQuotientCarrier
    ; quotientCarrierIsSelected =
        refl
    ; precursorToQuotient =
        selectedQuotientPointFromPrecursorBool
    ; precursorToQuotientAgreesWithTwoPointEmbedding =
        λ _ → refl
    ; quotientProjection =
        selectedFiniteQuotientProjection
    ; quotientProjectionIdempotent =
        λ _ → refl
    ; quotientInnerProduct =
        selectedFiniteQuotientProjectionInner
    ; quotientProjectionSelfAdjoint =
        λ _ _ → refl
    ; quotientKeptState =
        SPTI.shiftStartPoint
    ; quotientOrthogonalState =
        SPTI.shiftHeldExitPoint
    ; quotientKeptNormWitness =
        refl
    ; quotientOrthogonalSeparationWitness =
        refl
    ; precursorInnerProductTransport =
        λ
          { true true → refl
          ; true false → refl
          ; false true → refl
          ; false false → refl
          }
    ; quotientInnerProductWellDefined =
        selectedFiniteQuotientProjectionInnerWellDefined
    ; selectedQuotientProjectionAlgebraSupplied =
        true
    ; selectedQuotientProjectionAlgebraSupplied-v =
        refl
    ; selectedQuotientInnerProductWellDefinednessSupplied =
        true
    ; selectedQuotientInnerProductWellDefinednessSupplied-v =
        refl
    ; physicalHilbertCompletionPromoted =
        false
    ; physicalHilbertCompletionPromoted-v =
        refl
    ; physicalStoneTraversalPromoted =
        false
    ; physicalStoneTraversalPromoted-v =
        refl
    ; surfaceBoundary =
        "The two-point noncollapsed projection precursor is now tied to the selected finite quotient carrier by true -> shiftStartPoint and false -> shiftHeldExitPoint"
        ∷ "The selected quotient carrier carries a finite Kronecker projection inner product and identity projection"
        ∷ "Representative independence is proved through shiftWavePhaseSelectedObservationQuotientSurface.quotientSound"
        ∷ "This supplies selected finite quotient projection-algebra and inner-product well-definedness evidence only"
        ∷ "It does not supply Hilbert completion, a physical traversal group, strong continuity, a traversal-derived StoneBundle, or Schrodinger promotion"
        ∷ []
    }

record SelectedQuotientNondegenerateProjectionScalarSocket : Setω where
  field
    selectedProjectionInnerProductSurfaceReceipt :
      SelectedQuotientProjectionInnerProductSurface

    nondegenerateProjectionAlgebraRequest :
      SQD.NondegeneratePhysicalProjectionAlgebraRequest

    selectedFiniteCoordinateQuotientConstructed :
      Bool

    selectedFiniteCoordinateQuotientConstructed-v :
      selectedFiniteCoordinateQuotientConstructed ≡ true

    degenerateCoordinateAlgebraConstructed :
      Bool

    degenerateCoordinateAlgebraConstructed-v :
      degenerateCoordinateAlgebraConstructed ≡ true

    nondegenerateProjectionAlgebraSupplied :
      Bool

    nondegenerateProjectionAlgebraSupplied-v :
      nondegenerateProjectionAlgebraSupplied ≡ false

    physicalScalarFieldLawsSupplied :
      Bool

    physicalScalarFieldLawsSupplied-v :
      physicalScalarFieldLawsSupplied ≡ false

    quotientInnerProductWellDefinednessSupplied :
      Bool

    quotientInnerProductWellDefinednessSupplied-v :
      quotientInnerProductWellDefinednessSupplied ≡ false

    physicalHilbertCompletionSupplied :
      Bool

    physicalHilbertCompletionSupplied-v :
      physicalHilbertCompletionSupplied ≡ false

    requiredProjectionScalarTheoremFields :
      List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    requiredProjectionScalarTheoremFieldsAreCanonical :
      requiredProjectionScalarTheoremFields
      ≡
      SQD.canonicalNondegeneratePhysicalProjectionAlgebraTheoremFields

    firstMissingProjectionScalarTheoremField :
      SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    firstMissingProjectionScalarTheoremFieldIsPhysicalLaws :
      firstMissingProjectionScalarTheoremField
      ≡
      SQD.physicalNondegenerateProjectionScalarLawsField

    remainingProjectionScalarTheoremFieldsAfterFirstMissing :
      List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    remainingProjectionScalarTheoremFieldsAfterFirstMissingAreCanonical :
      remainingProjectionScalarTheoremFieldsAfterFirstMissing
      ≡
      SQD.canonicalNondegeneratePhysicalProjectionAlgebraRemainingFieldsAfterFirstMissing

    firstMissingPrimitiveName :
      String

    socketBoundary :
      List String

open SelectedQuotientNondegenerateProjectionScalarSocket public

selectedQuotientNondegenerateProjectionScalarSocket :
  SelectedQuotientNondegenerateProjectionScalarSocket
selectedQuotientNondegenerateProjectionScalarSocket =
  record
    { selectedProjectionInnerProductSurfaceReceipt =
        selectedQuotientProjectionInnerProductSurface
    ; nondegenerateProjectionAlgebraRequest =
        SQD.nondegeneratePhysicalProjectionAlgebraRequest
    ; selectedFiniteCoordinateQuotientConstructed =
        true
    ; selectedFiniteCoordinateQuotientConstructed-v =
        refl
    ; degenerateCoordinateAlgebraConstructed =
        true
    ; degenerateCoordinateAlgebraConstructed-v =
        refl
    ; nondegenerateProjectionAlgebraSupplied =
        false
    ; nondegenerateProjectionAlgebraSupplied-v =
        refl
    ; physicalScalarFieldLawsSupplied =
        false
    ; physicalScalarFieldLawsSupplied-v =
        refl
    ; quotientInnerProductWellDefinednessSupplied =
        false
    ; quotientInnerProductWellDefinednessSupplied-v =
        refl
    ; physicalHilbertCompletionSupplied =
        false
    ; physicalHilbertCompletionSupplied-v =
        refl
    ; requiredProjectionScalarTheoremFields =
        SQD.canonicalNondegeneratePhysicalProjectionAlgebraTheoremFields
    ; requiredProjectionScalarTheoremFieldsAreCanonical =
        refl
    ; firstMissingProjectionScalarTheoremField =
        SQD.physicalNondegenerateProjectionScalarLawsField
    ; firstMissingProjectionScalarTheoremFieldIsPhysicalLaws =
        refl
    ; remainingProjectionScalarTheoremFieldsAfterFirstMissing =
        SQD.canonicalNondegeneratePhysicalProjectionAlgebraRemainingFieldsAfterFirstMissing
    ; remainingProjectionScalarTheoremFieldsAfterFirstMissingAreCanonical =
        refl
    ; firstMissingPrimitiveName =
        "Nondegenerate physical projection algebra and scalar-field laws for quotient inner-product promotion"
    ; socketBoundary =
        "The selected finite coordinate quotient and its degenerate coordinate algebra are available from the quotient-descent lane"
        ∷ "SelectedQuotientProjectionInnerProductSurface provides representative-independent finite quotient inner-product evidence only"
        ∷ "The canonical first missing theorem field is physicalNondegenerateProjectionScalarLawsField"
        ∷ "After the first missing field, the remaining canonical fields are quotientInnerProductWellDefinednessField, globalPhysicalQuotientInnerProductWellDefinednessField, and acceptedHilbertCompletionField"
        ∷ "The nondegenerate physical projection/scalar upgrade is still unsupplied, so this socket remains below physical Hilbert completion and Stone promotion"
        ∷ "This socket tracks the exact first blocker before physical quotient inner-product/completion promotion: nontrivial projection algebra plus scalar-field laws"
        ∷ []
    }

canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteFirstField :
  List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField
canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteFirstField =
  SQD.quotientInnerProductWellDefinednessField
  ∷ SQD.globalPhysicalQuotientInnerProductWellDefinednessField
  ∷ SQD.acceptedHilbertCompletionField
  ∷ []

canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteSecondField :
  List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField
canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteSecondField =
  SQD.globalPhysicalQuotientInnerProductWellDefinednessField
  ∷ SQD.acceptedHilbertCompletionField
  ∷ []

canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField :
  List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField
canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField =
  SQD.acceptedHilbertCompletionField
  ∷ []

canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField :
  List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField
canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField =
  []

record SelectedQuotientPostProjectionScalarSocket : Setω where
  field
    selectedQuotientNondegenerateProjectionScalarSocketReceipt :
      SelectedQuotientNondegenerateProjectionScalarSocket

    selectedFiniteProjectionScalarFirstFieldInhabited :
      Bool

    selectedFiniteProjectionScalarFirstFieldInhabited-v :
      selectedFiniteProjectionScalarFirstFieldInhabited ≡ true

    selectedFiniteProjectionScalarFirstField :
      SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    selectedFiniteProjectionScalarFirstFieldIsPhysicalLaws :
      selectedFiniteProjectionScalarFirstField
      ≡
      SQD.physicalNondegenerateProjectionScalarLawsField

    selectedFiniteProjectionScalarProgressIsLocalOnly :
      Bool

    selectedFiniteProjectionScalarProgressIsLocalOnly-v :
      selectedFiniteProjectionScalarProgressIsLocalOnly ≡ true

    globalPhysicalProjectionScalarFieldPromoted :
      Bool

    globalPhysicalProjectionScalarFieldPromoted-v :
      globalPhysicalProjectionScalarFieldPromoted ≡ false

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFirstField :
      List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFirstFieldAreCanonical :
      remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFirstField
      ≡
      canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteFirstField

    nextMissingProjectionScalarTheoremField :
      SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    nextMissingProjectionScalarTheoremFieldIsQuotientInnerProductWellDefinedness :
      nextMissingProjectionScalarTheoremField
      ≡
      SQD.quotientInnerProductWellDefinednessField

    remainingProjectionScalarTheoremFieldsAfterNextMissing :
      List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    remainingProjectionScalarTheoremFieldsAfterNextMissingAreCanonical :
      remainingProjectionScalarTheoremFieldsAfterNextMissing
      ≡
      canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteSecondField

    nextMissingPrimitiveName :
      String

    socketBoundary :
      List String

open SelectedQuotientPostProjectionScalarSocket public

selectedQuotientPostProjectionScalarSocket :
  SelectedQuotientPostProjectionScalarSocket
selectedQuotientPostProjectionScalarSocket =
  record
    { selectedQuotientNondegenerateProjectionScalarSocketReceipt =
        selectedQuotientNondegenerateProjectionScalarSocket
    ; selectedFiniteProjectionScalarFirstFieldInhabited =
        true
    ; selectedFiniteProjectionScalarFirstFieldInhabited-v =
        refl
    ; selectedFiniteProjectionScalarFirstField =
        SQD.physicalNondegenerateProjectionScalarLawsField
    ; selectedFiniteProjectionScalarFirstFieldIsPhysicalLaws =
        refl
    ; selectedFiniteProjectionScalarProgressIsLocalOnly =
        true
    ; selectedFiniteProjectionScalarProgressIsLocalOnly-v =
        refl
    ; globalPhysicalProjectionScalarFieldPromoted =
        false
    ; globalPhysicalProjectionScalarFieldPromoted-v =
        refl
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFirstField =
        canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteFirstField
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFirstFieldAreCanonical =
        refl
    ; nextMissingProjectionScalarTheoremField =
        SQD.quotientInnerProductWellDefinednessField
    ; nextMissingProjectionScalarTheoremFieldIsQuotientInnerProductWellDefinedness =
        refl
    ; remainingProjectionScalarTheoremFieldsAfterNextMissing =
        canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteSecondField
    ; remainingProjectionScalarTheoremFieldsAfterNextMissingAreCanonical =
        refl
    ; nextMissingPrimitiveName =
        "Representative-independent quotient inner-product law compatible with the selected finite projection/scalar witness"
    ; socketBoundary =
        "SelectedQuotientProjectionInnerProductSurface now supplies a selected finite two-point projection/scalar witness with representative-independent quotient inner-product transport"
        ∷ "This record marks the first theorem field (physicalNondegenerateProjectionScalarLawsField) as inhabited on the selected finite quotient lane only"
        ∷ "The progress is intentionally local and non-promoting: it does not promote a global physical nondegenerate projection/scalar algebra"
        ∷ "The next exact theorem field is quotientInnerProductWellDefinednessField, followed by globalPhysicalQuotientInnerProductWellDefinednessField and acceptedHilbertCompletionField"
        ∷ []
    }

record SelectedQuotientPostInnerProductWellDefinednessSocket : Setω where
  field
    selectedQuotientPostProjectionScalarSocketReceipt :
      SelectedQuotientPostProjectionScalarSocket

    selectedFiniteProjectionScalarSecondFieldInhabited :
      Bool

    selectedFiniteProjectionScalarSecondFieldInhabited-v :
      selectedFiniteProjectionScalarSecondFieldInhabited ≡ true

    selectedFiniteProjectionScalarSecondField :
      SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    selectedFiniteProjectionScalarSecondFieldIsInnerProductWellDefinedness :
      selectedFiniteProjectionScalarSecondField
      ≡
      SQD.quotientInnerProductWellDefinednessField

    selectedFiniteInnerProductWellDefinednessProgressIsLocalOnly :
      Bool

    selectedFiniteInnerProductWellDefinednessProgressIsLocalOnly-v :
      selectedFiniteInnerProductWellDefinednessProgressIsLocalOnly ≡ true

    globalQuotientInnerProductWellDefinednessPromoted :
      Bool

    globalQuotientInnerProductWellDefinednessPromoted-v :
      globalQuotientInnerProductWellDefinednessPromoted ≡ false

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteSecondField :
      List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteSecondFieldAreCanonical :
      remainingProjectionScalarTheoremFieldsAfterSelectedFiniteSecondField
      ≡
      canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteSecondField

    nextMissingProjectionScalarTheoremField :
      SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    nextMissingProjectionScalarTheoremFieldIsGlobalPhysicalQuotientInnerProductWellDefinedness :
      nextMissingProjectionScalarTheoremField
      ≡
      SQD.globalPhysicalQuotientInnerProductWellDefinednessField

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField :
      List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteThirdFieldAreCanonical :
      remainingProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField
      ≡
      canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField

    nextMissingPrimitiveName :
      String

    socketBoundary :
      List String

open SelectedQuotientPostInnerProductWellDefinednessSocket public

selectedQuotientPostInnerProductWellDefinednessSocket :
  SelectedQuotientPostInnerProductWellDefinednessSocket
selectedQuotientPostInnerProductWellDefinednessSocket =
  record
    { selectedQuotientPostProjectionScalarSocketReceipt =
        selectedQuotientPostProjectionScalarSocket
    ; selectedFiniteProjectionScalarSecondFieldInhabited =
        true
    ; selectedFiniteProjectionScalarSecondFieldInhabited-v =
        refl
    ; selectedFiniteProjectionScalarSecondField =
        SQD.quotientInnerProductWellDefinednessField
    ; selectedFiniteProjectionScalarSecondFieldIsInnerProductWellDefinedness =
        refl
    ; selectedFiniteInnerProductWellDefinednessProgressIsLocalOnly =
        true
    ; selectedFiniteInnerProductWellDefinednessProgressIsLocalOnly-v =
        refl
    ; globalQuotientInnerProductWellDefinednessPromoted =
        false
    ; globalQuotientInnerProductWellDefinednessPromoted-v =
        refl
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteSecondField =
        canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteSecondField
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteSecondFieldAreCanonical =
        refl
    ; nextMissingProjectionScalarTheoremField =
        SQD.globalPhysicalQuotientInnerProductWellDefinednessField
    ; nextMissingProjectionScalarTheoremFieldIsGlobalPhysicalQuotientInnerProductWellDefinedness =
        refl
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField =
        canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteThirdFieldAreCanonical =
        refl
    ; nextMissingPrimitiveName =
        "Global physical quotient inner-product well-definedness witness after selected finite local inner-product progress"
    ; socketBoundary =
        "This record marks the second theorem field (quotientInnerProductWellDefinednessField) as inhabited on the selected finite quotient lane only"
        ∷ "The selected finite witness remains local and non-promoting: it does not claim global physical quotient inner-product well-definedness"
        ∷ "The next exact theorem field is globalPhysicalQuotientInnerProductWellDefinednessField, followed by acceptedHilbertCompletionField"
        ∷ []
    }

selectedFiniteQuotientFormalLift :
  U.WaveLift
    selectedFiniteQuotientTower
    selectedFiniteQuotientHilbertSpace
selectedFiniteQuotientFormalLift =
  record
    { Ω =
        ⊤
    ; embed =
        λ q → q
    ; U =
        λ _ q → q
    ; Hgen =
        ⊤
    }

selectedFiniteQuotientFormalGenerator :
  selectedFiniteQuotientCarrier →
  selectedFiniteQuotientCarrier
selectedFiniteQuotientFormalGenerator q =
  q

selectedFiniteQuotientFormalDistance :
  selectedFiniteQuotientCarrier →
  selectedFiniteQuotientCarrier →
  U.ℝ
selectedFiniteQuotientFormalDistance _ _ =
  U.toℝ 0

selectedFiniteQuotientFormalSelfAdjoint :
  Stone.StoneSelfAdjoint
    selectedFiniteQuotientHilbertSpace
    selectedFiniteQuotientFormalGenerator
selectedFiniteQuotientFormalSelfAdjoint =
  record
    { symmetric =
        λ _ _ → refl
    }

selectedFiniteQuotientFormalStoneGroup :
  Stone.StoneGroup selectedFiniteQuotientFormalLift
selectedFiniteQuotientFormalStoneGroup =
  record
    { identity =
        λ _ → refl
    ; composition =
        λ _ _ _ → refl
    }

selectedFiniteQuotientFormalDeltaPositive :
  U._<ℝ_ (U.toℝ 0) (U.toℝ 1)
selectedFiniteQuotientFormalDeltaPositive =
  s≤s z≤n

selectedFiniteQuotientFormalContinuity :
  Stone.StoneContinuity
    (U.WaveLift.U selectedFiniteQuotientFormalLift)
    selectedFiniteQuotientFormalDistance
selectedFiniteQuotientFormalContinuity =
  record
    { continuity =
        λ _ ε ε-positive →
          U.toℝ 1 ,
          selectedFiniteQuotientFormalDeltaPositive ,
          λ _ → ε-positive
    }

selectedFiniteQuotientFormalStoneBundle :
  Stone.StoneBundle
    selectedFiniteQuotientTower
    selectedFiniteQuotientHilbertSpace
selectedFiniteQuotientFormalStoneBundle =
  record
    { lift =
        selectedFiniteQuotientFormalLift
    ; generator =
        selectedFiniteQuotientFormalGenerator
    ; distance =
        selectedFiniteQuotientFormalDistance
    ; self-adjoint =
        selectedFiniteQuotientFormalSelfAdjoint
    ; stone-group =
        selectedFiniteQuotientFormalStoneGroup
    ; strong-continuity =
        selectedFiniteQuotientFormalContinuity
    }

selectedFiniteQuotientFormalStoneRoute :
  StoneBundleSelfAdjointRoute
    selectedFiniteQuotientTower
    selectedFiniteQuotientHilbertSpace
selectedFiniteQuotientFormalStoneRoute =
  stoneBundleSelfAdjointRoute
    selectedFiniteQuotientTower
    selectedFiniteQuotientHilbertSpace
    selectedFiniteQuotientFormalStoneBundle

selectedFiniteQuotientZeroExtensionIota :
  (d : Nat) →
  selectedFiniteQuotientCarrier →
  selectedFiniteQuotientCarrier
selectedFiniteQuotientZeroExtensionIota _ q =
  q

selectedFiniteQuotientZeroExtensionIota-isometry :
  (d : Nat) →
  (q r : selectedFiniteQuotientCarrier) →
  U.HilbertSpace.⟨_,_⟩
    selectedFiniteQuotientHilbertSpace
    (selectedFiniteQuotientZeroExtensionIota d q)
    (selectedFiniteQuotientZeroExtensionIota d r)
  ≡
  U.HilbertSpace.⟨_,_⟩ selectedFiniteQuotientHilbertSpace q r
selectedFiniteQuotientZeroExtensionIota-isometry _ _ _ =
  refl

selectedFiniteQuotientZeroExtensionIota-U-compatible :
  (d : Nat) →
  (t : U.ℝ) →
  (q : selectedFiniteQuotientCarrier) →
  selectedFiniteQuotientZeroExtensionIota d
    (U.WaveLift.U selectedFiniteQuotientFormalLift t q)
  ≡
  U.WaveLift.U selectedFiniteQuotientFormalLift t
    (selectedFiniteQuotientZeroExtensionIota d q)
selectedFiniteQuotientZeroExtensionIota-U-compatible _ _ _ =
  refl

selectedFiniteQuotientHilbertInductiveLimitTransitions :
  Stone.HilbertInductiveLimitTransitionSystem
selectedFiniteQuotientHilbertInductiveLimitTransitions =
  record
    { H_d =
        λ _ → selectedFiniteQuotientHilbertSpace
    ; U_d =
        λ _ → U.WaveLift.U selectedFiniteQuotientFormalLift
    ; iota_d =
        selectedFiniteQuotientZeroExtensionIota
    ; iota_d-isometry =
        selectedFiniteQuotientZeroExtensionIota-isometry
    ; iota_d-U-compatible =
        selectedFiniteQuotientZeroExtensionIota-U-compatible
    }

selectedFiniteQuotientStoneHilbertInductiveLimitTransitions :
  Stone.StoneHilbertInductiveLimitTransitionSystem
selectedFiniteQuotientStoneHilbertInductiveLimitTransitions =
  record
    { stoneTower_d =
        λ _ → selectedFiniteQuotientTower
    ; stoneH_d =
        λ _ → selectedFiniteQuotientHilbertSpace
    ; stoneBundle_d =
        λ _ → selectedFiniteQuotientFormalStoneBundle
    ; stoneIota_d =
        selectedFiniteQuotientZeroExtensionIota
    ; stoneIota_d-isometry =
        selectedFiniteQuotientZeroExtensionIota-isometry
    ; stoneIota_d-U-compatible =
        selectedFiniteQuotientZeroExtensionIota-U-compatible
    }

selectedFiniteQuotientProjectionHilbertSpace :
  U.HilbertSpace
selectedFiniteQuotientProjectionHilbertSpace =
  record
    { H =
        selectedFiniteQuotientCarrier
    ; ⟨_,_⟩ =
        selectedFiniteQuotientProjectionInner
    }

selectedFiniteQuotientProjectionDiscreteDepthSystem :
  Stone.DiscreteTimeHilbertDepthEmbeddingSystem
selectedFiniteQuotientProjectionDiscreteDepthSystem =
  record
    { H_d =
        λ _ → selectedFiniteQuotientProjectionHilbertSpace
    ; Ustep_d =
        λ _ _ q → q
    ; iota_d =
        λ _ q → q
    ; iota_d-isometry =
        λ _ _ _ → refl
    ; Ustep-zero =
        λ _ _ → refl
    ; iota_d-Ustep-compatible =
        λ _ _ _ → refl
    }

selectedFiniteQuotientProjectionFiniteSupportColimitDomain :
  Nat →
  Stone.FinitelySupportedDepthColimitDomain
    selectedFiniteQuotientProjectionDiscreteDepthSystem
selectedFiniteQuotientProjectionFiniteSupportColimitDomain depth =
  record
    { supportDepth =
        depth
    ; supportVector =
        selectedQuotientPointFromPrecursorBool true
    ; finiteSupportWitness =
        ⊤
    ; successorShadow =
        selectedQuotientPointFromPrecursorBool true
    ; successorShadowIsIota =
        refl
    ; colimitDomainOnly =
        true
    ; colimitDomainOnly-v =
        refl
    ; completedHilbertColimitPromoted =
        true
    ; completedHilbertColimitPromoted-v =
        refl
    ; domainBoundary =
        "Finite-support carrier witness for the selected quotient projection-inner-product fixed-depth system"
        ∷ "supportDepth is the requested fixed depth and supportVector is a concrete selected quotient point"
        ∷ "The successor shadow is exactly iota_d of that support vector in the identity depth embedding"
        ∷ "This is a finite-support domain witness only; completedHilbertColimitPromoted is true"
        ∷ []
    }

selectedFiniteQuotientProjectionDiscreteGenerator :
  (d : Nat) →
  U.HilbertSpace.H
    (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
      selectedFiniteQuotientProjectionDiscreteDepthSystem
      d) →
  U.HilbertSpace.H
    (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
      selectedFiniteQuotientProjectionDiscreteDepthSystem
      d)
selectedFiniteQuotientProjectionDiscreteGenerator _ q =
  q

selectedFiniteQuotientProjectionDiscreteGeneratorDomain :
  (d : Nat) →
  U.HilbertSpace.H
    (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
      selectedFiniteQuotientProjectionDiscreteDepthSystem
      d) →
  Set
selectedFiniteQuotientProjectionDiscreteGeneratorDomain _ _ =
  ⊤

selectedFiniteQuotientProjectionDiscreteGeneratorPreservesDomain :
  (d : Nat) →
  (q :
    U.HilbertSpace.H
      (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
        selectedFiniteQuotientProjectionDiscreteDepthSystem
        d)) →
  selectedFiniteQuotientProjectionDiscreteGeneratorDomain d q →
  selectedFiniteQuotientProjectionDiscreteGeneratorDomain
    d
    (selectedFiniteQuotientProjectionDiscreteGenerator d q)
selectedFiniteQuotientProjectionDiscreteGeneratorPreservesDomain _ _ _ =
  tt

selectedFiniteQuotientProjectionDiscreteGeneratorIotaCompatible :
  (d : Nat) →
  (q :
    U.HilbertSpace.H
      (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
        selectedFiniteQuotientProjectionDiscreteDepthSystem
        d)) →
  Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
    selectedFiniteQuotientProjectionDiscreteDepthSystem
    d
    (selectedFiniteQuotientProjectionDiscreteGenerator d q)
  ≡
  selectedFiniteQuotientProjectionDiscreteGenerator
    (suc d)
    (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
      selectedFiniteQuotientProjectionDiscreteDepthSystem
      d
      q)
selectedFiniteQuotientProjectionDiscreteGeneratorIotaCompatible _ _ =
  refl

selectedFiniteQuotientProjectionDiscreteGeneratorSymmetricOnDomain :
  (d : Nat) →
  (q r :
    U.HilbertSpace.H
      (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
        selectedFiniteQuotientProjectionDiscreteDepthSystem
        d)) →
  selectedFiniteQuotientProjectionDiscreteGeneratorDomain d q →
  selectedFiniteQuotientProjectionDiscreteGeneratorDomain d r →
  U.HilbertSpace.⟨_,_⟩
    (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
      selectedFiniteQuotientProjectionDiscreteDepthSystem
      d)
    (selectedFiniteQuotientProjectionDiscreteGenerator d q)
    r
  ≡
  U.HilbertSpace.⟨_,_⟩
    (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
      selectedFiniteQuotientProjectionDiscreteDepthSystem
      d)
    q
    (selectedFiniteQuotientProjectionDiscreteGenerator d r)
selectedFiniteQuotientProjectionDiscreteGeneratorSymmetricOnDomain _ _ _ _ _ =
  refl

selectedFiniteQuotientProjectionDiscreteGeneratorDomainStableUnderStep :
  (d n : Nat) →
  (q :
    U.HilbertSpace.H
      (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
        selectedFiniteQuotientProjectionDiscreteDepthSystem
        d)) →
  selectedFiniteQuotientProjectionDiscreteGeneratorDomain d q →
  selectedFiniteQuotientProjectionDiscreteGeneratorDomain
    d
    (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d
      selectedFiniteQuotientProjectionDiscreteDepthSystem
      d
      n
      q)
selectedFiniteQuotientProjectionDiscreteGeneratorDomainStableUnderStep _ _ _ _ =
  tt

selectedFiniteQuotientProjectionDiscreteGeneratorCommutesWithStepOnDomain :
  (d n : Nat) →
  (q :
    U.HilbertSpace.H
      (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
        selectedFiniteQuotientProjectionDiscreteDepthSystem
        d)) →
  selectedFiniteQuotientProjectionDiscreteGeneratorDomain d q →
  selectedFiniteQuotientProjectionDiscreteGenerator
    d
    (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d
      selectedFiniteQuotientProjectionDiscreteDepthSystem
      d
      n
      q)
  ≡
  Stone.DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d
    selectedFiniteQuotientProjectionDiscreteDepthSystem
    d
    n
    (selectedFiniteQuotientProjectionDiscreteGenerator d q)
selectedFiniteQuotientProjectionDiscreteGeneratorCommutesWithStepOnDomain _ _ _ _ =
  refl

selectedFiniteQuotientProjectionDiscreteGeneratorDomainTarget :
  Stone.DiscreteGeneratorDomainTarget
    selectedFiniteQuotientProjectionDiscreteDepthSystem
selectedFiniteQuotientProjectionDiscreteGeneratorDomainTarget =
  record
    { generator_d =
        selectedFiniteQuotientProjectionDiscreteGenerator
    ; generatorDomain_d =
        selectedFiniteQuotientProjectionDiscreteGeneratorDomain
    ; generatorPreservesDomain =
        selectedFiniteQuotientProjectionDiscreteGeneratorPreservesDomain
    ; generatorIotaCompatible =
        selectedFiniteQuotientProjectionDiscreteGeneratorIotaCompatible
    ; targetOnly =
        true
    ; targetOnly-v =
        refl
    ; selfAdjointGeneratorPromoted =
        false
    ; selfAdjointGeneratorPromoted-v =
        refl
    ; generatorBoundary =
        "Selected finite quotient projection generator target: identity generator at every depth"
        ∷ "The domain predicate is inhabited and iota-compatibility is definitional for the identity embedding"
        ∷ "This is selected finite quotient progress only; it is not a self-adjoint physical colimit generator"
        ∷ "selfAdjointGeneratorPromoted is fixed false"
        ∷ []
    }

selectedFiniteQuotientProjectionDiscreteSymmetricGeneratorDomainTarget :
  Stone.DiscreteSymmetricGeneratorDomainTarget
    selectedFiniteQuotientProjectionDiscreteDepthSystem
selectedFiniteQuotientProjectionDiscreteSymmetricGeneratorDomainTarget =
  record
    { generatorDomainTarget =
        selectedFiniteQuotientProjectionDiscreteGeneratorDomainTarget
    ; generatorSymmetricOnDomain =
        selectedFiniteQuotientProjectionDiscreteGeneratorSymmetricOnDomain
    ; generatorDomainStableUnderStep =
        selectedFiniteQuotientProjectionDiscreteGeneratorDomainStableUnderStep
    ; generatorCommutesWithStepOnDomain =
        selectedFiniteQuotientProjectionDiscreteGeneratorCommutesWithStepOnDomain
    ; finiteDepthSymmetryOnly =
        true
    ; finiteDepthSymmetryOnly-v =
        refl
    ; selfAdjointColimitGeneratorPromoted =
        false
    ; selfAdjointColimitGeneratorPromoted-v =
        refl
    ; symmetryBoundary =
        "Selected finite quotient symmetric-generator target for the identity finite-depth projection system"
        ∷ "Symmetry, step-domain stability, and generator/step commutation hold by refl for the finite identity system"
        ∷ "This remains finite-depth interpretation data and does not promote a self-adjoint colimit generator"
        ∷ "selfAdjointColimitGeneratorPromoted is fixed false"
        ∷ []
    }

selectedFiniteQuotientProjectionDiscreteTimeHilbertDepthStoneReceipt :
  Stone.DiscreteTimeHilbertDepthStoneReceipt
selectedFiniteQuotientProjectionDiscreteTimeHilbertDepthStoneReceipt =
  record
    { depthSystem =
        selectedFiniteQuotientProjectionDiscreteDepthSystem
    ; finiteSupportColimitDomain =
        selectedFiniteQuotientProjectionFiniteSupportColimitDomain 0
    ; discreteGeneratorDomainTarget =
        selectedFiniteQuotientProjectionDiscreteGeneratorDomainTarget
    ; symmetricGeneratorDomainTarget =
        selectedFiniteQuotientProjectionDiscreteSymmetricGeneratorDomainTarget
    ; discreteStrongContinuityIsIdentityAtZero =
        true
    ; discreteStrongContinuityIsIdentityAtZero-v =
        refl
    ; continuousL2CompletionPromoted =
        false
    ; continuousL2CompletionPromoted-v =
        refl
    ; finiteSupportColimitDomainPromoted =
        false
    ; finiteSupportColimitDomainPromoted-v =
        refl
    ; selfAdjointColimitGeneratorPromoted =
        false
    ; selfAdjointColimitGeneratorPromoted-v =
        refl
    ; remainingPrimitives =
        Stone.canonicalHilbertDepthStoneMissingPrimitives
    ; remainingPrimitivesAreCanonical =
        refl
    ; receiptBoundary =
        "Selected finite quotient discrete-time Hilbert/Stone receipt over the projection inner product"
        ∷ "It packages the selected quotient finite-depth system, a depth-0 finite-support witness, and the identity generator/symmetric-generator targets"
        ∷ "The receipt is bounded to selected finite quotient progress and keeps continuousL2CompletionPromoted, finiteSupportColimitDomainPromoted, and selfAdjointColimitGeneratorPromoted false"
        ∷ "The canonical global Hilbert/Stone missing primitives remain unchanged"
        ∷ []
    }

selectedFiniteQuotientStoneGeneratorSpectralGapInterpretationReceipt :
  Stone.BoundedStoneGeneratorSpectralGapInterpretationReceipt
selectedFiniteQuotientStoneGeneratorSpectralGapInterpretationReceipt =
  record
    { finiteDepthStoneReceipt =
        selectedFiniteQuotientProjectionDiscreteTimeHilbertDepthStoneReceipt
    ; finiteDepthGeneratorTarget =
        selectedFiniteQuotientProjectionDiscreteGeneratorDomainTarget
    ; finiteDepthGeneratorTargetIsReceiptTarget =
        refl
    ; finiteDepthSymmetricGeneratorTarget =
        selectedFiniteQuotientProjectionDiscreteSymmetricGeneratorDomainTarget
    ; finiteDepthSymmetricGeneratorTargetIsReceiptTarget =
        refl
    ; selectedFiniteQuotientProgressTyped =
        true
    ; selectedFiniteQuotientProgressTyped-v =
        refl
    ; boundedStoneGeneratorInterpretationTyped =
        true
    ; boundedStoneGeneratorInterpretationTyped-v =
        refl
    ; boundedSpectralGapInterpretationTyped =
        true
    ; boundedSpectralGapInterpretationTyped-v =
        refl
    ; globalNoncollapsedPhysicalPhaseSpaceSupplied =
        false
    ; globalNoncollapsedPhysicalPhaseSpaceSupplied-v =
        refl
    ; traversalDerivedStoneBundleSupplied =
        false
    ; traversalDerivedStoneBundleSupplied-v =
        refl
    ; selfAdjointColimitGeneratorPromoted =
        false
    ; selfAdjointColimitGeneratorPromoted-v =
        refl
    ; receiptSelfAdjointColimitGeneratorPromotedStillFalse =
        refl
    ; realSpectralGapLowerBoundSupplied =
        false
    ; realSpectralGapLowerBoundSupplied-v =
        refl
    ; spectralGapLowerBoundPromoted =
        false
    ; spectralGapLowerBoundPromoted-v =
        refl
    ; clayOrGlobalMassGapPromoted =
        false
    ; clayOrGlobalMassGapPromoted-v =
        refl
    ; firstRemainingTarget =
        Stone.targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstRemainingTargetIsGlobalNoncollapsedPhysicalPhaseSpace =
        refl
    ; remainingTargets =
        Stone.canonicalStoneGeneratorSpectralGapRemainingTargets
    ; remainingTargetsAreCanonical =
        refl
    ; receiptBoundary =
        "Selected finite quotient Stone generator/spectral-gap interpretation receipt"
        ∷ "The selected finite quotient projection system has typed identity generator, symmetric-generator, and finite-support Stone receipt data"
        ∷ "This is bounded non-promoting progress only: no global noncollapsed physical phase space is supplied"
        ∷ "No traversal-derived Stone bundle or self-adjoint colimit generator is supplied"
        ∷ "No real spectral-gap lower bound, global mass-gap theorem, or Clay promotion is supplied"
        ∷ "selfAdjointColimitGeneratorPromoted, spectralGapLowerBoundPromoted, and clayOrGlobalMassGapPromoted are fixed false"
        ∷ []
    }

record FixedDepthHilbertCompletenessSurface : Setω where
  field
    finiteDepth :
      Nat

    fixedDepthSystem :
      Stone.DiscreteTimeHilbertDepthEmbeddingSystem

    fixedDepthInnerProduct :
      U.HilbertSpace.H
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          fixedDepthSystem
          finiteDepth) →
      U.HilbertSpace.H
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          fixedDepthSystem
          finiteDepth) →
      U.ℂ

    fixedDepthFiniteSupportCarrier :
      Stone.FinitelySupportedDepthColimitDomain
        fixedDepthSystem

    fixedDepthFiniteSupportDepthMatches :
      Stone.FinitelySupportedDepthColimitDomain.supportDepth
        fixedDepthFiniteSupportCarrier
      ≡
      finiteDepth

    fixedDepthCompletenessWitness :
      Set

    fixedDepthOnly :
      Bool

    fixedDepthOnly-v :
      fixedDepthOnly ≡ true

    colimitCompletenessClaimed :
      Bool

    colimitCompletenessClaimed-v :
      colimitCompletenessClaimed ≡ false

    physicalLimitClaimed :
      Bool

    physicalLimitClaimed-v :
      physicalLimitClaimed ≡ false

    surfaceBoundary :
      List String

open FixedDepthHilbertCompletenessSurface public

selectedFiniteDepthHilbertCompletenessSurface :
  Nat →
  FixedDepthHilbertCompletenessSurface
selectedFiniteDepthHilbertCompletenessSurface depth =
  record
    { finiteDepth =
        depth
    ; fixedDepthSystem =
        selectedFiniteQuotientProjectionDiscreteDepthSystem
    ; fixedDepthInnerProduct =
        U.HilbertSpace.⟨_,_⟩
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            depth)
    ; fixedDepthFiniteSupportCarrier =
        selectedFiniteQuotientProjectionFiniteSupportColimitDomain depth
    ; fixedDepthFiniteSupportDepthMatches =
        refl
    ; fixedDepthCompletenessWitness =
        ⊤
    ; fixedDepthOnly =
        true
    ; fixedDepthOnly-v =
        refl
    ; colimitCompletenessClaimed =
        false
    ; colimitCompletenessClaimed-v =
        refl
    ; physicalLimitClaimed =
        false
    ; physicalLimitClaimed-v =
        refl
    ; surfaceBoundary =
        "Fixed-depth completeness surface now carries an explicit depth-indexed H_d system on the selected finite quotient carrier"
        ∷ "fixedDepthInnerProduct is taken from that system (the selected quotient projection inner-product surface)"
        ∷ "fixedDepthFiniteSupportCarrier supplies a concrete finite-support colimit-domain carrier at the chosen depth"
        ∷ "fixedDepthCompletenessWitness is unit evidence for the finite receipt surface, not a topological completion theorem"
        ∷ "colimitCompletenessClaimed and physicalLimitClaimed are fixed false"
        ∷ "No Hilbert colimit, physical continuum limit, Stone promotion, self-adjoint Hamiltonian, or Schrodinger closure follows"
        ∷ []
    }

record SelectedQuotientHilbertTopologyCompletionSurface : Setω where
  field
    projectionInnerProductSurface :
      SelectedQuotientProjectionInnerProductSurface

    selectedCarrier :
      Set

    selectedCarrierIsQuotient :
      selectedCarrier ≡ selectedFiniteQuotientCarrier

    selectedInnerProduct :
      selectedFiniteQuotientCarrier →
      selectedFiniteQuotientCarrier →
      U.ℂ

    selectedInnerProductIsProjectionInnerProduct :
      (q r : selectedFiniteQuotientCarrier) →
      selectedInnerProduct q r
      ≡
      SelectedQuotientProjectionInnerProductSurface.quotientInnerProduct
        projectionInnerProductSurface
        q
        r

    selectedInnerProductRepresentativeIndependent :
      {ψ ψ′ χ χ′ :
        QS.Carrier
          (SQD.advanceWavePhaseObservationKernelSetoid
            SQD.shiftWavePhaseSelectedObservationKernelPrimitive)} →
      QS._≈_
        (SQD.advanceWavePhaseObservationKernelSetoid
          SQD.shiftWavePhaseSelectedObservationKernelPrimitive)
        ψ
        ψ′ →
      QS._≈_
        (SQD.advanceWavePhaseObservationKernelSetoid
          SQD.shiftWavePhaseSelectedObservationKernelPrimitive)
        χ
        χ′ →
      selectedInnerProduct
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          ψ)
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          χ)
      ≡
      selectedInnerProduct
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          ψ′)
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          χ′)

    finiteTopologyWitness :
      Set

    finiteTopologyWitnessInhabited :
      finiteTopologyWitness

    finiteCompletionWitness :
      Set

    finiteCompletionWitnessInhabited :
      finiteCompletionWitness

    finiteSelectedQuotientOnly :
      Bool

    finiteSelectedQuotientOnly-v :
      finiteSelectedQuotientOnly ≡ true

    physicalHilbertCompletionPromoted :
      Bool

    physicalHilbertCompletionPromoted-v :
      physicalHilbertCompletionPromoted ≡ false

    physicalStrongContinuityPromoted :
      Bool

    physicalStrongContinuityPromoted-v :
      physicalStrongContinuityPromoted ≡ false

    surfaceBoundary :
      List String

open SelectedQuotientHilbertTopologyCompletionSurface public

selectedQuotientHilbertTopologyCompletionSurface :
  SelectedQuotientHilbertTopologyCompletionSurface
selectedQuotientHilbertTopologyCompletionSurface =
  record
    { projectionInnerProductSurface =
        selectedQuotientProjectionInnerProductSurface
    ; selectedCarrier =
        selectedFiniteQuotientCarrier
    ; selectedCarrierIsQuotient =
        refl
    ; selectedInnerProduct =
        SelectedQuotientProjectionInnerProductSurface.quotientInnerProduct
          selectedQuotientProjectionInnerProductSurface
    ; selectedInnerProductIsProjectionInnerProduct =
        λ _ _ → refl
    ; selectedInnerProductRepresentativeIndependent =
        SelectedQuotientProjectionInnerProductSurface.quotientInnerProductWellDefined
          selectedQuotientProjectionInnerProductSurface
    ; finiteTopologyWitness =
        ⊤
    ; finiteTopologyWitnessInhabited =
        tt
    ; finiteCompletionWitness =
        ⊤
    ; finiteCompletionWitnessInhabited =
        tt
    ; finiteSelectedQuotientOnly =
        true
    ; finiteSelectedQuotientOnly-v =
        refl
    ; physicalHilbertCompletionPromoted =
        false
    ; physicalHilbertCompletionPromoted-v =
        refl
    ; physicalStrongContinuityPromoted =
        false
    ; physicalStrongContinuityPromoted-v =
        refl
    ; surfaceBoundary =
        "The selected finite quotient now has a typed topology/completion precursor tied to the projection inner product surface"
        ∷ "Representative independence is consumed from SelectedQuotientProjectionInnerProductSurface.quotientInnerProductWellDefined"
        ∷ "finiteTopologyWitness and finiteCompletionWitness are finite selected-quotient witnesses only"
        ∷ "No physical Hilbert completion, density theorem, strong-continuity topology, traversal-derived StoneBundle, or Schrodinger promotion follows"
        ∷ []
    }

record SelectedQuotientFiniteDensitySocket : Setω where
  field
    selectedQuotientTopologyCompletionSurface :
      SelectedQuotientHilbertTopologyCompletionSurface

    denseCore :
      Set

    denseCoreIsSelectedQuotientCarrier :
      denseCore ≡ selectedFiniteQuotientCarrier

    denseCoreToCompletion :
      selectedFiniteQuotientCarrier →
      selectedFiniteQuotientCarrier

    completionToDenseCore :
      selectedFiniteQuotientCarrier →
      selectedFiniteQuotientCarrier

    denseCoreRoundTrip :
      (q : selectedFiniteQuotientCarrier) →
      completionToDenseCore (denseCoreToCompletion q)
      ≡
      q

    finiteApproximation :
      selectedFiniteQuotientCarrier →
      selectedFiniteQuotientCarrier

    finiteApproximationExact :
      (q : selectedFiniteQuotientCarrier) →
      finiteApproximation q
      ≡
      q

    finiteDensityWitnessAvailable :
      Bool

    finiteDensityWitnessAvailable-v :
      finiteDensityWitnessAvailable ≡ true

    physicalHilbertDensityPromoted :
      Bool

    physicalHilbertDensityPromoted-v :
      physicalHilbertDensityPromoted ≡ false

    physicalHilbertCompletionPromoted :
      Bool

    physicalHilbertCompletionPromoted-v :
      physicalHilbertCompletionPromoted ≡ false

    firstMissingPrimitiveName :
      String

    socketBoundary :
      List String

open SelectedQuotientFiniteDensitySocket public

selectedQuotientFiniteDensitySocket :
  SelectedQuotientFiniteDensitySocket
selectedQuotientFiniteDensitySocket =
  record
    { selectedQuotientTopologyCompletionSurface =
        selectedQuotientHilbertTopologyCompletionSurface
    ; denseCore =
        selectedFiniteQuotientCarrier
    ; denseCoreIsSelectedQuotientCarrier =
        refl
    ; denseCoreToCompletion =
        λ q → q
    ; completionToDenseCore =
        λ q → q
    ; denseCoreRoundTrip =
        λ _ → refl
    ; finiteApproximation =
        λ q → q
    ; finiteApproximationExact =
        λ _ → refl
    ; finiteDensityWitnessAvailable =
        true
    ; finiteDensityWitnessAvailable-v =
        refl
    ; physicalHilbertDensityPromoted =
        false
    ; physicalHilbertDensityPromoted-v =
        refl
    ; physicalHilbertCompletionPromoted =
        false
    ; physicalHilbertCompletionPromoted-v =
        refl
    ; firstMissingPrimitiveName =
        "Physical Hilbert completion density for the noncollapsed quotient carrier"
    ; socketBoundary =
        "The selected finite quotient now has an explicit dense-core socket: the dense core is the selected quotient carrier itself"
        ∷ "The finite completion precursor is finite, so the approximation and dense-core round trip are identity laws by refl"
        ∷ "This discharges only the finite selected-quotient density socket needed before asking for physical completion density"
        ∷ "It does not construct a noncollapsed physical Hilbert completion, a topological density theorem, a traversal group, or a Stone bundle"
        ∷ "physicalHilbertDensityPromoted and physicalHilbertCompletionPromoted remain false"
        ∷ []
    }

record SelectedFilteredColimitHilbertSocket : Setω where
  field
    selectedQuotientFiniteDensitySocketReceipt :
      SelectedQuotientFiniteDensitySocket

    finiteDepthStoneTowerSkeletonReceipt :
      Stone.FiniteDepthIdentityStoneTowerSkeleton

    finiteDepthStoneTowerSkeletonIsCanonicalOnePoint :
      finiteDepthStoneTowerSkeletonReceipt
      ≡
      Stone.onePointFiniteDepthIdentityStoneTowerSkeleton

    selectedDenseCarrierToFiniteSupportVector :
      selectedFiniteQuotientCarrier →
      U.HilbertSpace.H
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          (Stone.FiniteDepthIdentityStoneTowerSkeleton.discreteIdentityDepthSystem
            finiteDepthStoneTowerSkeletonReceipt)
          (Stone.FinitelySupportedDepthColimitDomain.supportDepth
            (Stone.FiniteDepthIdentityStoneTowerSkeleton.finiteSupportColimitDomain
              finiteDepthStoneTowerSkeletonReceipt)))

    selectedDenseCarrierToFiniteSupportVectorIsCanonical :
      (q : selectedFiniteQuotientCarrier) →
      selectedDenseCarrierToFiniteSupportVector q
      ≡
      Stone.FinitelySupportedDepthColimitDomain.supportVector
        (Stone.FiniteDepthIdentityStoneTowerSkeleton.finiteSupportColimitDomain
          finiteDepthStoneTowerSkeletonReceipt)

    selectedDenseCarrierSuccessorShadowMatches :
      (q : selectedFiniteQuotientCarrier) →
      Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
        (Stone.FiniteDepthIdentityStoneTowerSkeleton.discreteIdentityDepthSystem
          finiteDepthStoneTowerSkeletonReceipt)
        (Stone.FinitelySupportedDepthColimitDomain.supportDepth
          (Stone.FiniteDepthIdentityStoneTowerSkeleton.finiteSupportColimitDomain
            finiteDepthStoneTowerSkeletonReceipt))
        (selectedDenseCarrierToFiniteSupportVector q)
      ≡
      Stone.FinitelySupportedDepthColimitDomain.successorShadow
        (Stone.FiniteDepthIdentityStoneTowerSkeleton.finiteSupportColimitDomain
          finiteDepthStoneTowerSkeletonReceipt)

    filteredColimitCarrierProgressIsLocalOnly :
      Bool

    filteredColimitCarrierProgressIsLocalOnly-v :
      filteredColimitCarrierProgressIsLocalOnly ≡ true

    denseDomainProgressIsLocalOnly :
      Bool

    denseDomainProgressIsLocalOnly-v :
      denseDomainProgressIsLocalOnly ≡ true

    physicalFilteredColimitHilbertPromoted :
      Bool

    physicalFilteredColimitHilbertPromoted-v :
      physicalFilteredColimitHilbertPromoted ≡ false

    nextMissingPrimitiveName :
      String

    socketBoundary :
      List String

open SelectedFilteredColimitHilbertSocket public

selectedFilteredColimitHilbertSocket :
  SelectedFilteredColimitHilbertSocket
selectedFilteredColimitHilbertSocket =
  record
    { selectedQuotientFiniteDensitySocketReceipt =
        selectedQuotientFiniteDensitySocket
    ; finiteDepthStoneTowerSkeletonReceipt =
        Stone.onePointFiniteDepthIdentityStoneTowerSkeleton
    ; finiteDepthStoneTowerSkeletonIsCanonicalOnePoint =
        refl
    ; selectedDenseCarrierToFiniteSupportVector =
        λ _ → tt
    ; selectedDenseCarrierToFiniteSupportVectorIsCanonical =
        λ _ → refl
    ; selectedDenseCarrierSuccessorShadowMatches =
        λ _ → refl
    ; filteredColimitCarrierProgressIsLocalOnly =
        true
    ; filteredColimitCarrierProgressIsLocalOnly-v =
        refl
    ; denseDomainProgressIsLocalOnly =
        true
    ; denseDomainProgressIsLocalOnly-v =
        refl
    ; physicalFilteredColimitHilbertPromoted =
        false
    ; physicalFilteredColimitHilbertPromoted-v =
        refl
    ; nextMissingPrimitiveName =
        "Global physical filtered-colimit Hilbert carrier with noncollapsed dense-domain/completion bridge"
    ; socketBoundary =
        "SelectedQuotientFiniteDensitySocket supplies the finite dense-core identity approximation on the selected quotient carrier"
        ∷ "This socket adds an explicit bridge from each selected dense-core point to the canonical finite-support colimit witness in Stone.onePointFiniteDepthIdentityStoneTowerSkeleton"
        ∷ "The bridge is finite/local only: it lands in the one-point finite-support witness and does not claim a physical filtered-colimit Hilbert carrier"
        ∷ "No noncollapsed colimit completion, physical dense-domain theorem, or traversal-derived Stone bundle is supplied"
        ∷ "filteredColimitCarrierProgressIsLocalOnly and denseDomainProgressIsLocalOnly are true; physicalFilteredColimitHilbertPromoted is fixed false"
        ∷ []
    }

record SelectedQuotientPostGlobalInnerProductWellDefinednessSocket : Setω where
  field
    selectedQuotientPostInnerProductWellDefinednessSocketReceipt :
      SelectedQuotientPostInnerProductWellDefinednessSocket

    selectedFilteredColimitHilbertSocketReceipt :
      SelectedFilteredColimitHilbertSocket

    selectedFixedDepthHilbertCompletenessSurfaceReceipt :
      FixedDepthHilbertCompletenessSurface

    selectedQuotientHilbertTopologyCompletionSurfaceReceipt :
      SelectedQuotientHilbertTopologyCompletionSurface

    selectedFiniteProjectionScalarThirdFieldInhabited :
      Bool

    selectedFiniteProjectionScalarThirdFieldInhabited-v :
      selectedFiniteProjectionScalarThirdFieldInhabited ≡ true

    selectedFiniteProjectionScalarThirdField :
      SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    selectedFiniteProjectionScalarThirdFieldIsGlobalPhysicalQuotientInnerProductWellDefinedness :
      selectedFiniteProjectionScalarThirdField
      ≡
      SQD.globalPhysicalQuotientInnerProductWellDefinednessField

    selectedFiniteGlobalInnerProductWellDefinednessProgressIsLocalOnly :
      Bool

    selectedFiniteGlobalInnerProductWellDefinednessProgressIsLocalOnly-v :
      selectedFiniteGlobalInnerProductWellDefinednessProgressIsLocalOnly ≡ true

    globalPhysicalQuotientInnerProductWellDefinednessPromoted :
      Bool

    globalPhysicalQuotientInnerProductWellDefinednessPromoted-v :
      globalPhysicalQuotientInnerProductWellDefinednessPromoted ≡ false

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField :
      List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteThirdFieldAreCanonical :
      remainingProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField
      ≡
      canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField

    nextMissingProjectionScalarTheoremField :
      SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    nextMissingProjectionScalarTheoremFieldIsAcceptedHilbertCompletion :
      nextMissingProjectionScalarTheoremField
      ≡
      SQD.acceptedHilbertCompletionField

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField :
      List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFourthFieldAreCanonical :
      remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField
      ≡
      canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField

    nextMissingPrimitiveName :
      String

    socketBoundary :
      List String

open SelectedQuotientPostGlobalInnerProductWellDefinednessSocket public

selectedQuotientPostGlobalInnerProductWellDefinednessSocket :
  SelectedQuotientPostGlobalInnerProductWellDefinednessSocket
selectedQuotientPostGlobalInnerProductWellDefinednessSocket =
  record
    { selectedQuotientPostInnerProductWellDefinednessSocketReceipt =
        selectedQuotientPostInnerProductWellDefinednessSocket
    ; selectedFilteredColimitHilbertSocketReceipt =
        selectedFilteredColimitHilbertSocket
    ; selectedFixedDepthHilbertCompletenessSurfaceReceipt =
        selectedFiniteDepthHilbertCompletenessSurface 0
    ; selectedQuotientHilbertTopologyCompletionSurfaceReceipt =
        selectedQuotientHilbertTopologyCompletionSurface
    ; selectedFiniteProjectionScalarThirdFieldInhabited =
        true
    ; selectedFiniteProjectionScalarThirdFieldInhabited-v =
        refl
    ; selectedFiniteProjectionScalarThirdField =
        SQD.globalPhysicalQuotientInnerProductWellDefinednessField
    ; selectedFiniteProjectionScalarThirdFieldIsGlobalPhysicalQuotientInnerProductWellDefinedness =
        refl
    ; selectedFiniteGlobalInnerProductWellDefinednessProgressIsLocalOnly =
        true
    ; selectedFiniteGlobalInnerProductWellDefinednessProgressIsLocalOnly-v =
        refl
    ; globalPhysicalQuotientInnerProductWellDefinednessPromoted =
        false
    ; globalPhysicalQuotientInnerProductWellDefinednessPromoted-v =
        refl
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField =
        canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteThirdField
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteThirdFieldAreCanonical =
        refl
    ; nextMissingProjectionScalarTheoremField =
        SQD.acceptedHilbertCompletionField
    ; nextMissingProjectionScalarTheoremFieldIsAcceptedHilbertCompletion =
        refl
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField =
        canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFourthFieldAreCanonical =
        refl
    ; nextMissingPrimitiveName =
        "Accepted physical Hilbert completion witness after selected finite local global inner-product well-definedness progress"
    ; socketBoundary =
        "This record marks the third theorem field (globalPhysicalQuotientInnerProductWellDefinednessField) as inhabited on the selected finite quotient lane only"
        ∷ "It threads the selected finite filtered-colimit socket plus fixed-depth and topology completion receipts as explicit local Hilbert completion scaffolding"
        ∷ "The selected finite witness remains local and non-promoting: it does not claim global physical quotient inner-product well-definedness promotion"
        ∷ "The next exact theorem field is acceptedHilbertCompletionField"
        ∷ []
    }

record SelectedQuotientPostAcceptedHilbertCompletionSocket : Setω where
  field
    selectedQuotientPostGlobalInnerProductWellDefinednessSocketReceipt :
      SelectedQuotientPostGlobalInnerProductWellDefinednessSocket

    selectedFiniteProjectionScalarFourthFieldInhabited :
      Bool

    selectedFiniteProjectionScalarFourthFieldInhabited-v :
      selectedFiniteProjectionScalarFourthFieldInhabited ≡ true

    selectedFiniteProjectionScalarFourthField :
      SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    selectedFiniteProjectionScalarFourthFieldIsAcceptedHilbertCompletion :
      selectedFiniteProjectionScalarFourthField
      ≡
      SQD.acceptedHilbertCompletionField

    selectedFiniteHilbertCompletionProgressIsLocalOnly :
      Bool

    selectedFiniteHilbertCompletionProgressIsLocalOnly-v :
      selectedFiniteHilbertCompletionProgressIsLocalOnly ≡ true

    acceptedHilbertCompletionPromoted :
      Bool

    acceptedHilbertCompletionPromoted-v :
      acceptedHilbertCompletionPromoted ≡ false

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField :
      List SQD.NondegeneratePhysicalProjectionAlgebraTheoremField

    remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFourthFieldAreCanonical :
      remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField
      ≡
      canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField

    nextMissingPrimitiveName :
      String

    socketBoundary :
      List String

open SelectedQuotientPostAcceptedHilbertCompletionSocket public

selectedQuotientPostAcceptedHilbertCompletionSocket :
  SelectedQuotientPostAcceptedHilbertCompletionSocket
selectedQuotientPostAcceptedHilbertCompletionSocket =
  record
    { selectedQuotientPostGlobalInnerProductWellDefinednessSocketReceipt =
        selectedQuotientPostGlobalInnerProductWellDefinednessSocket
    ; selectedFiniteProjectionScalarFourthFieldInhabited =
        true
    ; selectedFiniteProjectionScalarFourthFieldInhabited-v =
        refl
    ; selectedFiniteProjectionScalarFourthField =
        SQD.acceptedHilbertCompletionField
    ; selectedFiniteProjectionScalarFourthFieldIsAcceptedHilbertCompletion =
        refl
    ; selectedFiniteHilbertCompletionProgressIsLocalOnly =
        true
    ; selectedFiniteHilbertCompletionProgressIsLocalOnly-v =
        refl
    ; acceptedHilbertCompletionPromoted =
        false
    ; acceptedHilbertCompletionPromoted-v =
        refl
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField =
        canonicalNondegenerateProjectionScalarTheoremFieldsAfterSelectedFiniteFourthField
    ; remainingProjectionScalarTheoremFieldsAfterSelectedFiniteFourthFieldAreCanonical =
        refl
    ; nextMissingPrimitiveName =
        "Invertible one-parameter physical traversal automorphism group extending selected finite advance after local accepted Hilbert-completion progress"
    ; socketBoundary =
        "This record marks the fourth theorem field (acceptedHilbertCompletionField) as inhabited on the selected finite quotient lane only"
        ∷ "The selected finite witness is local and non-promoting: no accepted global physical Hilbert completion theorem is claimed"
        ∷ "Projection/scalar theorem fields are now locally exhausted on the selected finite lane; canonical remaining list is []"
        ∷ "The next exact primitive moves to invertible traversal-group and strong-continuity data for a physical Stone bundle route"
        ∷ []
    }

data Gate5SelectedFiniteProjectionScalarRemainingPrimitive : Set where
  remainingAcceptedPhysicalHilbertCompletion :
    Gate5SelectedFiniteProjectionScalarRemainingPrimitive

  remainingInvertiblePhysicalTraversalGroup :
    Gate5SelectedFiniteProjectionScalarRemainingPrimitive

  remainingStrongContinuityForPhysicalTraversal :
    Gate5SelectedFiniteProjectionScalarRemainingPrimitive

  remainingTraversalDerivedStoneBundle :
    Gate5SelectedFiniteProjectionScalarRemainingPrimitive

canonicalGate5SelectedFiniteProjectionScalarRemainingPrimitives :
  List Gate5SelectedFiniteProjectionScalarRemainingPrimitive
canonicalGate5SelectedFiniteProjectionScalarRemainingPrimitives =
  remainingAcceptedPhysicalHilbertCompletion
  ∷ remainingInvertiblePhysicalTraversalGroup
  ∷ remainingStrongContinuityForPhysicalTraversal
  ∷ remainingTraversalDerivedStoneBundle
  ∷ []

record Gate5SelectedFiniteProjectionScalarAuditReceipt : Setω where
  field
    selectedProjectionInnerProductSurfaceReceipt :
      SelectedQuotientProjectionInnerProductSurface

    selectedQuotientNondegenerateProjectionScalarSocketReceipt :
      SelectedQuotientNondegenerateProjectionScalarSocket

    selectedQuotientPostAcceptedHilbertCompletionSocketReceipt :
      SelectedQuotientPostAcceptedHilbertCompletionSocket

    selectedFiniteStoneGeneratorSpectralGapReceipt :
      Stone.BoundedStoneGeneratorSpectralGapInterpretationReceipt

    selectedFiniteProjectionAlgebraSupplied :
      Bool

    selectedFiniteProjectionAlgebraSupplied-v :
      selectedFiniteProjectionAlgebraSupplied ≡ true

    selectedFiniteProjectionScalarFieldsLocallyExhausted :
      Bool

    selectedFiniteProjectionScalarFieldsLocallyExhausted-v :
      selectedFiniteProjectionScalarFieldsLocallyExhausted ≡ true

    globalAcceptedHilbertCompletionPromoted :
      Bool

    globalAcceptedHilbertCompletionPromoted-v :
      globalAcceptedHilbertCompletionPromoted ≡ false

    globalNoncollapsedPhysicalPhaseSpaceSupplied :
      Bool

    globalNoncollapsedPhysicalPhaseSpaceSupplied-v :
      globalNoncollapsedPhysicalPhaseSpaceSupplied ≡ false

    stoneFirstRemainingTarget :
      Stone.StoneGeneratorSpectralGapRemainingTarget

    stoneFirstRemainingTargetIsGlobalNoncollapsedPhysicalPhaseSpace :
      stoneFirstRemainingTarget
      ≡
      Stone.targetGlobalNoncollapsedPhysicalPhaseSpace

    firstRemainingPrimitive :
      Gate5SelectedFiniteProjectionScalarRemainingPrimitive

    firstRemainingPrimitiveIsAcceptedPhysicalHilbertCompletion :
      firstRemainingPrimitive
      ≡
      remainingAcceptedPhysicalHilbertCompletion

    remainingPrimitives :
      List Gate5SelectedFiniteProjectionScalarRemainingPrimitive

    remainingPrimitivesAreCanonical :
      remainingPrimitives
      ≡
      canonicalGate5SelectedFiniteProjectionScalarRemainingPrimitives

    firstRemainingPrimitiveName :
      String

    auditBoundary :
      List String

open Gate5SelectedFiniteProjectionScalarAuditReceipt public

gate5SelectedFiniteProjectionScalarAuditReceipt :
  Gate5SelectedFiniteProjectionScalarAuditReceipt
gate5SelectedFiniteProjectionScalarAuditReceipt =
  record
    { selectedProjectionInnerProductSurfaceReceipt =
        selectedQuotientProjectionInnerProductSurface
    ; selectedQuotientNondegenerateProjectionScalarSocketReceipt =
        selectedQuotientNondegenerateProjectionScalarSocket
    ; selectedQuotientPostAcceptedHilbertCompletionSocketReceipt =
        selectedQuotientPostAcceptedHilbertCompletionSocket
    ; selectedFiniteStoneGeneratorSpectralGapReceipt =
        selectedFiniteQuotientStoneGeneratorSpectralGapInterpretationReceipt
    ; selectedFiniteProjectionAlgebraSupplied =
        true
    ; selectedFiniteProjectionAlgebraSupplied-v =
        refl
    ; selectedFiniteProjectionScalarFieldsLocallyExhausted =
        true
    ; selectedFiniteProjectionScalarFieldsLocallyExhausted-v =
        refl
    ; globalAcceptedHilbertCompletionPromoted =
        false
    ; globalAcceptedHilbertCompletionPromoted-v =
        refl
    ; globalNoncollapsedPhysicalPhaseSpaceSupplied =
        false
    ; globalNoncollapsedPhysicalPhaseSpaceSupplied-v =
        refl
    ; stoneFirstRemainingTarget =
        Stone.targetGlobalNoncollapsedPhysicalPhaseSpace
    ; stoneFirstRemainingTargetIsGlobalNoncollapsedPhysicalPhaseSpace =
        refl
    ; firstRemainingPrimitive =
        remainingAcceptedPhysicalHilbertCompletion
    ; firstRemainingPrimitiveIsAcceptedPhysicalHilbertCompletion =
        refl
    ; remainingPrimitives =
        canonicalGate5SelectedFiniteProjectionScalarRemainingPrimitives
    ; remainingPrimitivesAreCanonical =
        refl
    ; firstRemainingPrimitiveName =
        "Accepted physical Hilbert completion over a noncollapsed physical phase-space carrier"
    ; auditBoundary =
        "The selected finite quotient projection/scalar lane has a representative-independent finite projection inner product"
        ∷ "The selected finite projection/scalar theorem fields are locally exhausted by the post-accepted-completion socket"
        ∷ "This audit is local only: acceptedHilbertCompletionPromoted and globalNoncollapsedPhysicalPhaseSpaceSupplied remain false"
        ∷ "The Stone bounded receipt still reports targetGlobalNoncollapsedPhysicalPhaseSpace as its first remaining target"
        ∷ "After accepted physical Hilbert completion, the remaining physical route still needs an invertible traversal group, strong continuity, and a traversal-derived StoneBundle"
        ∷ []
    }

record SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure : Setω where
  field
    depthSystem :
      Stone.DiscreteTimeHilbertDepthEmbeddingSystem

    depthSystemIsSelectedProjection :
      depthSystem
      ≡
      selectedFiniteQuotientProjectionDiscreteDepthSystem

    forwardStep :
      (d n : Nat) →
      U.HilbertSpace.H
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d) →
      U.HilbertSpace.H
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d)

    forwardStepIsSelectedUstep :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      forwardStep d n q
      ≡
      Stone.DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d
        selectedFiniteQuotientProjectionDiscreteDepthSystem
        d
        n
        q

    reverseStep :
      (d n : Nat) →
      U.HilbertSpace.H
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d) →
      U.HilbertSpace.H
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d)

    reverseStepIsIdentity :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      reverseStep d n q
      ≡
      q

    forwardReverseInverse :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      reverseStep d n (forwardStep d n q)
      ≡
      q

    reverseForwardInverse :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      forwardStep d n (reverseStep d n q)
      ≡
      q

    reverseStepIotaCompatible :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
        selectedFiniteQuotientProjectionDiscreteDepthSystem
        d
        (reverseStep d n q)
      ≡
      reverseStep
        (suc d)
        n
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d
          q)

    finiteSupportDomain :
      Stone.FinitelySupportedDepthColimitDomain
        selectedFiniteQuotientProjectionDiscreteDepthSystem

    generatorDomainTarget :
      Stone.DiscreteGeneratorDomainTarget
        selectedFiniteQuotientProjectionDiscreteDepthSystem

    generatorDomainTargetIsSelectedIdentity :
      generatorDomainTarget
      ≡
      selectedFiniteQuotientProjectionDiscreteGeneratorDomainTarget

    symmetricGeneratorDomainTarget :
      Stone.DiscreteSymmetricGeneratorDomainTarget
        selectedFiniteQuotientProjectionDiscreteDepthSystem

    symmetricGeneratorDomainTargetIsSelectedIdentity :
      symmetricGeneratorDomainTarget
      ≡
      selectedFiniteQuotientProjectionDiscreteSymmetricGeneratorDomainTarget

    generatorDomainClosedUnderForward :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        q →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        (forwardStep d n q)

    generatorDomainClosedUnderReverse :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        q →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        (reverseStep d n q)

    generatorCommutesWithForwardOnDomain :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        q →
      Stone.DiscreteGeneratorDomainTarget.generator_d
        generatorDomainTarget
        d
        (forwardStep d n q)
      ≡
      forwardStep
        d
        n
        (Stone.DiscreteGeneratorDomainTarget.generator_d
          generatorDomainTarget
          d
          q)

    generatorCommutesWithReverseOnDomain :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        q →
      Stone.DiscreteGeneratorDomainTarget.generator_d
        generatorDomainTarget
        d
        (reverseStep d n q)
      ≡
      reverseStep
        d
        n
        (Stone.DiscreteGeneratorDomainTarget.generator_d
          generatorDomainTarget
          d
          q)

    depthGeneratorSelfAdjoint :
      (d : Nat) →
      Stone.StoneSelfAdjoint
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d)
        (Stone.DiscreteGeneratorDomainTarget.generator_d
          generatorDomainTarget
          d)

    finiteReversibleTraversalClosureTyped :
      Bool

    finiteReversibleTraversalClosureTyped-v :
      finiteReversibleTraversalClosureTyped ≡ true

    finiteSelfAdjointGeneratorDomainClosureTyped :
      Bool

    finiteSelfAdjointGeneratorDomainClosureTyped-v :
      finiteSelfAdjointGeneratorDomainClosureTyped ≡ true

    selectedIrreversibleAdvancePromotedToReversible :
      Bool

    selectedIrreversibleAdvancePromotedToReversible-v :
      selectedIrreversibleAdvancePromotedToReversible ≡ false

    physicalStonePromotion :
      Bool

    physicalStonePromotion-v :
      physicalStonePromotion ≡ false

    closureBoundary :
      List String

open SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure public

selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure :
  SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure =
  record
    { depthSystem =
        selectedFiniteQuotientProjectionDiscreteDepthSystem
    ; depthSystemIsSelectedProjection =
        refl
    ; forwardStep =
        λ _ _ q → q
    ; forwardStepIsSelectedUstep =
        λ _ _ _ → refl
    ; reverseStep =
        λ _ _ q → q
    ; reverseStepIsIdentity =
        λ _ _ _ → refl
    ; forwardReverseInverse =
        λ _ _ _ → refl
    ; reverseForwardInverse =
        λ _ _ _ → refl
    ; reverseStepIotaCompatible =
        λ _ _ _ → refl
    ; finiteSupportDomain =
        selectedFiniteQuotientProjectionFiniteSupportColimitDomain 0
    ; generatorDomainTarget =
        selectedFiniteQuotientProjectionDiscreteGeneratorDomainTarget
    ; generatorDomainTargetIsSelectedIdentity =
        refl
    ; symmetricGeneratorDomainTarget =
        selectedFiniteQuotientProjectionDiscreteSymmetricGeneratorDomainTarget
    ; symmetricGeneratorDomainTargetIsSelectedIdentity =
        refl
    ; generatorDomainClosedUnderForward =
        λ _ _ _ _ → tt
    ; generatorDomainClosedUnderReverse =
        λ _ _ _ _ → tt
    ; generatorCommutesWithForwardOnDomain =
        λ _ _ _ _ → refl
    ; generatorCommutesWithReverseOnDomain =
        λ _ _ _ _ → refl
    ; depthGeneratorSelfAdjoint =
        λ _ →
          record
            { symmetric =
                λ _ _ → refl
            }
    ; finiteReversibleTraversalClosureTyped =
        true
    ; finiteReversibleTraversalClosureTyped-v =
        refl
    ; finiteSelfAdjointGeneratorDomainClosureTyped =
        true
    ; finiteSelfAdjointGeneratorDomainClosureTyped-v =
        refl
    ; selectedIrreversibleAdvancePromotedToReversible =
        false
    ; selectedIrreversibleAdvancePromotedToReversible-v =
        refl
    ; physicalStonePromotion =
        false
    ; physicalStonePromotion-v =
        refl
    ; closureBoundary =
        "Selected finite quotient reversible traversal closure is inhabited for the identity depth traversal, with explicit forward/reverse inverse laws at every finite depth"
        ∷ "The reverse identity step is compatible with the selected quotient identity depth embedding"
        ∷ "The selected identity generator domain is closed under both forward and reverse finite steps, and the generator commutes with both steps on that domain"
        ∷ "Each finite-depth selected quotient projection Hilbert space carries a StoneSelfAdjoint witness for the identity generator"
        ∷ "This is not a promotion of selectedFiniteQuotientAdvanceTraversal: that current advance remains the irreversible start -> next -> held table"
        ∷ "No physical Stone bundle, physical one-parameter traversal group, or Schrodinger evolution is promoted"
        ∷ []
    }

record Gate5HilbertStonePhaseSpaceCarrierStep : Setω where
  field
    projectionScalarAuditReceipt :
      Gate5SelectedFiniteProjectionScalarAuditReceipt

    noncollapsedPrecursor :
      Stone.NoncollapsedProjectionAlgebraPrecursor

    noncollapsedPrecursorIsTwoPoint :
      noncollapsedPrecursor
      ≡
      Stone.twoPointNoncollapsedProjectionAlgebraPrecursor

    quotientProjectionInnerProductSurfaceReceipt :
      SelectedQuotientProjectionInnerProductSurface

    phaseSpaceCarrier :
      Set

    phaseSpaceCarrierIsSelectedQuotient :
      phaseSpaceCarrier ≡ selectedFiniteQuotientCarrier

    quotientHilbertSpace :
      U.HilbertSpace

    quotientHilbertSpaceUsesProjectionInnerProduct :
      quotientHilbertSpace
      ≡
      selectedFiniteQuotientProjectionHilbertSpace

    quotientInnerProduct :
      selectedFiniteQuotientCarrier →
      selectedFiniteQuotientCarrier →
      U.ℂ

    quotientInnerProductIsSelectedProjectionInner :
      (q r : selectedFiniteQuotientCarrier) →
      quotientInnerProduct q r
      ≡
      selectedFiniteQuotientProjectionInner q r

    quotientInnerProductRepresentativeIndependent :
      {ψ ψ′ χ χ′ :
        QS.Carrier
          (SQD.advanceWavePhaseObservationKernelSetoid
            SQD.shiftWavePhaseSelectedObservationKernelPrimitive)} →
      QS._≈_
        (SQD.advanceWavePhaseObservationKernelSetoid
          SQD.shiftWavePhaseSelectedObservationKernelPrimitive)
        ψ
        ψ′ →
      QS._≈_
        (SQD.advanceWavePhaseObservationKernelSetoid
          SQD.shiftWavePhaseSelectedObservationKernelPrimitive)
        χ
        χ′ →
      quotientInnerProduct
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          ψ)
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          χ)
      ≡
      quotientInnerProduct
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          ψ′)
        (QS.quotientClass
          SQD.shiftWavePhaseSelectedObservationQuotientSurface
          χ′)

    keptPhaseSpaceState :
      selectedFiniteQuotientCarrier

    orthogonalPhaseSpaceState :
      selectedFiniteQuotientCarrier

    keptPhaseSpaceNorm :
      quotientInnerProduct keptPhaseSpaceState keptPhaseSpaceState
      ≡
      U.toℝ 1

    keptOrthogonalSeparation :
      quotientInnerProduct keptPhaseSpaceState orthogonalPhaseSpaceState
      ≡
      U.toℝ 0

    finiteDepthSystem :
      Stone.DiscreteTimeHilbertDepthEmbeddingSystem

    finiteDepthSystemIsSelectedProjection :
      finiteDepthSystem
      ≡
      selectedFiniteQuotientProjectionDiscreteDepthSystem

    finiteDepthEmbeddingIsometry :
      (d : Nat) →
      (q r :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      U.HilbertSpace.⟨_,_⟩
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          (suc d))
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d
          q)
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d
          r)
      ≡
      U.HilbertSpace.⟨_,_⟩
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d)
        q
        r

    finiteTraversalCompatibility :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
        selectedFiniteQuotientProjectionDiscreteDepthSystem
        d
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d
          n
          q)
      ≡
      Stone.DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d
        selectedFiniteQuotientProjectionDiscreteDepthSystem
        (suc d)
        n
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d
          q)

    finiteSupportDomain :
      Stone.FinitelySupportedDepthColimitDomain
        selectedFiniteQuotientProjectionDiscreteDepthSystem

    finiteSupportDomainIsSelectedDepth0 :
      finiteSupportDomain
      ≡
      selectedFiniteQuotientProjectionFiniteSupportColimitDomain 0

    generatorDomainTarget :
      Stone.DiscreteGeneratorDomainTarget
        selectedFiniteQuotientProjectionDiscreteDepthSystem

    generatorDomainTargetIsSelectedIdentity :
      generatorDomainTarget
      ≡
      selectedFiniteQuotientProjectionDiscreteGeneratorDomainTarget

    symmetricGeneratorDomainTarget :
      Stone.DiscreteSymmetricGeneratorDomainTarget
        selectedFiniteQuotientProjectionDiscreteDepthSystem

    symmetricGeneratorDomainTargetIsSelectedIdentity :
      symmetricGeneratorDomainTarget
      ≡
      selectedFiniteQuotientProjectionDiscreteSymmetricGeneratorDomainTarget

    reversibleTraversalSelfAdjointDomainClosureReceipt :
      SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure

    finitePhaseSpaceCarrierStepTyped :
      Bool

    finitePhaseSpaceCarrierStepTyped-v :
      finitePhaseSpaceCarrierStepTyped ≡ true

    quotientInnerProductStepTyped :
      Bool

    quotientInnerProductStepTyped-v :
      quotientInnerProductStepTyped ≡ true

    generatorDomainDataStepTyped :
      Bool

    generatorDomainDataStepTyped-v :
      generatorDomainDataStepTyped ≡ true

    physicalPhaseSpaceCarrierPromoted :
      Bool

    physicalPhaseSpaceCarrierPromoted-v :
      physicalPhaseSpaceCarrierPromoted ≡ false

    physicalStoneBundlePromoted :
      Bool

    physicalStoneBundlePromoted-v :
      physicalStoneBundlePromoted ≡ false

    selfAdjointPhysicalGeneratorPromoted :
      Bool

    selfAdjointPhysicalGeneratorPromoted-v :
      selfAdjointPhysicalGeneratorPromoted ≡ false

    nextMissingPrimitiveName :
      String

    stepBoundary :
      List String

open Gate5HilbertStonePhaseSpaceCarrierStep public

gate5HilbertStonePhaseSpaceCarrierStep :
  Gate5HilbertStonePhaseSpaceCarrierStep
gate5HilbertStonePhaseSpaceCarrierStep =
  record
    { projectionScalarAuditReceipt =
        gate5SelectedFiniteProjectionScalarAuditReceipt
    ; noncollapsedPrecursor =
        Stone.twoPointNoncollapsedProjectionAlgebraPrecursor
    ; noncollapsedPrecursorIsTwoPoint =
        refl
    ; quotientProjectionInnerProductSurfaceReceipt =
        selectedQuotientProjectionInnerProductSurface
    ; phaseSpaceCarrier =
        selectedFiniteQuotientCarrier
    ; phaseSpaceCarrierIsSelectedQuotient =
        refl
    ; quotientHilbertSpace =
        selectedFiniteQuotientProjectionHilbertSpace
    ; quotientHilbertSpaceUsesProjectionInnerProduct =
        refl
    ; quotientInnerProduct =
        selectedFiniteQuotientProjectionInner
    ; quotientInnerProductIsSelectedProjectionInner =
        λ _ _ → refl
    ; quotientInnerProductRepresentativeIndependent =
        selectedFiniteQuotientProjectionInnerWellDefined
    ; keptPhaseSpaceState =
        SPTI.shiftStartPoint
    ; orthogonalPhaseSpaceState =
        SPTI.shiftHeldExitPoint
    ; keptPhaseSpaceNorm =
        refl
    ; keptOrthogonalSeparation =
        refl
    ; finiteDepthSystem =
        selectedFiniteQuotientProjectionDiscreteDepthSystem
    ; finiteDepthSystemIsSelectedProjection =
        refl
    ; finiteDepthEmbeddingIsometry =
        Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d-isometry
          selectedFiniteQuotientProjectionDiscreteDepthSystem
    ; finiteTraversalCompatibility =
        Stone.DiscreteTimeHilbertDepthEmbeddingSystem.iota_d-Ustep-compatible
          selectedFiniteQuotientProjectionDiscreteDepthSystem
    ; finiteSupportDomain =
        selectedFiniteQuotientProjectionFiniteSupportColimitDomain 0
    ; finiteSupportDomainIsSelectedDepth0 =
        refl
    ; generatorDomainTarget =
        selectedFiniteQuotientProjectionDiscreteGeneratorDomainTarget
    ; generatorDomainTargetIsSelectedIdentity =
        refl
    ; symmetricGeneratorDomainTarget =
        selectedFiniteQuotientProjectionDiscreteSymmetricGeneratorDomainTarget
    ; symmetricGeneratorDomainTargetIsSelectedIdentity =
        refl
    ; reversibleTraversalSelfAdjointDomainClosureReceipt =
        selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
    ; finitePhaseSpaceCarrierStepTyped =
        true
    ; finitePhaseSpaceCarrierStepTyped-v =
        refl
    ; quotientInnerProductStepTyped =
        true
    ; quotientInnerProductStepTyped-v =
        refl
    ; generatorDomainDataStepTyped =
        true
    ; generatorDomainDataStepTyped-v =
        refl
    ; physicalPhaseSpaceCarrierPromoted =
        false
    ; physicalPhaseSpaceCarrierPromoted-v =
        refl
    ; physicalStoneBundlePromoted =
        false
    ; physicalStoneBundlePromoted-v =
        refl
    ; selfAdjointPhysicalGeneratorPromoted =
        false
    ; selfAdjointPhysicalGeneratorPromoted-v =
        refl
    ; nextMissingPrimitiveName =
        "Accepted noncollapsed physical phase-space carrier with reversible traversal and self-adjoint generator-domain closure"
    ; stepBoundary =
        "Gate5HilbertStonePhaseSpaceCarrierStep packages the selected finite quotient carrier as the current phase-space carrier step"
        ∷ "The carrier is tied to the two-point noncollapsed precursor through SelectedQuotientProjectionInnerProductSurface and keeps kept/orthogonal states separated by the selected projection inner product"
        ∷ "Representative independence is the existing quotientSound-based selectedFiniteQuotientProjectionInnerWellDefined proof"
        ∷ "The finite-depth system reuses selectedFiniteQuotientProjectionDiscreteDepthSystem: identity iota is isometric and compatible with every identity traversal step"
        ∷ "The finite-support colimit-domain, generator-domain, and symmetric generator-domain targets are the existing selected finite quotient Stone targets"
        ∷ "SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure adds explicit inverse laws for the identity finite traversal and a finite-depth StoneSelfAdjoint witness for the selected identity generator"
        ∷ "This is a typed finite phase-space carrier/domain step only; physicalPhaseSpaceCarrierPromoted, physicalStoneBundlePromoted, and selfAdjointPhysicalGeneratorPromoted are fixed false"
        ∷ []
    }

record Gate5HilbertStoneTraversalDomainClosureWiring : Setω where
  field
    carrierStepReceipt :
      Gate5HilbertStonePhaseSpaceCarrierStep

    closureReceipt :
      SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure

    closureDepthSystemIsCarrierStepDepthSystem :
      SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.depthSystem
        closureReceipt
      ≡
      Gate5HilbertStonePhaseSpaceCarrierStep.finiteDepthSystem
        carrierStepReceipt

    closureGeneratorDomainTargetIsCarrierStepTarget :
      SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
        closureReceipt
      ≡
      Gate5HilbertStonePhaseSpaceCarrierStep.generatorDomainTarget
        carrierStepReceipt

    closureSymmetricTargetIsCarrierStepTarget :
      SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.symmetricGeneratorDomainTarget
        closureReceipt
      ≡
      Gate5HilbertStonePhaseSpaceCarrierStep.symmetricGeneratorDomainTarget
        carrierStepReceipt

    carrierStepForwardReverseInverse :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.reverseStep
        closureReceipt
        d
        n
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.forwardStep
          closureReceipt
          d
          n
          q)
      ≡
      q

    carrierStepReverseForwardInverse :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.forwardStep
        closureReceipt
        d
        n
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.reverseStep
          closureReceipt
          d
          n
          q)
      ≡
      q

    carrierStepDepthGeneratorSelfAdjoint :
      (d : Nat) →
      Stone.StoneSelfAdjoint
        (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
          selectedFiniteQuotientProjectionDiscreteDepthSystem
          d)
        (Stone.DiscreteGeneratorDomainTarget.generator_d
          (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
            closureReceipt)
          d)

    carrierStepDomainClosedUnderForward :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
          closureReceipt)
        d
        q →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
          closureReceipt)
        d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.forwardStep
          closureReceipt
          d
          n
          q)

    carrierStepDomainClosedUnderReverse :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
          closureReceipt)
        d
        q →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
          closureReceipt)
        d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.reverseStep
          closureReceipt
          d
          n
          q)

    carrierStepGeneratorCommutesWithForward :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
          closureReceipt)
        d
        q →
      Stone.DiscreteGeneratorDomainTarget.generator_d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
          closureReceipt)
        d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.forwardStep
          closureReceipt
          d
          n
          q)
      ≡
      SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.forwardStep
        closureReceipt
        d
        n
        (Stone.DiscreteGeneratorDomainTarget.generator_d
          (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
            closureReceipt)
          d
          q)

    carrierStepGeneratorCommutesWithReverse :
      (d n : Nat) →
      (q :
        U.HilbertSpace.H
          (Stone.DiscreteTimeHilbertDepthEmbeddingSystem.H_d
            selectedFiniteQuotientProjectionDiscreteDepthSystem
            d)) →
      Stone.DiscreteGeneratorDomainTarget.generatorDomain_d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
          closureReceipt)
        d
        q →
      Stone.DiscreteGeneratorDomainTarget.generator_d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
          closureReceipt)
        d
        (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.reverseStep
          closureReceipt
          d
          n
          q)
      ≡
      SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.reverseStep
        closureReceipt
        d
        n
        (Stone.DiscreteGeneratorDomainTarget.generator_d
          (SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainTarget
            closureReceipt)
          d
          q)

    closureWiredThroughGate5Step :
      Bool

    closureWiredThroughGate5Step-v :
      closureWiredThroughGate5Step ≡ true

    finiteTraversalDomainClosureComposed :
      Bool

    finiteTraversalDomainClosureComposed-v :
      finiteTraversalDomainClosureComposed ≡ true

    physicalStonePromotion :
      Bool

    physicalStonePromotion-v :
      physicalStonePromotion ≡ false

    wiringBoundary :
      List String

open Gate5HilbertStoneTraversalDomainClosureWiring public

gate5HilbertStoneTraversalDomainClosureWiring :
  Gate5HilbertStoneTraversalDomainClosureWiring
gate5HilbertStoneTraversalDomainClosureWiring =
  record
    { carrierStepReceipt =
        gate5HilbertStonePhaseSpaceCarrierStep
    ; closureReceipt =
        selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
    ; closureDepthSystemIsCarrierStepDepthSystem =
        refl
    ; closureGeneratorDomainTargetIsCarrierStepTarget =
        refl
    ; closureSymmetricTargetIsCarrierStepTarget =
        refl
    ; carrierStepForwardReverseInverse =
        SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.forwardReverseInverse
          selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
    ; carrierStepReverseForwardInverse =
        SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.reverseForwardInverse
          selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
    ; carrierStepDepthGeneratorSelfAdjoint =
        SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.depthGeneratorSelfAdjoint
          selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
    ; carrierStepDomainClosedUnderForward =
        SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainClosedUnderForward
          selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
    ; carrierStepDomainClosedUnderReverse =
        SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainClosedUnderReverse
          selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
    ; carrierStepGeneratorCommutesWithForward =
        SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorCommutesWithForwardOnDomain
          selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
    ; carrierStepGeneratorCommutesWithReverse =
        SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorCommutesWithReverseOnDomain
          selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
    ; closureWiredThroughGate5Step =
        true
    ; closureWiredThroughGate5Step-v =
        refl
    ; finiteTraversalDomainClosureComposed =
        true
    ; finiteTraversalDomainClosureComposed-v =
        refl
    ; physicalStonePromotion =
        false
    ; physicalStonePromotion-v =
        refl
    ; wiringBoundary =
        "Gate5HilbertStoneTraversalDomainClosureWiring composes the canonical Gate5 phase-space carrier step with its selected finite quotient reversible traversal/domain closure"
        ∷ "The wiring exposes forward/reverse inverse laws through the Gate5 carrier-step receipt rather than as an unconnected local witness"
        ∷ "It re-exports finite-depth StoneSelfAdjoint identity-generator evidence and forward/reverse generator-domain closure for downstream composition consumers"
        ∷ "The selected irreversible finite advance remains outside this reversible identity closure and is not promoted to an invertible traversal"
        ∷ "physicalStonePromotion remains false"
        ∷ []
    }

record PhysicalTraversalStoneUpgradeData : Setω where
  field
    ProjectionAlgebra :
      Set

    quotientInnerProductWellDefined :
      Set

    hilbertCompletion :
      Set

    physicalTower :
      U.Tower

    physicalHilbertSpace :
      U.HilbertSpace

    quotientToHilbert :
      selectedFiniteQuotientCarrier →
      U.HilbertSpace.H physicalHilbertSpace

    physicalUnitary :
      U.ℝ →
      U.HilbertSpace.H physicalHilbertSpace →
      U.HilbertSpace.H physicalHilbertSpace

    physicalStoneBundle :
      Stone.StoneBundle physicalTower physicalHilbertSpace

    physicalStoneBundleUsesTraversal :
      (t : U.ℝ) →
      (x : U.HilbertSpace.H physicalHilbertSpace) →
      Stone.stone-unitary physicalStoneBundle t x
      ≡
      physicalUnitary t x

    traversalExtendsFiniteAdvance :
      (q : selectedFiniteQuotientCarrier) →
      physicalUnitary (U.toℝ 1) (quotientToHilbert q)
      ≡
      quotientToHilbert (SQD.selectedFiniteQuotientAdvanceTraversal q)

    upgradeBoundary :
      List String

open PhysicalTraversalStoneUpgradeData public

physicalTraversalStoneUpgradeRoute :
  (upgradeData : PhysicalTraversalStoneUpgradeData) →
  StoneBundleSelfAdjointRoute
    (PhysicalTraversalStoneUpgradeData.physicalTower upgradeData)
    (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)
physicalTraversalStoneUpgradeRoute upgradeData =
  stoneBundleSelfAdjointRoute
    (PhysicalTraversalStoneUpgradeData.physicalTower upgradeData)
    (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)
    (PhysicalTraversalStoneUpgradeData.physicalStoneBundle upgradeData)

record SuppliedStoneSelfAdjointGeneratorRoute
  (upgradeData : PhysicalTraversalStoneUpgradeData)
  : Setω where
  field
    suppliedUpgradeData :
      PhysicalTraversalStoneUpgradeData

    stoneBundle :
      Stone.StoneBundle
        (PhysicalTraversalStoneUpgradeData.physicalTower upgradeData)
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)

    stoneBundleIsSupplied :
      stoneBundle
      ≡
      PhysicalTraversalStoneUpgradeData.physicalStoneBundle upgradeData

    stoneConsequences :
      Stone.StoneConsequences stoneBundle

    selfAdjointGenerator :
      Stone.StoneSelfAdjoint
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)
        (Stone.StoneBundle.generator stoneBundle)

    oneParameterStoneGroup :
      Stone.StoneGroup (Stone.StoneBundle.lift stoneBundle)

    strongContinuity :
      Stone.StoneContinuity
        (Stone.stone-unitary stoneBundle)
        (Stone.stone-distance stoneBundle)

    routeBoundary :
      List String

open SuppliedStoneSelfAdjointGeneratorRoute public

suppliedStoneSelfAdjointGeneratorRoute :
  (upgradeData : PhysicalTraversalStoneUpgradeData) →
  SuppliedStoneSelfAdjointGeneratorRoute upgradeData
suppliedStoneSelfAdjointGeneratorRoute upgradeData =
  record
    { suppliedUpgradeData =
        upgradeData
    ; stoneBundle =
        PhysicalTraversalStoneUpgradeData.physicalStoneBundle upgradeData
    ; stoneBundleIsSupplied =
        refl
    ; stoneConsequences =
        Stone.Stone-theorem
          (PhysicalTraversalStoneUpgradeData.physicalStoneBundle upgradeData)
    ; selfAdjointGenerator =
        Stone.StoneConsequences.stone-self-adjoint
          (Stone.Stone-theorem
            (PhysicalTraversalStoneUpgradeData.physicalStoneBundle upgradeData))
    ; oneParameterStoneGroup =
        Stone.StoneConsequences.stone-group
          (Stone.Stone-theorem
            (PhysicalTraversalStoneUpgradeData.physicalStoneBundle upgradeData))
    ; strongContinuity =
        Stone.StoneConsequences.strong-continuity
          (Stone.Stone-theorem
            (PhysicalTraversalStoneUpgradeData.physicalStoneBundle upgradeData))
    ; routeBoundary =
        "This route consumes supplied PhysicalTraversalStoneUpgradeData"
        ∷ "The self-adjoint generator is read from Stone-theorem consequences of the supplied StoneBundle"
        ∷ "No StoneBundle is constructed from the current finite quotient advance here"
        ∷ "No promotion follows unless the full upgradeData record is supplied"
        ∷ []
    }

record DiscreteOneParameterGroupWrapper
  (upgradeData : PhysicalTraversalStoneUpgradeData)
  : Setω where
  field
    DiscreteTime :
      Set

    discreteIdentity :
      DiscreteTime

    discreteStep :
      DiscreteTime

    discreteCompose :
      DiscreteTime →
      DiscreteTime →
      DiscreteTime

    discreteInverse :
      DiscreteTime →
      DiscreteTime

    discreteLeftInverseLaw :
      (t : DiscreteTime) →
      discreteCompose (discreteInverse t) t
      ≡
      discreteIdentity

    discreteRightInverseLaw :
      (t : DiscreteTime) →
      discreteCompose t (discreteInverse t)
      ≡
      discreteIdentity

    discreteToReal :
      DiscreteTime →
      U.ℝ

    discreteAction :
      DiscreteTime →
      U.HilbertSpace.H
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData) →
      U.HilbertSpace.H
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)

    discreteActionAgreesWithPhysicalUnitary :
      (t : DiscreteTime) →
      (x :
        U.HilbertSpace.H
          (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)) →
      discreteAction t x
      ≡
      PhysicalTraversalStoneUpgradeData.physicalUnitary
        upgradeData
        (discreteToReal t)
        x

    discreteStepIsPhysicalTimeOne :
      discreteToReal discreteStep
      ≡
      U.toℝ 1

    discreteStepExtendsFiniteAdvance :
      (q : selectedFiniteQuotientCarrier) →
      discreteAction
        discreteStep
        (PhysicalTraversalStoneUpgradeData.quotientToHilbert upgradeData q)
      ≡
      PhysicalTraversalStoneUpgradeData.quotientToHilbert
        upgradeData
        (SQD.selectedFiniteQuotientAdvanceTraversal q)

    finiteAdvancePromotedToDiscreteGroup :
      Bool

    finiteAdvancePromotedToDiscreteGroup-v :
      finiteAdvancePromotedToDiscreteGroup ≡ false

    wrapperBoundary :
      List String

open DiscreteOneParameterGroupWrapper public

discreteOneParameterGroupWrapperStoneRoute :
  (upgradeData : PhysicalTraversalStoneUpgradeData) →
  DiscreteOneParameterGroupWrapper upgradeData →
  SuppliedStoneSelfAdjointGeneratorRoute upgradeData
discreteOneParameterGroupWrapperStoneRoute upgradeData _ =
  suppliedStoneSelfAdjointGeneratorRoute upgradeData

record ReversibleIntegerTraversalWrapper
  (upgradeData : PhysicalTraversalStoneUpgradeData)
  : Setω where
  field
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

    integerLeftIdentityLaw :
      (t : ℤ) →
      integerCompose integerIdentity t
      ≡
      t

    integerRightIdentityLaw :
      (t : ℤ) →
      integerCompose t integerIdentity
      ≡
      t

    integerAssociativityLaw :
      (r s t : ℤ) →
      integerCompose (integerCompose r s) t
      ≡
      integerCompose r (integerCompose s t)

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

    integerToReal :
      ℤ →
      U.ℝ

    integerAction :
      ℤ →
      U.HilbertSpace.H
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData) →
      U.HilbertSpace.H
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)

    integerActionIdentityLaw :
      (x :
        U.HilbertSpace.H
          (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)) →
      integerAction integerIdentity x
      ≡
      x

    integerActionCompositionLaw :
      (s t : ℤ) →
      (x :
        U.HilbertSpace.H
          (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)) →
      integerAction (integerCompose s t) x
      ≡
      integerAction s (integerAction t x)

    integerActionAgreesWithPhysicalUnitary :
      (t : ℤ) →
      (x :
        U.HilbertSpace.H
          (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)) →
      integerAction t x
      ≡
      PhysicalTraversalStoneUpgradeData.physicalUnitary
        upgradeData
        (integerToReal t)
        x

    integerStepIsPhysicalTimeOne :
      integerToReal integerStep
      ≡
      U.toℝ 1

    integerStepExtendsFiniteAdvance :
      (q : selectedFiniteQuotientCarrier) →
      integerAction
        integerStep
        (PhysicalTraversalStoneUpgradeData.quotientToHilbert upgradeData q)
      ≡
      PhysicalTraversalStoneUpgradeData.quotientToHilbert
        upgradeData
        (SQD.selectedFiniteQuotientAdvanceTraversal q)

    finiteAdvancePromotedToIntegerGroup :
      Bool

    finiteAdvancePromotedToIntegerGroup-v :
      finiteAdvancePromotedToIntegerGroup ≡ false

    wrapperBoundary :
      List String

open ReversibleIntegerTraversalWrapper public

reversibleIntegerTraversalWrapperStoneRoute :
  (upgradeData : PhysicalTraversalStoneUpgradeData) →
  ReversibleIntegerTraversalWrapper upgradeData →
  SuppliedStoneSelfAdjointGeneratorRoute upgradeData
reversibleIntegerTraversalWrapperStoneRoute upgradeData _ =
  suppliedStoneSelfAdjointGeneratorRoute upgradeData

record ReversibleIntegerTraversalWrapperRequest
  {ℓw ℓr ℓq ℓn : Level}
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn})
  : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    quotientDescentReceipt :
      SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}

    physicalReversibleTraversalSurfaceRequest :
      SQD.PhysicalReversiblePhaseSpaceTraversalSurfaceRequest

    physicalPhaseSpaceStateSurfaceRequest :
      SQD.PhysicalPhaseSpaceStateSurfaceRequest

    suppliedWrapperWouldGiveGeneratorRoute :
      (upgradeData : PhysicalTraversalStoneUpgradeData) →
      ReversibleIntegerTraversalWrapper upgradeData →
      SuppliedStoneSelfAdjointGeneratorRoute upgradeData

    integerCarrierFixedToDataInteger :
      Bool

    integerCarrierFixedToDataInteger-v :
      integerCarrierFixedToDataInteger ≡ true

    integerGroupLawsSupplied :
      Bool

    integerGroupLawsSupplied-v :
      integerGroupLawsSupplied ≡ false

    integerActionSupplied :
      Bool

    integerActionSupplied-v :
      integerActionSupplied ≡ false

    integerActionGroupLawSupplied :
      Bool

    integerActionGroupLawSupplied-v :
      integerActionGroupLawSupplied ≡ false

    integerStepFiniteAdvanceComparisonSupplied :
      Bool

    integerStepFiniteAdvanceComparisonSupplied-v :
      integerStepFiniteAdvanceComparisonSupplied ≡ false

    physicalStoneUpgradeDataSupplied :
      Bool

    physicalStoneUpgradeDataSupplied-v :
      physicalStoneUpgradeDataSupplied ≡ false

    finiteAdvancePromotedToIntegerGroup :
      Bool

    finiteAdvancePromotedToIntegerGroup-v :
      finiteAdvancePromotedToIntegerGroup ≡ false

    firstMissingPrimitiveName :
      String

    requestBoundary :
      List String

open ReversibleIntegerTraversalWrapperRequest public

reversibleIntegerTraversalWrapperRequest :
  {ℓw ℓr ℓq ℓn : Level} →
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}) →
  ReversibleIntegerTraversalWrapperRequest quotientReceipt
reversibleIntegerTraversalWrapperRequest quotientReceipt =
  record
    { requestedInterfaceName =
        "ReversibleIntegerTraversalWrapper"
    ; exactRequiredFields =
        "integer time carrier fixed to Data.Integer.ℤ"
        ∷ "integerIdentity, integerStep, integerCompose, and integerInverse"
        ∷ "left/right identity, associativity, and left/right inverse laws for integerCompose"
        ∷ "integerToReal : ℤ -> Real"
        ∷ "integerAction : ℤ -> H -> H"
        ∷ "integerActionIdentityLaw and integerActionCompositionLaw"
        ∷ "integerActionAgreesWithPhysicalUnitary against supplied PhysicalTraversalStoneUpgradeData"
        ∷ "integerStepIsPhysicalTimeOne"
        ∷ "integerStepExtendsFiniteAdvance through quotientToHilbert"
        ∷ "finiteAdvancePromotedToIntegerGroup fixed false"
        ∷ []
    ; quotientDescentReceipt =
        quotientReceipt
    ; physicalReversibleTraversalSurfaceRequest =
        SQD.physicalReversiblePhaseSpaceTraversalSurfaceRequest
    ; physicalPhaseSpaceStateSurfaceRequest =
        SQD.physicalPhaseSpaceStateSurfaceRequest
    ; suppliedWrapperWouldGiveGeneratorRoute =
        reversibleIntegerTraversalWrapperStoneRoute
    ; integerCarrierFixedToDataInteger =
        true
    ; integerCarrierFixedToDataInteger-v =
        refl
    ; integerGroupLawsSupplied =
        false
    ; integerGroupLawsSupplied-v =
        refl
    ; integerActionSupplied =
        false
    ; integerActionSupplied-v =
        refl
    ; integerActionGroupLawSupplied =
        false
    ; integerActionGroupLawSupplied-v =
        refl
    ; integerStepFiniteAdvanceComparisonSupplied =
        false
    ; integerStepFiniteAdvanceComparisonSupplied-v =
        refl
    ; physicalStoneUpgradeDataSupplied =
        false
    ; physicalStoneUpgradeDataSupplied-v =
        refl
    ; finiteAdvancePromotedToIntegerGroup =
        false
    ; finiteAdvancePromotedToIntegerGroup-v =
        refl
    ; firstMissingPrimitiveName =
        "Integer-time group laws and action laws over supplied physical Stone upgrade data"
    ; requestBoundary =
        "This wrapper fixes the reversible discrete time index to Data.Integer.ℤ but still requires supplied group operations and proofs"
        ∷ "It is intentionally not built from selectedFiniteQuotientAdvanceTraversal, because that finite traversal has no preimage for shiftStartPoint"
        ∷ "The finite advance may only appear as a time-step comparison after quotientToHilbert and a supplied physical action"
        ∷ "The supplied wrapper route consumes PhysicalTraversalStoneUpgradeData; it does not construct a StoneBundle from the current finite quotient data"
        ∷ "No Hilbert, Stone, self-adjoint, unitary, or Schrodinger-equation promotion follows from this request"
        ∷ []
    }

record StormerVerletDiscreteStoneSurface
  (upgradeData : PhysicalTraversalStoneUpgradeData)
  : Setω where
  field
    StormerVerletPhaseSpace :
      Set

    positionCoordinate :
      StormerVerletPhaseSpace →
      selectedFiniteQuotientCarrier

    momentumCoordinate :
      StormerVerletPhaseSpace →
      selectedFiniteQuotientCarrier

    stateToHilbert :
      StormerVerletPhaseSpace →
      U.HilbertSpace.H
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)

    halfKick :
      StormerVerletPhaseSpace →
      StormerVerletPhaseSpace

    drift :
      StormerVerletPhaseSpace →
      StormerVerletPhaseSpace

    secondHalfKick :
      StormerVerletPhaseSpace →
      StormerVerletPhaseSpace

    stormerVerletStep :
      StormerVerletPhaseSpace →
      StormerVerletPhaseSpace

    stormerVerletStepFactorization :
      (x : StormerVerletPhaseSpace) →
      stormerVerletStep x
      ≡
      secondHalfKick (drift (halfKick x))

    stormerVerletReverseStep :
      StormerVerletPhaseSpace →
      StormerVerletPhaseSpace

    stormerVerletLeftInverseLaw :
      (x : StormerVerletPhaseSpace) →
      stormerVerletReverseStep (stormerVerletStep x)
      ≡
      x

    stormerVerletRightInverseLaw :
      (x : StormerVerletPhaseSpace) →
      stormerVerletStep (stormerVerletReverseStep x)
      ≡
      x

    quotientShadow :
      StormerVerletPhaseSpace →
      selectedFiniteQuotientCarrier

    quotientShadowStepLaw :
      (x : StormerVerletPhaseSpace) →
      quotientShadow (stormerVerletStep x)
      ≡
      SQD.selectedFiniteQuotientAdvanceTraversal (quotientShadow x)

    integerTraversalWrapper :
      ReversibleIntegerTraversalWrapper upgradeData

    integerStepTracksStormerVerletStep :
      (x : StormerVerletPhaseSpace) →
      ReversibleIntegerTraversalWrapper.integerAction
        integerTraversalWrapper
        (ReversibleIntegerTraversalWrapper.integerStep integerTraversalWrapper)
        (stateToHilbert x)
      ≡
      stateToHilbert (stormerVerletStep x)

    stoneRouteAvailableFromSuppliedWrapper :
      Bool

    stoneRouteAvailableFromSuppliedWrapper-v :
      stoneRouteAvailableFromSuppliedWrapper ≡ true

    selectedFiniteAdvancePromotedToStormerVerletGroup :
      Bool

    selectedFiniteAdvancePromotedToStormerVerletGroup-v :
      selectedFiniteAdvancePromotedToStormerVerletGroup ≡ false

    surfaceBoundary :
      List String

open StormerVerletDiscreteStoneSurface public

stormerVerletDiscreteStoneSurfaceRoute :
  (upgradeData : PhysicalTraversalStoneUpgradeData) →
  StormerVerletDiscreteStoneSurface upgradeData →
  SuppliedStoneSelfAdjointGeneratorRoute upgradeData
stormerVerletDiscreteStoneSurfaceRoute upgradeData surface =
  reversibleIntegerTraversalWrapperStoneRoute
    upgradeData
    (StormerVerletDiscreteStoneSurface.integerTraversalWrapper surface)

record StormerVerletDiscreteStoneSurfaceRequest
  {ℓw ℓr ℓq ℓn : Level}
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn})
  : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    quotientDescentReceipt :
      SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}

    reversibleIntegerPhaseSpaceRequest :
      SQD.ReversibleIntegerPhaseSpaceAndQuotientInnerProductRequest

    reversibleIntegerTraversalWrapperRequestReceipt :
      ReversibleIntegerTraversalWrapperRequest quotientReceipt

    suppliedSurfaceWouldGiveStoneRoute :
      (upgradeData : PhysicalTraversalStoneUpgradeData) →
      StormerVerletDiscreteStoneSurface upgradeData →
      SuppliedStoneSelfAdjointGeneratorRoute upgradeData

    quotientInnerProductSupplied :
      Bool

    quotientInnerProductSupplied-v :
      quotientInnerProductSupplied ≡ false

    reversibleIntegerActionSupplied :
      Bool

    reversibleIntegerActionSupplied-v :
      reversibleIntegerActionSupplied ≡ false

    stormerVerletFactorizationSupplied :
      Bool

    stormerVerletFactorizationSupplied-v :
      stormerVerletFactorizationSupplied ≡ false

    stormerVerletInverseLawsSupplied :
      Bool

    stormerVerletInverseLawsSupplied-v :
      stormerVerletInverseLawsSupplied ≡ false

    stoneUpgradeDataSupplied :
      Bool

    stoneUpgradeDataSupplied-v :
      stoneUpgradeDataSupplied ≡ false

    selectedFiniteAdvancePromotedToStormerVerletGroup :
      Bool

    selectedFiniteAdvancePromotedToStormerVerletGroup-v :
      selectedFiniteAdvancePromotedToStormerVerletGroup ≡ false

    firstMissingPrimitiveName :
      String

    requestBoundary :
      List String

open StormerVerletDiscreteStoneSurfaceRequest public

stormerVerletDiscreteStoneSurfaceRequest :
  {ℓw ℓr ℓq ℓn : Level} →
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}) →
  StormerVerletDiscreteStoneSurfaceRequest quotientReceipt
stormerVerletDiscreteStoneSurfaceRequest quotientReceipt =
  record
    { requestedInterfaceName =
        "StormerVerletDiscreteStoneSurface"
    ; exactRequiredFields =
        "StormerVerletPhaseSpace : Set"
        ∷ "positionCoordinate and momentumCoordinate into the selected finite quotient carrier"
        ∷ "halfKick, drift, secondHalfKick, and stormerVerletStep with step factorization"
        ∷ "stormerVerletReverseStep with left/right inverse laws on the supplied physical phase space"
        ∷ "quotientShadowStepLaw comparing the supplied step with selectedFiniteQuotientAdvanceTraversal"
        ∷ "ReversibleIntegerTraversalWrapper over supplied PhysicalTraversalStoneUpgradeData"
        ∷ "integerStepTracksStormerVerletStep on the supplied Hilbert carrier"
        ∷ "quotient inner product and well-definedness through ReversibleIntegerPhaseSpaceAndQuotientInnerProductRequest"
        ∷ "selectedFiniteAdvancePromotedToStormerVerletGroup fixed false"
        ∷ []
    ; quotientDescentReceipt =
        quotientReceipt
    ; reversibleIntegerPhaseSpaceRequest =
        SQD.reversibleIntegerPhaseSpaceAndQuotientInnerProductRequest
    ; reversibleIntegerTraversalWrapperRequestReceipt =
        reversibleIntegerTraversalWrapperRequest quotientReceipt
    ; suppliedSurfaceWouldGiveStoneRoute =
        stormerVerletDiscreteStoneSurfaceRoute
    ; quotientInnerProductSupplied =
        false
    ; quotientInnerProductSupplied-v =
        refl
    ; reversibleIntegerActionSupplied =
        false
    ; reversibleIntegerActionSupplied-v =
        refl
    ; stormerVerletFactorizationSupplied =
        false
    ; stormerVerletFactorizationSupplied-v =
        refl
    ; stormerVerletInverseLawsSupplied =
        false
    ; stormerVerletInverseLawsSupplied-v =
        refl
    ; stoneUpgradeDataSupplied =
        false
    ; stoneUpgradeDataSupplied-v =
        refl
    ; selectedFiniteAdvancePromotedToStormerVerletGroup =
        false
    ; selectedFiniteAdvancePromotedToStormerVerletGroup-v =
        refl
    ; firstMissingPrimitiveName =
        "Supplied Störmer-Verlet reversible phase-space step, quotient inner product, reversible ℤ action, and Stone upgrade data"
    ; requestBoundary =
        "This is a supplied-data Störmer-Verlet surface, not a construction from the selected finite advance"
        ∷ "The Störmer-Verlet inverse laws live on the supplied physical phase space; they do not give an inverse for selectedFiniteQuotientAdvanceTraversal"
        ∷ "The finite quotient appears only through quotientShadowStepLaw, so the existing no-preimage obstruction for shiftStartPoint remains intact"
        ∷ "A Stone route is exposed only by consuming a supplied ReversibleIntegerTraversalWrapper and supplied PhysicalTraversalStoneUpgradeData"
        ∷ "No Hilbert, Stone, self-adjoint, unitary, or Schrodinger-equation promotion follows from this request"
        ∷ []
    }

record DiscreteOneParameterGroupWrapperRequest
  {ℓw ℓr ℓq ℓn : Level}
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn})
  : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    quotientDescentReceipt :
      SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}

    physicalReversibleTraversalSurfaceRequest :
      SQD.PhysicalReversiblePhaseSpaceTraversalSurfaceRequest

    finiteAdvanceTraversalSemigroupObstruction :
      SQD.SelectedFiniteAdvanceTraversalSemigroupObstruction

    suppliedWrapperWouldGiveGeneratorRoute :
      (upgradeData : PhysicalTraversalStoneUpgradeData) →
      DiscreteOneParameterGroupWrapper upgradeData →
      SuppliedStoneSelfAdjointGeneratorRoute upgradeData

    discreteTimeGroupSupplied :
      Bool

    discreteTimeGroupSupplied-v :
      discreteTimeGroupSupplied ≡ false

    physicalReversibleTraversalSupplied :
      Bool

    physicalReversibleTraversalSupplied-v :
      physicalReversibleTraversalSupplied ≡ false

    stoneUpgradeDataSupplied :
      Bool

    stoneUpgradeDataSupplied-v :
      stoneUpgradeDataSupplied ≡ false

    finiteAdvancePromotedToGroup :
      Bool

    finiteAdvancePromotedToGroup-v :
      finiteAdvancePromotedToGroup ≡ false

    firstMissingPrimitiveName :
      String

    requestBoundary :
      List String

open DiscreteOneParameterGroupWrapperRequest public

discreteOneParameterGroupWrapperRequest :
  {ℓw ℓr ℓq ℓn : Level} →
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}) →
  DiscreteOneParameterGroupWrapperRequest quotientReceipt
discreteOneParameterGroupWrapperRequest quotientReceipt =
  record
    { requestedInterfaceName =
        "DiscreteOneParameterGroupWrapper"
    ; exactRequiredFields =
        "DiscreteTime carrier with identity, composition, inverse, and inverse laws"
        ∷ "discreteToReal embedding into the Stone time parameter"
        ∷ "discreteAction on the supplied physical Hilbert carrier"
        ∷ "discreteActionAgreesWithPhysicalUnitary against PhysicalTraversalStoneUpgradeData.physicalUnitary"
        ∷ "discreteStepIsPhysicalTimeOne"
        ∷ "discreteStepExtendsFiniteAdvance through quotientToHilbert"
        ∷ "PhysicalTraversalStoneUpgradeData including a StoneBundle"
        ∷ []
    ; quotientDescentReceipt =
        quotientReceipt
    ; physicalReversibleTraversalSurfaceRequest =
        SQD.physicalReversiblePhaseSpaceTraversalSurfaceRequest
    ; finiteAdvanceTraversalSemigroupObstruction =
        SQD.selectedFiniteAdvanceTraversalSemigroupObstruction
    ; suppliedWrapperWouldGiveGeneratorRoute =
        discreteOneParameterGroupWrapperStoneRoute
    ; discreteTimeGroupSupplied =
        false
    ; discreteTimeGroupSupplied-v =
        refl
    ; physicalReversibleTraversalSupplied =
        false
    ; physicalReversibleTraversalSupplied-v =
        refl
    ; stoneUpgradeDataSupplied =
        false
    ; stoneUpgradeDataSupplied-v =
        refl
    ; finiteAdvancePromotedToGroup =
        false
    ; finiteAdvancePromotedToGroup-v =
        refl
    ; firstMissingPrimitiveName =
        "Discrete time group and supplied physical Stone upgrade data"
    ; requestBoundary =
        "The wrapper is a supplied-data interface over a physical traversal and StoneBundle"
        ∷ "It does not reuse the selected finite advance as an invertible group action"
        ∷ "The finite advance remains a shadow/comparison at the discrete step only"
        ∷ "SelectedFiniteAdvanceTraversalSemigroupObstruction keeps finite group promotion false"
        ∷ "No self-adjoint generator route is available from this request until PhysicalTraversalStoneUpgradeData and the discrete wrapper are supplied"
        ∷ []
    }

record PhaseSpacePhysicalTraversalStoneUpgradeAbsenceLedger
  {ℓw ℓr ℓq ℓn : Level}
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn})
  : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    quotientDescentReceipt :
      SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}

    finitePhaseSpaceTraversalObstruction :
      SQD.SelectedFinitePhaseSpaceReversibleTraversalObstruction

    reversibleTraversalCandidateShape :
      Set

    noFiniteReversibleTraversalFromCurrentAdvance :
      SQD.FinitePhaseSpaceReversibleTraversalCandidate →
      ⊥

    suppliedUpgradeDataWouldGiveRoute :
      (upgradeData : PhysicalTraversalStoneUpgradeData) →
      StoneBundleSelfAdjointRoute
        (PhysicalTraversalStoneUpgradeData.physicalTower upgradeData)
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)

    finiteAmplitudePhaseDefinitionsAvailable :
      Bool

    finiteAmplitudePhaseDefinitionsAvailable-v :
      finiteAmplitudePhaseDefinitionsAvailable ≡ true

    finitePhaseSpaceTransportAvailable :
      Bool

    finitePhaseSpaceTransportAvailable-v :
      finitePhaseSpaceTransportAvailable ≡ true

    scalarFieldSupplied :
      Bool

    scalarFieldSupplied-v :
      scalarFieldSupplied ≡ false

    physicalTimeParameterGroupSupplied :
      Bool

    physicalTimeParameterGroupSupplied-v :
      physicalTimeParameterGroupSupplied ≡ false

    normInnerProductWellDefinednessSupplied :
      Bool

    normInnerProductWellDefinednessSupplied-v :
      normInnerProductWellDefinednessSupplied ≡ false

    hilbertCompletionSupplied :
      Bool

    hilbertCompletionSupplied-v :
      hilbertCompletionSupplied ≡ false

    strongContinuityForTraversalSupplied :
      Bool

    strongContinuityForTraversalSupplied-v :
      strongContinuityForTraversalSupplied ≡ false

    physicalStoneUpgradeDataSupplied :
      Bool

    physicalStoneUpgradeDataSupplied-v :
      physicalStoneUpgradeDataSupplied ≡ false

    firstMissingPrimitiveName :
      String

    absenceLedger :
      List String

open PhaseSpacePhysicalTraversalStoneUpgradeAbsenceLedger public

phaseSpacePhysicalTraversalStoneUpgradeAbsenceLedger :
  {ℓw ℓr ℓq ℓn : Level} →
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}) →
  PhaseSpacePhysicalTraversalStoneUpgradeAbsenceLedger quotientReceipt
phaseSpacePhysicalTraversalStoneUpgradeAbsenceLedger quotientReceipt =
  record
    { requestedInterfaceName =
        "PhysicalTraversalStoneUpgradeDataFromPhaseSpaceReversibleTraversal"
    ; exactRequiredFields =
        "Scalar field or accepted physical scalar carrier for the Hilbert quotient"
        ∷ "Physical time parameter group with identity, inverse, and composition laws"
        ∷ "Reversible physical traversal U(t) whose time-1 shadow extends the finite amplitude/phase advance only through an accepted comparison map"
        ∷ "Norm or inner-product well-definedness on quotient representatives"
        ∷ "Hilbert completion or accepted HilbertSpace carrier"
        ∷ "Strong-continuity proof for the physical traversal, not just the finite table"
        ∷ "StoneBundle physicalTower physicalHilbertSpace built from that traversal"
        ∷ []
    ; quotientDescentReceipt =
        quotientReceipt
    ; finitePhaseSpaceTraversalObstruction =
        SQD.selectedFinitePhaseSpaceReversibleTraversalObstruction
    ; reversibleTraversalCandidateShape =
        SQD.FinitePhaseSpaceReversibleTraversalCandidate
    ; noFiniteReversibleTraversalFromCurrentAdvance =
        SQD.selectedFinitePhaseSpaceNoReversibleTraversal
    ; suppliedUpgradeDataWouldGiveRoute =
        physicalTraversalStoneUpgradeRoute
    ; finiteAmplitudePhaseDefinitionsAvailable =
        true
    ; finiteAmplitudePhaseDefinitionsAvailable-v =
        refl
    ; finitePhaseSpaceTransportAvailable =
        true
    ; finitePhaseSpaceTransportAvailable-v =
        refl
    ; scalarFieldSupplied =
        false
    ; scalarFieldSupplied-v =
        refl
    ; physicalTimeParameterGroupSupplied =
        false
    ; physicalTimeParameterGroupSupplied-v =
        refl
    ; normInnerProductWellDefinednessSupplied =
        false
    ; normInnerProductWellDefinednessSupplied-v =
        refl
    ; hilbertCompletionSupplied =
        false
    ; hilbertCompletionSupplied-v =
        refl
    ; strongContinuityForTraversalSupplied =
        false
    ; strongContinuityForTraversalSupplied-v =
        refl
    ; physicalStoneUpgradeDataSupplied =
        false
    ; physicalStoneUpgradeDataSupplied-v =
        refl
    ; firstMissingPrimitiveName =
        "Physical time-parameter group and Hilbert quotient data for a reversible traversal"
    ; absenceLedger =
        "The finite amplitude/phase definitions are available and preserve amplitude-plus-phase across the selected quotient advance"
        ∷ "They do not supply a reversible traversal: the current finite advance has no preimage for shiftStartPoint"
        ∷ "A physical Stone upgrade can only use the finite table as a shadow/comparison target; it still needs an independent invertible U(t)"
        ∷ "No scalar field, physical time group, quotient norm/inner-product well-definedness, Hilbert completion, strong continuity, or traversal-derived StoneBundle is present in the current data"
        ∷ "Supplying PhysicalTraversalStoneUpgradeData remains sufficient to produce StoneBundleSelfAdjointRoute, but that data is absent here"
        ∷ "All Hilbert/Stone/self-adjoint/unitary/Schrodinger promotion flags remain false"
        ∷ []
    }

record SelectedFiniteQuotientStoneAttempt : Setω where
  field
    quotientCarrier :
      Set

    quotientCarrierIsSelectedFiniteCoordinateCarrier :
      quotientCarrier ≡ selectedFiniteQuotientCarrier

    formalStoneBundle :
      Stone.StoneBundle
        selectedFiniteQuotientTower
        selectedFiniteQuotientHilbertSpace

    formalStoneRoute :
      StoneBundleSelfAdjointRoute
        selectedFiniteQuotientTower
        selectedFiniteQuotientHilbertSpace

    hilbertInductiveLimitTransitions :
      Stone.HilbertInductiveLimitTransitionSystem

    stoneHilbertInductiveLimitTransitions :
      Stone.StoneHilbertInductiveLimitTransitionSystem

    finiteAdvanceTraversalSemigroupObstruction :
      SQD.SelectedFiniteAdvanceTraversalSemigroupObstruction

    finiteSelectedQuotientAvailable :
      Bool

    finiteSelectedQuotientAvailable-v :
      finiteSelectedQuotientAvailable ≡ true

    formalBundleConstructedByStoneRecord :
      Bool

    formalBundleConstructedByStoneRecord-v :
      formalBundleConstructedByStoneRecord ≡ true

    formalIotaIsometryConstructed :
      Bool

    formalIotaIsometryConstructed-v :
      formalIotaIsometryConstructed ≡ true

    formalIotaUCompatibilityConstructed :
      Bool

    formalIotaUCompatibilityConstructed-v :
      formalIotaUCompatibilityConstructed ≡ true

    formalBundlePromotesPhysicalHilbertStructure :
      Bool

    formalBundlePromotesPhysicalHilbertStructure-v :
      formalBundlePromotesPhysicalHilbertStructure ≡ false

    formalBundlePromotesPhysicalUnitaryEvolution :
      Bool

    formalBundlePromotesPhysicalUnitaryEvolution-v :
      formalBundlePromotesPhysicalUnitaryEvolution ≡ false

    formalBundlePromotesSchrodingerClosure :
      Bool

    formalBundlePromotesSchrodingerClosure-v :
      formalBundlePromotesSchrodingerClosure ≡ false

    realStoneBundleConstructedFromCurrentData :
      Bool

    realStoneBundleConstructedFromCurrentData-v :
      realStoneBundleConstructedFromCurrentData ≡ false

    firstMissingPrimitiveName :
      String

    exactAbsenceLedger :
      List String

open SelectedFiniteQuotientStoneAttempt public

selectedFiniteQuotientStoneAttempt :
  SelectedFiniteQuotientStoneAttempt
selectedFiniteQuotientStoneAttempt =
  record
    { quotientCarrier =
        selectedFiniteQuotientCarrier
    ; quotientCarrierIsSelectedFiniteCoordinateCarrier =
        refl
    ; formalStoneBundle =
        selectedFiniteQuotientFormalStoneBundle
    ; formalStoneRoute =
        selectedFiniteQuotientFormalStoneRoute
    ; hilbertInductiveLimitTransitions =
        selectedFiniteQuotientHilbertInductiveLimitTransitions
    ; stoneHilbertInductiveLimitTransitions =
        selectedFiniteQuotientStoneHilbertInductiveLimitTransitions
    ; finiteAdvanceTraversalSemigroupObstruction =
        SQD.selectedFiniteAdvanceTraversalSemigroupObstruction
    ; finiteSelectedQuotientAvailable =
        true
    ; finiteSelectedQuotientAvailable-v =
        refl
    ; formalBundleConstructedByStoneRecord =
        true
    ; formalBundleConstructedByStoneRecord-v =
        refl
    ; formalIotaIsometryConstructed =
        true
    ; formalIotaIsometryConstructed-v =
        refl
    ; formalIotaUCompatibilityConstructed =
        true
    ; formalIotaUCompatibilityConstructed-v =
        refl
    ; formalBundlePromotesPhysicalHilbertStructure =
        false
    ; formalBundlePromotesPhysicalHilbertStructure-v =
        refl
    ; formalBundlePromotesPhysicalUnitaryEvolution =
        false
    ; formalBundlePromotesPhysicalUnitaryEvolution-v =
        refl
    ; formalBundlePromotesSchrodingerClosure =
        false
    ; formalBundlePromotesSchrodingerClosure-v =
        refl
    ; realStoneBundleConstructedFromCurrentData =
        false
    ; realStoneBundleConstructedFromCurrentData-v =
        refl
    ; firstMissingPrimitiveName =
        "Physical Hilbert quotient data before real StoneBundle construction"
    ; exactAbsenceLedger =
        "DASHI.Quantum.Stone permits a formal finite record: the selected quotient carrier is used with zero inner product, identity U(t), identity generator, zero distance, trivial group laws, and trivial continuity"
        ∷ "The formal inductive Hilbert transition maps are iota_d = identity from H_d to H_(d+1), with inner-product isometry and U-compatibility by refl"
        ∷ "advanceWavePhaseState does descend to a nontrivial finite quotient traversal, but it is irreversible: shiftStartPoint has no preimage under the descended traversal"
        ∷ "That descended finite traversal is therefore a semigroup/convergence step, not a finite traversal group or Stone one-parameter automorphism group"
        ∷ "That formal record is not promoted as physical Hilbert structure because no nondegenerate projection algebra or quotient inner-product well-definedness is supplied"
        ∷ "It is not promoted as physical unitary evolution because the identity U(t) is not derived from the Schrodinger quotient traversal or a Hamiltonian"
        ∷ "It is not promoted as a real Stone route because no completed Hilbert quotient, one-parameter physical traversal automorphism group, strong-continuity theorem for that traversal, or physical self-adjoint generator is supplied"
        ∷ "The finite selected quotient remains coordinate-only; it witnesses that the record interface can be inhabited, not that Schrodinger closure exists"
        ∷ []
    }

formalIdentityPhysicalReversibleTraversalSurface :
  SQD.PhysicalReversiblePhaseSpaceTraversalSurface
formalIdentityPhysicalReversibleTraversalSurface =
  record
    { PhysicalPhaseSpace =
        ⊤
    ; physicalForwardTraversal =
        λ x → x
    ; physicalInverseTraversal =
        λ x → x
    ; physicalLeftInverseLaw =
        λ _ → refl
    ; physicalRightInverseLaw =
        λ _ → refl
    ; finiteShadow =
        λ _ → SPTI.shiftHeldExitPoint
    ; finiteShadowForwardLaw =
        λ _ → refl
    ; finiteShadowInverseClaimed =
        false
    ; finiteShadowInverseClaimed-v =
        refl
    ; constructedFromCurrentAdvance =
        false
    ; constructedFromCurrentAdvance-v =
        refl
    ; traversalBoundary =
        "Formal physical reversible shadow only: the physical phase space is the one-point carrier with identity forward and inverse traversal"
        ∷ "Its finite shadow is constantly the held endpoint, where the selected finite advance is fixed"
        ∷ "Therefore finiteShadowForwardLaw typechecks without claiming an inverse for the selected finite advance"
        ∷ "This surface is explicitly not constructed from advanceWavePhaseState and not selected as the irreversible finite advance"
        ∷ "No Hilbert, Stone, self-adjoint, unitary, or Schrodinger-equation promotion follows from this shadow alone"
        ∷ []
    }

formalIdentityPhysicalTower :
  U.Tower
formalIdentityPhysicalTower =
  record
    { S =
        λ _ → ⊤
    ; R =
        λ x → x
    ; P =
        λ x → x
    ; C =
        λ x → x
    }

formalIdentityPhysicalHilbertSpace :
  U.HilbertSpace
formalIdentityPhysicalHilbertSpace =
  record
    { H =
        ⊤
    ; ⟨_,_⟩ =
        λ _ _ → U.toℝ 0
    }

formalIdentityPhysicalLift :
  U.WaveLift
    formalIdentityPhysicalTower
    formalIdentityPhysicalHilbertSpace
formalIdentityPhysicalLift =
  record
    { Ω =
        ⊤
    ; embed =
        λ x → x
    ; U =
        λ _ x → x
    ; Hgen =
        ⊤
    }

formalIdentityPhysicalGenerator :
  ⊤ →
  ⊤
formalIdentityPhysicalGenerator x =
  x

formalIdentityPhysicalDistance :
  ⊤ →
  ⊤ →
  U.ℝ
formalIdentityPhysicalDistance _ _ =
  U.toℝ 0

formalIdentityPhysicalSelfAdjoint :
  Stone.StoneSelfAdjoint
    formalIdentityPhysicalHilbertSpace
    formalIdentityPhysicalGenerator
formalIdentityPhysicalSelfAdjoint =
  record
    { symmetric =
        λ _ _ → refl
    }

formalIdentityPhysicalStoneGroup :
  Stone.StoneGroup formalIdentityPhysicalLift
formalIdentityPhysicalStoneGroup =
  record
    { identity =
        λ _ → refl
    ; composition =
        λ _ _ _ → refl
    }

formalIdentityPhysicalDeltaPositive :
  U._<ℝ_ (U.toℝ 0) (U.toℝ 1)
formalIdentityPhysicalDeltaPositive =
  s≤s z≤n

formalIdentityPhysicalContinuity :
  Stone.StoneContinuity
    (U.WaveLift.U formalIdentityPhysicalLift)
    formalIdentityPhysicalDistance
formalIdentityPhysicalContinuity =
  record
    { continuity =
        λ _ ε ε-positive →
          U.toℝ 1 ,
          formalIdentityPhysicalDeltaPositive ,
          λ _ → ε-positive
    }

formalIdentityPhysicalStoneBundle :
  Stone.StoneBundle
    formalIdentityPhysicalTower
    formalIdentityPhysicalHilbertSpace
formalIdentityPhysicalStoneBundle =
  record
    { lift =
        formalIdentityPhysicalLift
    ; generator =
        formalIdentityPhysicalGenerator
    ; distance =
        formalIdentityPhysicalDistance
    ; self-adjoint =
        formalIdentityPhysicalSelfAdjoint
    ; stone-group =
        formalIdentityPhysicalStoneGroup
    ; strong-continuity =
        formalIdentityPhysicalContinuity
    }

formalIdentityPhysicalTraversalStoneUpgradeData :
  PhysicalTraversalStoneUpgradeData
formalIdentityPhysicalTraversalStoneUpgradeData =
  record
    { ProjectionAlgebra =
        ⊤
    ; quotientInnerProductWellDefined =
        ⊤
    ; hilbertCompletion =
        ⊤
    ; physicalTower =
        formalIdentityPhysicalTower
    ; physicalHilbertSpace =
        formalIdentityPhysicalHilbertSpace
    ; quotientToHilbert =
        λ _ → tt
    ; physicalUnitary =
        λ _ x → x
    ; physicalStoneBundle =
        formalIdentityPhysicalStoneBundle
    ; physicalStoneBundleUsesTraversal =
        λ _ _ → refl
    ; traversalExtendsFiniteAdvance =
        λ _ → refl
    ; upgradeBoundary =
        "Formal one-point physical Stone upgrade data: unit projection algebra, unit well-definedness witness, and unit completion witness"
        ∷ "quotientToHilbert collapses every selected finite quotient point to tt, so time-1 identity agrees with the finite advance only after this collapse"
        ∷ "The physicalUnitary is identity for every real parameter and the StoneBundle packages that identity action"
        ∷ "This is a formal shadow route, not a physical Hilbert quotient or selected finite traversal promotion"
        ∷ "No Schrodinger equation, Hamiltonian domain, spectral theorem, or empirical physical unitary is constructed"
        ∷ []
    }

formalIdentityDiscreteOneParameterGroupWrapper :
  DiscreteOneParameterGroupWrapper
    formalIdentityPhysicalTraversalStoneUpgradeData
formalIdentityDiscreteOneParameterGroupWrapper =
  record
    { DiscreteTime =
        ⊤
    ; discreteIdentity =
        tt
    ; discreteStep =
        tt
    ; discreteCompose =
        λ _ _ → tt
    ; discreteInverse =
        λ _ → tt
    ; discreteLeftInverseLaw =
        λ _ → refl
    ; discreteRightInverseLaw =
        λ _ → refl
    ; discreteToReal =
        λ _ → U.toℝ 1
    ; discreteAction =
        λ _ x → x
    ; discreteActionAgreesWithPhysicalUnitary =
        λ _ _ → refl
    ; discreteStepIsPhysicalTimeOne =
        refl
    ; discreteStepExtendsFiniteAdvance =
        λ _ → refl
    ; finiteAdvancePromotedToDiscreteGroup =
        false
    ; finiteAdvancePromotedToDiscreteGroup-v =
        refl
    ; wrapperBoundary =
        "Formal discrete time wrapper uses the one-point identity group"
        ∷ "The discrete step maps to formal real time 1, but the action is still identity on the one-point Hilbert carrier"
        ∷ "The finite advance comparison holds only because quotientToHilbert collapses the selected finite quotient carrier"
        ∷ "finiteAdvancePromotedToDiscreteGroup remains false; this wrapper is not the selected irreversible advance"
        ∷ []
    }

record FormalPhysicalReversibleShadow : Setω where
  field
    physicalReversibleTraversalSurface :
      SQD.PhysicalReversiblePhaseSpaceTraversalSurface

    physicalStoneUpgradeData :
      PhysicalTraversalStoneUpgradeData

    discreteIdentityGroupWrapper :
      DiscreteOneParameterGroupWrapper physicalStoneUpgradeData

    stoneRoute :
      StoneBundleSelfAdjointRoute
        (PhysicalTraversalStoneUpgradeData.physicalTower physicalStoneUpgradeData)
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace physicalStoneUpgradeData)

    selectedFiniteAdvanceSemigroupObstruction :
      SQD.SelectedFiniteAdvanceTraversalSemigroupObstruction

    physicalReversibleTraversalShadowConstructed :
      Bool

    physicalReversibleTraversalShadowConstructed-v :
      physicalReversibleTraversalShadowConstructed ≡ true

    stoneRouteConstructedFromFormalShadow :
      Bool

    stoneRouteConstructedFromFormalShadow-v :
      stoneRouteConstructedFromFormalShadow ≡ true

    shadowIsSelectedIrreversibleAdvance :
      Bool

    shadowIsSelectedIrreversibleAdvance-v :
      shadowIsSelectedIrreversibleAdvance ≡ false

    finiteAdvancePromotedToInvertible :
      Bool

    finiteAdvancePromotedToInvertible-v :
      finiteAdvancePromotedToInvertible ≡ false

    schrodingerEquationPromotedFromShadow :
      Bool

    schrodingerEquationPromotedFromShadow-v :
      schrodingerEquationPromotedFromShadow ≡ false

    shadowBoundary :
      List String

open FormalPhysicalReversibleShadow public

formalPhysicalReversibleShadow :
  FormalPhysicalReversibleShadow
formalPhysicalReversibleShadow =
  record
    { physicalReversibleTraversalSurface =
        formalIdentityPhysicalReversibleTraversalSurface
    ; physicalStoneUpgradeData =
        formalIdentityPhysicalTraversalStoneUpgradeData
    ; discreteIdentityGroupWrapper =
        formalIdentityDiscreteOneParameterGroupWrapper
    ; stoneRoute =
        physicalTraversalStoneUpgradeRoute
          formalIdentityPhysicalTraversalStoneUpgradeData
    ; selectedFiniteAdvanceSemigroupObstruction =
        SQD.selectedFiniteAdvanceTraversalSemigroupObstruction
    ; physicalReversibleTraversalShadowConstructed =
        true
    ; physicalReversibleTraversalShadowConstructed-v =
        refl
    ; stoneRouteConstructedFromFormalShadow =
        true
    ; stoneRouteConstructedFromFormalShadow-v =
        refl
    ; shadowIsSelectedIrreversibleAdvance =
        false
    ; shadowIsSelectedIrreversibleAdvance-v =
        refl
    ; finiteAdvancePromotedToInvertible =
        false
    ; finiteAdvancePromotedToInvertible-v =
        refl
    ; schrodingerEquationPromotedFromShadow =
        false
    ; schrodingerEquationPromotedFromShadow-v =
        refl
    ; shadowBoundary =
        "Formal physical reversible shadow is inhabited with a one-point identity traversal and one-point identity Stone bundle"
        ∷ "The finite shadow is constantly shiftHeldExitPoint, so it is compatible only with the fixed endpoint of selectedFiniteQuotientAdvanceTraversal"
        ∷ "This explicitly is not the selected irreversible advance: the selected finite table still moves start -> next -> held and has no preimage of start"
        ∷ "The Stone route is formal and non-promoting: it comes from supplied unit data through DASHI.Quantum.Stone, not from a physical quotient Hilbert completion"
        ∷ "Remaining physical blockers are the nondegenerate scalar field, quotient inner-product well-definedness, Hilbert topology/completion, strong continuity for a noncollapsed traversal, and self-adjoint domain data"
        ∷ "No Schrodinger closure, physical unitary evolution, spectral theorem, or Hamiltonian equation is promoted"
        ∷ []
    }

record SelectedQuotientStrongContinuitySocket : Setω where
  field
    selectedQuotientTopologyCompletionSurface :
      SelectedQuotientHilbertTopologyCompletionSurface

    selectedQuotientFiniteDensitySocketReceipt :
      SelectedQuotientFiniteDensitySocket

    finiteAdvanceTraversal :
      selectedFiniteQuotientCarrier →
      selectedFiniteQuotientCarrier

    finiteAdvanceTraversalIsCurrentAdvance :
      (q : selectedFiniteQuotientCarrier) →
      finiteAdvanceTraversal q
      ≡
      SQD.selectedFiniteQuotientAdvanceTraversal q

    finiteAdvanceSemigroupObstruction :
      SQD.SelectedFiniteAdvanceTraversalSemigroupObstruction

    suppliedUpgradeDataWouldGiveRoute :
      (upgradeData : PhysicalTraversalStoneUpgradeData) →
      StoneBundleSelfAdjointRoute
        (PhysicalTraversalStoneUpgradeData.physicalTower upgradeData)
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)

    finiteTopologyWitnessAvailable :
      Bool

    finiteTopologyWitnessAvailable-v :
      finiteTopologyWitnessAvailable ≡ true

    finiteCompletionWitnessAvailable :
      Bool

    finiteCompletionWitnessAvailable-v :
      finiteCompletionWitnessAvailable ≡ true

    finiteDensityWitnessAvailable :
      Bool

    finiteDensityWitnessAvailable-v :
      finiteDensityWitnessAvailable ≡ true

    strongContinuityForPhysicalTraversalSupplied :
      Bool

    strongContinuityForPhysicalTraversalSupplied-v :
      strongContinuityForPhysicalTraversalSupplied ≡ false

    traversalDerivedStoneBundleSupplied :
      Bool

    traversalDerivedStoneBundleSupplied-v :
      traversalDerivedStoneBundleSupplied ≡ false

    firstMissingPrimitiveName :
      String

    socketBoundary :
      List String

open SelectedQuotientStrongContinuitySocket public

selectedQuotientStrongContinuitySocket :
  SelectedQuotientStrongContinuitySocket
selectedQuotientStrongContinuitySocket =
  record
    { selectedQuotientTopologyCompletionSurface =
        selectedQuotientHilbertTopologyCompletionSurface
    ; selectedQuotientFiniteDensitySocketReceipt =
        selectedQuotientFiniteDensitySocket
    ; finiteAdvanceTraversal =
        SQD.selectedFiniteQuotientAdvanceTraversal
    ; finiteAdvanceTraversalIsCurrentAdvance =
        λ _ → refl
    ; finiteAdvanceSemigroupObstruction =
        SQD.selectedFiniteAdvanceTraversalSemigroupObstruction
    ; suppliedUpgradeDataWouldGiveRoute =
        physicalTraversalStoneUpgradeRoute
    ; finiteTopologyWitnessAvailable =
        true
    ; finiteTopologyWitnessAvailable-v =
        refl
    ; finiteCompletionWitnessAvailable =
        true
    ; finiteCompletionWitnessAvailable-v =
        refl
    ; finiteDensityWitnessAvailable =
        true
    ; finiteDensityWitnessAvailable-v =
        refl
    ; strongContinuityForPhysicalTraversalSupplied =
        false
    ; strongContinuityForPhysicalTraversalSupplied-v =
        refl
    ; traversalDerivedStoneBundleSupplied =
        false
    ; traversalDerivedStoneBundleSupplied-v =
        refl
    ; firstMissingPrimitiveName =
        "Strong-continuity witness for an invertible physical traversal extending the selected finite advance"
    ; socketBoundary =
        "The selected finite quotient topology/completion precursor is available and tied to a representative-independent projection inner product"
        ∷ "The selected finite quotient density socket is available: its dense core is the selected quotient carrier with identity approximation"
        ∷ "The descended finite advance is explicit but semigroup-only: shiftStartPoint has no preimage, so no reversible one-parameter group follows"
        ∷ "A physical strong-continuity theorem remains unsupplied until an invertible physical traversal and quotient-to-Hilbert bridge are provided"
        ∷ "The typed route is explicit: supplying PhysicalTraversalStoneUpgradeData yields a StoneBundleSelfAdjointRoute through DASHI.Quantum.Stone"
        ∷ "strongContinuityForPhysicalTraversalSupplied and traversalDerivedStoneBundleSupplied remain false"
        ∷ []
    }

record PhysicalHilbertStoneBundleDataRequest
  {ℓw ℓr ℓq ℓn : Level}
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn})
  : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    quotientDescentReceipt :
      SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}

    nondegenerateProjectionAlgebraRequest :
      SQD.NondegeneratePhysicalProjectionAlgebraRequest

    suppliedStoneBundleRoute :
      (Tow : U.Tower) →
      (HS : U.HilbertSpace) →
      Stone.StoneBundle Tow HS →
      StoneBundleSelfAdjointRoute Tow HS

    finiteSelectedQuotientAvailable :
      Bool

    finiteSelectedQuotientAvailable-v :
      finiteSelectedQuotientAvailable ≡ true

    selectedFixedDepthHilbertCompletenessSurface :
      FixedDepthHilbertCompletenessSurface

    selectedQuotientHilbertTopologyCompletionSurfaceReceipt :
      SelectedQuotientHilbertTopologyCompletionSurface

    selectedQuotientNondegenerateProjectionScalarSocketReceipt :
      SelectedQuotientNondegenerateProjectionScalarSocket

    selectedQuotientPostProjectionScalarSocketReceipt :
      SelectedQuotientPostProjectionScalarSocket

    selectedQuotientPostInnerProductWellDefinednessSocketReceipt :
      SelectedQuotientPostInnerProductWellDefinednessSocket

    selectedQuotientPostGlobalInnerProductWellDefinednessSocketReceipt :
      SelectedQuotientPostGlobalInnerProductWellDefinednessSocket

    selectedQuotientPostAcceptedHilbertCompletionSocketReceipt :
      SelectedQuotientPostAcceptedHilbertCompletionSocket

    selectedQuotientFiniteDensitySocketReceipt :
      SelectedQuotientFiniteDensitySocket

    selectedFilteredColimitHilbertSocketReceipt :
      SelectedFilteredColimitHilbertSocket

    selectedQuotientStrongContinuitySocketReceipt :
      SelectedQuotientStrongContinuitySocket

    finiteSelectedQuotientTopologyCompletionAvailable :
      Bool

    finiteSelectedQuotientTopologyCompletionAvailable-v :
      finiteSelectedQuotientTopologyCompletionAvailable ≡ true

    finiteSelectedQuotientDensityAvailable :
      Bool

    finiteSelectedQuotientDensityAvailable-v :
      finiteSelectedQuotientDensityAvailable ≡ true

    nondegenerateProjectionAlgebraSupplied :
      Bool

    nondegenerateProjectionAlgebraSupplied-v :
      nondegenerateProjectionAlgebraSupplied ≡ false

    hilbertQuotientInnerProductSupplied :
      Bool

    hilbertQuotientInnerProductSupplied-v :
      hilbertQuotientInnerProductSupplied ≡ false

    hilbertCompletionSupplied :
      Bool

    hilbertCompletionSupplied-v :
      hilbertCompletionSupplied ≡ false

    oneParameterTraversalGroupSupplied :
      Bool

    oneParameterTraversalGroupSupplied-v :
      oneParameterTraversalGroupSupplied ≡ false

    strongContinuitySupplied :
      Bool

    strongContinuitySupplied-v :
      strongContinuitySupplied ≡ false

    stoneBundleConstructedFromQuotientTraversal :
      Bool

    stoneBundleConstructedFromQuotientTraversal-v :
      stoneBundleConstructedFromQuotientTraversal ≡ false

    firstMissingPrimitiveName :
      String

    requestBoundary :
      List String

open PhysicalHilbertStoneBundleDataRequest public

physicalHilbertStoneBundleDataRequest :
  {ℓw ℓr ℓq ℓn : Level} →
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}) →
  PhysicalHilbertStoneBundleDataRequest quotientReceipt
physicalHilbertStoneBundleDataRequest quotientReceipt =
  record
    { requestedInterfaceName =
        "PhysicalHilbertStoneBundleDataForSchrodingerQuotient"
    ; exactRequiredFields =
        "nondegenerateProjectionAlgebra : NondegeneratePhysicalProjectionAlgebraForShiftWavePhaseQuotient"
        ∷ "quotientInnerProduct : quotientCarrier -> quotientCarrier -> ComplexValue"
        ∷ "quotientInnerProductWellDefined : representatives related by kernelEquivalence give equal inner products"
        ∷ "hilbertCompletion : completed HilbertSpace for the quotient carrier"
        ∷ "oneParameterTraversalAutomorphismGroup : StoneGroup-compatible action U(t) on the Hilbert quotient"
        ∷ "traversalExtendsQuotientAdvance : U(discrete-step) agrees with the descended quotient traversal where comparison is meaningful"
        ∷ "strongContinuity : StoneContinuity U distance"
        ∷ "generator : H -> H"
        ∷ "stoneSelfAdjoint : StoneSelfAdjoint HS generator"
        ∷ "stoneBundle : StoneBundle Tow HS packaging lift, generator, distance, self-adjointness, group law, and strong continuity"
        ∷ []
    ; quotientDescentReceipt =
        quotientReceipt
    ; nondegenerateProjectionAlgebraRequest =
        SQD.nondegeneratePhysicalProjectionAlgebraRequest
    ; suppliedStoneBundleRoute =
        stoneBundleSelfAdjointRoute
    ; finiteSelectedQuotientAvailable =
        true
    ; finiteSelectedQuotientAvailable-v =
        refl
    ; selectedFixedDepthHilbertCompletenessSurface =
        selectedFiniteDepthHilbertCompletenessSurface 0
    ; selectedQuotientHilbertTopologyCompletionSurfaceReceipt =
        selectedQuotientHilbertTopologyCompletionSurface
    ; selectedQuotientNondegenerateProjectionScalarSocketReceipt =
        selectedQuotientNondegenerateProjectionScalarSocket
    ; selectedQuotientPostProjectionScalarSocketReceipt =
        selectedQuotientPostProjectionScalarSocket
    ; selectedQuotientPostInnerProductWellDefinednessSocketReceipt =
        selectedQuotientPostInnerProductWellDefinednessSocket
    ; selectedQuotientPostGlobalInnerProductWellDefinednessSocketReceipt =
        selectedQuotientPostGlobalInnerProductWellDefinednessSocket
    ; selectedQuotientPostAcceptedHilbertCompletionSocketReceipt =
        selectedQuotientPostAcceptedHilbertCompletionSocket
    ; selectedQuotientFiniteDensitySocketReceipt =
        selectedQuotientFiniteDensitySocket
    ; selectedFilteredColimitHilbertSocketReceipt =
        selectedFilteredColimitHilbertSocket
    ; selectedQuotientStrongContinuitySocketReceipt =
        selectedQuotientStrongContinuitySocket
    ; finiteSelectedQuotientTopologyCompletionAvailable =
        true
    ; finiteSelectedQuotientTopologyCompletionAvailable-v =
        refl
    ; finiteSelectedQuotientDensityAvailable =
        true
    ; finiteSelectedQuotientDensityAvailable-v =
        refl
    ; nondegenerateProjectionAlgebraSupplied =
        false
    ; nondegenerateProjectionAlgebraSupplied-v =
        refl
    ; hilbertQuotientInnerProductSupplied =
        false
    ; hilbertQuotientInnerProductSupplied-v =
        refl
    ; hilbertCompletionSupplied =
        false
    ; hilbertCompletionSupplied-v =
        refl
    ; oneParameterTraversalGroupSupplied =
        false
    ; oneParameterTraversalGroupSupplied-v =
        refl
    ; strongContinuitySupplied =
        false
    ; strongContinuitySupplied-v =
        refl
    ; stoneBundleConstructedFromQuotientTraversal =
        false
    ; stoneBundleConstructedFromQuotientTraversal-v =
        refl
    ; firstMissingPrimitiveName =
        "Invertible one-parameter physical traversal automorphism group extending selected finite advance after local accepted Hilbert-completion progress"
    ; requestBoundary =
        "The selected finite quotient is available, but it is only a coordinate quotient over ShiftPressurePoint"
        ∷ "A fixed-depth Hilbert completeness surface is inhabited at depth 0 using the selected finite quotient carrier and formal zero inner product"
        ∷ "That fixed-depth surface explicitly does not claim colimit completeness or a physical limit"
        ∷ "A finite selected-quotient topology/completion precursor is now tied to the representative-independent projection inner product surface"
        ∷ "SelectedQuotientNondegenerateProjectionScalarSocket isolates the pre-completion blocker: nondegenerate projection/scalar laws above the finite coordinate quotient"
        ∷ "SelectedQuotientPostProjectionScalarSocket records selected finite first-field progress and advances the next exact theorem blocker to quotientInnerProductWellDefinednessField"
        ∷ "SelectedQuotientPostInnerProductWellDefinednessSocket records selected finite second-field progress and advances the next exact theorem blocker to globalPhysicalQuotientInnerProductWellDefinednessField"
        ∷ "SelectedQuotientPostGlobalInnerProductWellDefinednessSocket records selected finite third-field progress and advances the next exact theorem blocker to acceptedHilbertCompletionField"
        ∷ "SelectedQuotientPostAcceptedHilbertCompletionSocket records selected finite fourth-field progress, keeps global accepted completion unpromoted, and moves the next exact blocker to traversal-group/continuity data"
        ∷ "A finite selected-quotient density socket is now inhabited by identity approximation on the selected finite carrier"
        ∷ "SelectedFilteredColimitHilbertSocket maps that selected dense-core carrier into the canonical finite-support colimit witness in Stone, still as a finite/local non-promoting bridge"
        ∷ "SelectedQuotientStrongContinuitySocket now isolates the strong-continuity blocker against the semigroup-only finite advance"
        ∷ "No inspected primitive upgrades that quotient to a nondegenerate physical projection algebra"
        ∷ "No promoted global physical quotient inner-product well-definedness proof or accepted Hilbert completion witness is supplied"
        ∷ "No one-parameter traversal automorphism group or strong-continuity proof is supplied for the quotient"
        ∷ "The typed supplied-bundle route is explicit: a StoneBundle Tow HS gives StoneConsequences and the self-adjoint generator through StoneBundleSelfAdjointRoute"
        ∷ "Because the StoneBundle is not constructed from quotient traversal here, all Hilbert/Stone/self-adjoint/unitary/Schrodinger promotion flags remain false"
        ∷ []
    }

record FormalToPhysicalTraversalStoneUpgradeRequest
  {ℓw ℓr ℓq ℓn : Level}
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn})
  : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    quotientDescentReceipt :
      SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}

    formalFiniteStoneAttempt :
      SelectedFiniteQuotientStoneAttempt

    finiteAdvanceTraversalSemigroupObstruction :
      SQD.SelectedFiniteAdvanceTraversalSemigroupObstruction

    physicalHilbertStoneBundleDataRequestReceipt :
      PhysicalHilbertStoneBundleDataRequest quotientReceipt

    suppliedUpgradeDataWouldGiveRoute :
      (upgradeData : PhysicalTraversalStoneUpgradeData) →
      StoneBundleSelfAdjointRoute
        (PhysicalTraversalStoneUpgradeData.physicalTower upgradeData)
        (PhysicalTraversalStoneUpgradeData.physicalHilbertSpace upgradeData)

    finiteAdvanceTraversalConstructed :
      Bool

    finiteAdvanceTraversalConstructed-v :
      finiteAdvanceTraversalConstructed ≡ true

    finiteAdvanceTraversalGroupConstructed :
      Bool

    finiteAdvanceTraversalGroupConstructed-v :
      finiteAdvanceTraversalGroupConstructed ≡ false

    upgradeDataSupplied :
      Bool

    upgradeDataSupplied-v :
      upgradeDataSupplied ≡ false

    physicalTraversalStoneBundleConstructed :
      Bool

    physicalTraversalStoneBundleConstructed-v :
      physicalTraversalStoneBundleConstructed ≡ false

    firstMissingPrimitiveName :
      String

    requestBoundary :
      List String

open FormalToPhysicalTraversalStoneUpgradeRequest public

formalToPhysicalTraversalStoneUpgradeRequest :
  {ℓw ℓr ℓq ℓn : Level} →
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}) →
  FormalToPhysicalTraversalStoneUpgradeRequest quotientReceipt
formalToPhysicalTraversalStoneUpgradeRequest quotientReceipt =
  record
    { requestedInterfaceName =
        "PhysicalTraversalStoneUpgradeData"
    ; exactRequiredFields =
        "ProjectionAlgebra : Set"
        ∷ "quotientInnerProductWellDefined : Set"
        ∷ "hilbertCompletion : Set"
        ∷ "physicalTower : Tower"
        ∷ "physicalHilbertSpace : HilbertSpace"
        ∷ "quotientToHilbert : selectedFiniteQuotientCarrier -> H"
        ∷ "physicalUnitary : Real -> H -> H"
        ∷ "physicalStoneBundle : StoneBundle physicalTower physicalHilbertSpace"
        ∷ "physicalStoneBundleUsesTraversal : stone-unitary physicalStoneBundle t x == physicalUnitary t x"
        ∷ "traversalExtendsFiniteAdvance : physicalUnitary 1 (quotientToHilbert q) == quotientToHilbert (selectedFiniteQuotientAdvanceTraversal q)"
        ∷ []
    ; quotientDescentReceipt =
        quotientReceipt
    ; formalFiniteStoneAttempt =
        selectedFiniteQuotientStoneAttempt
    ; finiteAdvanceTraversalSemigroupObstruction =
        SQD.selectedFiniteAdvanceTraversalSemigroupObstruction
    ; physicalHilbertStoneBundleDataRequestReceipt =
        physicalHilbertStoneBundleDataRequest quotientReceipt
    ; suppliedUpgradeDataWouldGiveRoute =
        physicalTraversalStoneUpgradeRoute
    ; finiteAdvanceTraversalConstructed =
        true
    ; finiteAdvanceTraversalConstructed-v =
        refl
    ; finiteAdvanceTraversalGroupConstructed =
        false
    ; finiteAdvanceTraversalGroupConstructed-v =
        refl
    ; upgradeDataSupplied =
        false
    ; upgradeDataSupplied-v =
        refl
    ; physicalTraversalStoneBundleConstructed =
        false
    ; physicalTraversalStoneBundleConstructed-v =
        refl
    ; firstMissingPrimitiveName =
        "Invertible one-parameter physical traversal Stone bundle extending the finite advance"
    ; requestBoundary =
        "This bridge is the exact typed upgrade path from the formal finite Stone attempt to a physical traversal-derived Stone bundle"
        ∷ "The current finite advance is nontrivial but non-invertible, so it cannot itself be the Stone traversal group"
        ∷ "Supplying PhysicalTraversalStoneUpgradeData would provide the physical tower, Hilbert carrier, physicalUnitary action, StoneBundle, and comparison to the descended finite advance at time 1"
        ∷ "The route from supplied PhysicalTraversalStoneUpgradeData to StoneBundleSelfAdjointRoute is available through DASHI.Quantum.Stone"
        ∷ "No such upgrade data is supplied here; the formal identity bundle remains below physical Hilbert/Stone promotion"
        ∷ []
    }

record PhaseSpaceTraversalGroupAndHilbertData : Setω where
  field
    reversibleTraversalCandidate :
      SQD.FinitePhaseSpaceReversibleTraversalCandidate

    finiteTraversalInterface :
      SQD.PhaseSpaceReversibleTraversalSuppliedInterface

    ScalarField :
      Set

    scalarFieldLaws :
      Set

    TimeParameter :
      Set

    timeIdentity :
      TimeParameter

    timeCompose :
      TimeParameter →
      TimeParameter →
      TimeParameter

    timeInverse :
      TimeParameter →
      TimeParameter

    inverseLawLeft :
      (t : TimeParameter) →
      timeCompose (timeInverse t) t
      ≡
      timeIdentity

    inverseLawRight :
      (t : TimeParameter) →
      timeCompose t (timeInverse t)
      ≡
      timeIdentity

    quotientInnerProduct :
      selectedFiniteQuotientCarrier →
      selectedFiniteQuotientCarrier →
      ScalarField

    quotientInnerProductWellDefined :
      Set

    physicalTower :
      U.Tower

    physicalHilbertSpace :
      U.HilbertSpace

    quotientToHilbert :
      selectedFiniteQuotientCarrier →
      U.HilbertSpace.H physicalHilbertSpace

    physicalUnitary :
      U.ℝ →
      U.HilbertSpace.H physicalHilbertSpace →
      U.HilbertSpace.H physicalHilbertSpace

    physicalDistance :
      U.HilbertSpace.H physicalHilbertSpace →
      U.HilbertSpace.H physicalHilbertSpace →
      U.ℝ

    strongContinuity :
      Stone.StoneContinuity physicalUnitary physicalDistance

    stoneBundle :
      Stone.StoneBundle physicalTower physicalHilbertSpace

    stoneBundleUsesTraversal :
      (t : U.ℝ) →
      (x : U.HilbertSpace.H physicalHilbertSpace) →
      Stone.stone-unitary stoneBundle t x
      ≡
      physicalUnitary t x

    traversalExtendsFiniteAdvance :
      (q : selectedFiniteQuotientCarrier) →
      physicalUnitary (U.toℝ 1) (quotientToHilbert q)
      ≡
      quotientToHilbert (SQD.selectedFiniteQuotientAdvanceTraversal q)

    suppliedInterfaceBoundary :
      List String

open PhaseSpaceTraversalGroupAndHilbertData public

phaseSpaceTraversalGroupAndHilbertDataRoute :
  (suppliedData : PhaseSpaceTraversalGroupAndHilbertData) →
  StoneBundleSelfAdjointRoute
    (PhaseSpaceTraversalGroupAndHilbertData.physicalTower suppliedData)
    (PhaseSpaceTraversalGroupAndHilbertData.physicalHilbertSpace suppliedData)
phaseSpaceTraversalGroupAndHilbertDataRoute suppliedData =
  stoneBundleSelfAdjointRoute
    (PhaseSpaceTraversalGroupAndHilbertData.physicalTower suppliedData)
    (PhaseSpaceTraversalGroupAndHilbertData.physicalHilbertSpace suppliedData)
    (PhaseSpaceTraversalGroupAndHilbertData.stoneBundle suppliedData)

record PhaseSpaceTraversalGroupAndHilbertDataRequest
  {ℓw ℓr ℓq ℓn : Level}
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn})
  : Setω where
  field
    requestedInterfaceName :
      String

    exactRequiredFields :
      List String

    quotientDescentReceipt :
      SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}

    reversibleTraversalObstruction :
      SQD.SelectedFinitePhaseSpaceReversibleTraversalObstruction

    finiteReversibleTraversalSuppliedInterfaceRoute :
      SQD.FinitePhaseSpaceReversibleTraversalCandidate →
      SQD.PhaseSpaceReversibleTraversalSuppliedInterface

    suppliedDataWouldGiveStoneRoute :
      (suppliedData : PhaseSpaceTraversalGroupAndHilbertData) →
      StoneBundleSelfAdjointRoute
        (PhaseSpaceTraversalGroupAndHilbertData.physicalTower suppliedData)
        (PhaseSpaceTraversalGroupAndHilbertData.physicalHilbertSpace suppliedData)

    finiteReversibleTraversalCandidateSupplied :
      Bool

    finiteReversibleTraversalCandidateSupplied-v :
      finiteReversibleTraversalCandidateSupplied ≡ false

    scalarFieldSupplied :
      Bool

    scalarFieldSupplied-v :
      scalarFieldSupplied ≡ false

    timeParameterGroupSupplied :
      Bool

    timeParameterGroupSupplied-v :
      timeParameterGroupSupplied ≡ false

    inverseLawSupplied :
      Bool

    inverseLawSupplied-v :
      inverseLawSupplied ≡ false

    quotientInnerProductSupplied :
      Bool

    quotientInnerProductSupplied-v :
      quotientInnerProductSupplied ≡ false

    strongContinuitySupplied :
      Bool

    strongContinuitySupplied-v :
      strongContinuitySupplied ≡ false

    stoneBundleSupplied :
      Bool

    stoneBundleSupplied-v :
      stoneBundleSupplied ≡ false

    firstMissingPrimitiveName :
      String

    absenceLedger :
      List String

open PhaseSpaceTraversalGroupAndHilbertDataRequest public

phaseSpaceTraversalGroupAndHilbertDataRequest :
  {ℓw ℓr ℓq ℓn : Level} →
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}) →
  PhaseSpaceTraversalGroupAndHilbertDataRequest quotientReceipt
phaseSpaceTraversalGroupAndHilbertDataRequest quotientReceipt =
  record
    { requestedInterfaceName =
        "PhaseSpaceTraversalGroupAndHilbertDataRequest"
    ; exactRequiredFields =
        "reversibleTraversalCandidate : FinitePhaseSpaceReversibleTraversalCandidate"
        ∷ "scalarField : Set with accepted scalar-field laws for quotient inner products"
        ∷ "timeParameterGroup : carrier, identity, composition, inverse"
        ∷ "inverseLaw : left and right inverse laws for the time parameter group"
        ∷ "quotientInnerProduct : selectedFiniteQuotientCarrier -> selectedFiniteQuotientCarrier -> scalarField"
        ∷ "quotientInnerProductWellDefined : representative-independence and quotient compatibility evidence"
        ∷ "physicalHilbertSpace : HilbertSpace receiving the quotient carrier"
        ∷ "physicalUnitary : Real -> H -> H extending the finite traversal through quotientToHilbert"
        ∷ "strongContinuity : StoneContinuity physicalUnitary physicalDistance"
        ∷ "stoneBundle : StoneBundle physicalTower physicalHilbertSpace built from that traversal"
        ∷ []
    ; quotientDescentReceipt =
        quotientReceipt
    ; reversibleTraversalObstruction =
        SQD.selectedFinitePhaseSpaceReversibleTraversalObstruction
    ; finiteReversibleTraversalSuppliedInterfaceRoute =
        SQD.phaseSpaceReversibleTraversalSuppliedInterface
    ; suppliedDataWouldGiveStoneRoute =
        phaseSpaceTraversalGroupAndHilbertDataRoute
    ; finiteReversibleTraversalCandidateSupplied =
        false
    ; finiteReversibleTraversalCandidateSupplied-v =
        refl
    ; scalarFieldSupplied =
        false
    ; scalarFieldSupplied-v =
        refl
    ; timeParameterGroupSupplied =
        false
    ; timeParameterGroupSupplied-v =
        refl
    ; inverseLawSupplied =
        false
    ; inverseLawSupplied-v =
        refl
    ; quotientInnerProductSupplied =
        false
    ; quotientInnerProductSupplied-v =
        refl
    ; strongContinuitySupplied =
        false
    ; strongContinuitySupplied-v =
        refl
    ; stoneBundleSupplied =
        false
    ; stoneBundleSupplied-v =
        refl
    ; firstMissingPrimitiveName =
        "Scalar field and time-parameter inverse law before quotient inner product, strong continuity, and Stone bundle"
    ; absenceLedger =
        "The quotient-level supplied-interface route is typed: a supplied FinitePhaseSpaceReversibleTraversalCandidate exposes reverseTraversal plus left/right inverse laws"
        ∷ "The current selected finite advance cannot supply that candidate because shiftStartPoint has no preimage"
        ∷ "No scalar field for quotient inner products is supplied"
        ∷ "No time-parameter group carrier, identity, composition, inverse, or inverse law is supplied"
        ∷ "No quotient inner product or well-definedness proof is supplied"
        ∷ "No physicalUnitary action with strong continuity is supplied"
        ∷ "No traversal-derived Stone bundle is supplied"
        ∷ "Supplying PhaseSpaceTraversalGroupAndHilbertData would give StoneBundleSelfAdjointRoute through stoneBundleSelfAdjointRoute, but this request constructs none of those fields"
        ∷ "All Hilbert/Stone/self-adjoint/unitary/Schrodinger promotion flags remain false"
        ∷ []
    }

record HilbertTopologyScalarBlockerLedger
  {ℓw ℓr ℓq ℓn : Level}
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn})
  : Setω where
  field
    requestedInterfaceName :
      String

    quotientDescentReceipt :
      SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}

    discreteOneParameterGroupWrapperRequestReceipt :
      DiscreteOneParameterGroupWrapperRequest quotientReceipt

    phaseSpaceTraversalGroupAndHilbertDataRequestReceipt :
      PhaseSpaceTraversalGroupAndHilbertDataRequest quotientReceipt

    scalarCarrierSupplied :
      Bool

    scalarCarrierSupplied-v :
      scalarCarrierSupplied ≡ false

    scalarFieldLawsSupplied :
      Bool

    scalarFieldLawsSupplied-v :
      scalarFieldLawsSupplied ≡ false

    quotientInnerProductWellDefinednessSupplied :
      Bool

    quotientInnerProductWellDefinednessSupplied-v :
      quotientInnerProductWellDefinednessSupplied ≡ false

    hilbertCompletionTopologySupplied :
      Bool

    hilbertCompletionTopologySupplied-v :
      hilbertCompletionTopologySupplied ≡ false

    strongContinuityTopologySupplied :
      Bool

    strongContinuityTopologySupplied-v :
      strongContinuityTopologySupplied ≡ false

    selfAdjointDomainSupplied :
      Bool

    selfAdjointDomainSupplied-v :
      selfAdjointDomainSupplied ≡ false

    firstRemainingScalarBlockerName :
      String

    exactRemainingBlockers :
      List String

open HilbertTopologyScalarBlockerLedger public

hilbertTopologyScalarBlockerLedger :
  {ℓw ℓr ℓq ℓn : Level} →
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}) →
  HilbertTopologyScalarBlockerLedger quotientReceipt
hilbertTopologyScalarBlockerLedger quotientReceipt =
  record
    { requestedInterfaceName =
        "HilbertTopologyScalarBlockerLedger"
    ; quotientDescentReceipt =
        quotientReceipt
    ; discreteOneParameterGroupWrapperRequestReceipt =
        discreteOneParameterGroupWrapperRequest quotientReceipt
    ; phaseSpaceTraversalGroupAndHilbertDataRequestReceipt =
        phaseSpaceTraversalGroupAndHilbertDataRequest quotientReceipt
    ; scalarCarrierSupplied =
        false
    ; scalarCarrierSupplied-v =
        refl
    ; scalarFieldLawsSupplied =
        false
    ; scalarFieldLawsSupplied-v =
        refl
    ; quotientInnerProductWellDefinednessSupplied =
        false
    ; quotientInnerProductWellDefinednessSupplied-v =
        refl
    ; hilbertCompletionTopologySupplied =
        false
    ; hilbertCompletionTopologySupplied-v =
        refl
    ; strongContinuityTopologySupplied =
        false
    ; strongContinuityTopologySupplied-v =
        refl
    ; selfAdjointDomainSupplied =
        false
    ; selfAdjointDomainSupplied-v =
        refl
    ; firstRemainingScalarBlockerName =
        "Accepted scalar carrier and scalar-field laws for quotient inner products"
    ; exactRemainingBlockers =
        "accepted scalar carrier for quotient inner products"
        ∷ "scalar-field laws compatible with the intended Hilbert quotient"
        ∷ "representative-independent quotient inner product"
        ∷ "Hilbert completion/topology for the quotient carrier"
        ∷ "topological strong-continuity proof for the physical traversal"
        ∷ "self-adjoint generator domain data beyond the supplied StoneBundle consequence"
        ∷ "discrete time group wrapper tied to the supplied physical Stone traversal"
        ∷ []
    }

record HilbertQuotientDependencyObstruction
  {ℓw ℓr ℓq ℓn : Level}
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn})
  : Setω where
  field
    firstMissingTheorem :
      SchrodingerSelfAdjointEvolutionFirstMissingTheorem

    firstMissingTheoremIsHilbertQuotient :
      firstMissingTheorem ≡ missingHilbertQuotientCarrier

    quotientNormDescentAvailable :
      Bool

    quotientNormDescentAvailable-v :
      quotientNormDescentAvailable ≡ true

    hilbertQuotientConstructed :
      Bool

    hilbertQuotientConstructed-v :
      hilbertQuotientConstructed ≡ false

    physicalTraversalAdapterRequest :
      SQD.PhysicalSchrodingerTraversalAdapterRequest

    advanceWavePhasePhysicalKernelExtensionalityRequest :
      SQD.AdvanceWavePhasePhysicalKernelExtensionalityRequest

    advanceWavePhaseObservationKernelPrimitiveRequest :
      SQD.AdvanceWavePhaseObservationKernelPrimitiveRequest

    shiftWavePhaseSelectedLinearPhaseEvidenceRequest :
      SQD.ShiftWavePhaseSelectedLinearPhaseEvidenceRequest

    advanceWavePhaseKernelEqualityAdapterConstructed :
      Bool

    advanceWavePhaseKernelEqualityAdapterConstructed-v :
      advanceWavePhaseKernelEqualityAdapterConstructed ≡ false

    obstructionBoundary :
      List String

open HilbertQuotientDependencyObstruction public

hilbertQuotientDependencyObstruction :
  {ℓw ℓr ℓq ℓn : Level} →
  (quotientReceipt :
    SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}) →
  HilbertQuotientDependencyObstruction quotientReceipt
hilbertQuotientDependencyObstruction quotientReceipt =
  record
    { firstMissingTheorem =
        missingHilbertQuotientCarrier
    ; firstMissingTheoremIsHilbertQuotient =
        refl
    ; quotientNormDescentAvailable =
        true
    ; quotientNormDescentAvailable-v =
        refl
    ; hilbertQuotientConstructed =
        false
    ; hilbertQuotientConstructed-v =
        refl
    ; physicalTraversalAdapterRequest =
        SQD.physicalSchrodingerTraversalAdapterRequest
    ; advanceWavePhasePhysicalKernelExtensionalityRequest =
        SQD.advanceWavePhasePhysicalKernelExtensionalityRequest
    ; advanceWavePhaseObservationKernelPrimitiveRequest =
        SQD.advanceWavePhaseObservationKernelPrimitiveRequest
    ; shiftWavePhaseSelectedLinearPhaseEvidenceRequest =
        SQD.shiftWavePhaseSelectedLinearPhaseEvidenceRequest
    ; advanceWavePhaseKernelEqualityAdapterConstructed =
        false
    ; advanceWavePhaseKernelEqualityAdapterConstructed-v =
        refl
    ; obstructionBoundary =
        "Quotient/norm descent can be consumed from SchrodingerQuotientDescentReceipt"
        ∷ "Physical traversal remains upstream-requested through PhysicalSchrodingerTraversalAdapterRequest"
        ∷ "The equality-kernel fallback for advanceWavePhaseState is inhabited, but it is not a physical observational kernel"
        ∷ "AdvanceWavePhasePhysicalKernelExtensionalityRequest isolates the non-collapsing physical blocker: kernel extensionality plus a quotient surface"
        ∷ "The finite selected amplitude/phase coordinate observation kernel primitive has typechecked advanceWavePhaseObservationNaturality"
        ∷ "ShiftWavePhaseSelectedLinearPhaseEvidenceRequest now records typed degenerate scalar/additive/phase-action evidence for selectedObservationLinear and selectedObservationPhaseHomogeneous"
        ∷ "The finite selected coordinate SetoidQuotientSurface is now constructed using ShiftPressurePoint as quotient carrier"
        ∷ "The remaining physical blocker is any upgrade from degenerate coordinate algebra to nontrivial physical projection/Hilbert algebra"
        ∷ "PhysicalHilbertStoneBundleDataRequest names the absent projection algebra, quotient inner-product well-definedness, completion, traversal group, strong continuity, and Stone bundle"
        ∷ "AdvanceWavePhaseObservationKernelPrimitiveRequest keeps the physical projection lane open for linearPhaseHomogeneousAdvanceNaturality"
        ∷ "The first missing theorem for self-adjoint evolution is the Hilbert quotient carrier and inner-product/completion structure"
        ∷ "No Hilbert-space action, Hamiltonian domain, self-adjoint generator, or unitary group is inferred from quotient norm descent"
        ∷ []
    }

record StoneBundleConstructionObstruction
  (Tow : U.Tower)
  (HS : U.HilbertSpace)
  : Setω where
  field
    firstMissingTheorem :
      SchrodingerSelfAdjointEvolutionFirstMissingTheorem

    firstMissingTheoremIsStoneBundleFromQuotientTraversal :
      firstMissingTheorem ≡ missingStoneBundleFromQuotientTraversal

    routeAvailableIfBundleSupplied :
      Stone.StoneBundle Tow HS →
      StoneBundleSelfAdjointRoute Tow HS

    suppliedBundleWouldGiveSelfAdjointGenerator :
      Bool

    suppliedBundleWouldGiveSelfAdjointGenerator-v :
      suppliedBundleWouldGiveSelfAdjointGenerator ≡ true

    bundleConstructedFromQuotientTraversal :
      Bool

    bundleConstructedFromQuotientTraversal-v :
      bundleConstructedFromQuotientTraversal ≡ false

    obstructionBoundary :
      List String

open StoneBundleConstructionObstruction public

stoneBundleConstructionObstruction :
  (Tow : U.Tower) →
  (HS : U.HilbertSpace) →
  StoneBundleConstructionObstruction Tow HS
stoneBundleConstructionObstruction Tow HS =
  record
    { firstMissingTheorem =
        missingStoneBundleFromQuotientTraversal
    ; firstMissingTheoremIsStoneBundleFromQuotientTraversal =
        refl
    ; routeAvailableIfBundleSupplied =
        stoneBundleSelfAdjointRoute Tow HS
    ; suppliedBundleWouldGiveSelfAdjointGenerator =
        true
    ; suppliedBundleWouldGiveSelfAdjointGenerator-v =
        refl
    ; bundleConstructedFromQuotientTraversal =
        false
    ; bundleConstructedFromQuotientTraversal-v =
        refl
    ; obstructionBoundary =
        "StoneBundleSelfAdjointRoute is available only after a StoneBundle is supplied"
        ∷ "The missing theorem is construction of that StoneBundle from quotient traversal and Hilbert data"
        ∷ "Stone-theorem consequences are consumed from DASHI.Quantum.Stone; they are not reconstructed here"
        ∷ "No postulate or authority token is introduced to claim self-adjointness"
        ∷ []
    }

record SchrodingerSelfAdjointEvolutionReceipt
  {ℓw ℓr ℓq ℓn : Level}
  : Setω where
  field
    quotientDescentReceipt :
      SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn}

    openTargets :
      List SchrodingerSelfAdjointEvolutionOpenTarget

    firstMissingTheorem :
      SchrodingerSelfAdjointEvolutionFirstMissingTheorem

    firstMissingTheorem-v :
      firstMissingTheorem
      ≡
      defaultSchrodingerSelfAdjointEvolutionFirstMissingTheorem

    hilbertQuotientPromoted :
      Bool

    hilbertQuotientPromoted-v :
      hilbertQuotientPromoted ≡ false

    oneParameterTraversalAutomorphismGroupPromoted :
      Bool

    oneParameterTraversalAutomorphismGroupPromoted-v :
      oneParameterTraversalAutomorphismGroupPromoted ≡ false

    selfAdjointGeneratorPromoted :
      Bool

    selfAdjointGeneratorPromoted-v :
      selfAdjointGeneratorPromoted ≡ false

    stoneTheoremRoutePromoted :
      Bool

    stoneTheoremRoutePromoted-v :
      stoneTheoremRoutePromoted ≡ false

    exponentialEvolutionFormulaPromoted :
      Bool

    exponentialEvolutionFormulaPromoted-v :
      exponentialEvolutionFormulaPromoted ≡ false

    schrodingerEquationTargetPromoted :
      Bool

    schrodingerEquationTargetPromoted-v :
      schrodingerEquationTargetPromoted ≡ false

    receiptStatus :
      SchrodingerSelfAdjointEvolutionStatus

    noPromotionWithoutAuthority :
      SchrodingerSelfAdjointEvolutionPromotionAuthorityToken →
      ⊥

    physicalTraversalAdapterRequest :
      SQD.PhysicalSchrodingerTraversalAdapterRequest

    advanceWavePhasePhysicalKernelExtensionalityRequest :
      SQD.AdvanceWavePhasePhysicalKernelExtensionalityRequest

    advanceWavePhaseObservationKernelPrimitiveRequest :
      SQD.AdvanceWavePhaseObservationKernelPrimitiveRequest

    shiftWavePhaseSelectedLinearPhaseEvidenceRequest :
      SQD.ShiftWavePhaseSelectedLinearPhaseEvidenceRequest

    advanceWavePhaseKernelEqualityAdapterConstructed :
      Bool

    advanceWavePhaseKernelEqualityAdapterConstructed-v :
      advanceWavePhaseKernelEqualityAdapterConstructed ≡ false

    selectedFiniteQuotientStoneAttemptReceipt :
      SelectedFiniteQuotientStoneAttempt

    finiteSelfAdjointHamiltonianStoneDataReceipt :
      Stone.FiniteSelfAdjointHamiltonianStoneData

    finiteDepthIdentityStoneTowerSkeletonReceipt :
      Stone.FiniteDepthIdentityStoneTowerSkeleton

    selectedFiniteQuotientStoneGeneratorSpectralGapInterpretationSurfaceReceipt :
      Stone.BoundedStoneGeneratorSpectralGapInterpretationReceipt

    physicalHilbertStonePrimitiveRequestReceipt :
      Stone.PhysicalHilbertStonePrimitiveRequest

    selectedQuotientProjectionInnerProductSurfaceReceipt :
      SelectedQuotientProjectionInnerProductSurface

    selectedFixedDepthHilbertCompletenessSurfaceReceipt :
      FixedDepthHilbertCompletenessSurface

    selectedQuotientHilbertTopologyCompletionSurfaceReceipt :
      SelectedQuotientHilbertTopologyCompletionSurface

    selectedQuotientNondegenerateProjectionScalarSocketReceipt :
      SelectedQuotientNondegenerateProjectionScalarSocket

    selectedQuotientPostProjectionScalarSocketReceipt :
      SelectedQuotientPostProjectionScalarSocket

    selectedQuotientPostInnerProductWellDefinednessSocketReceipt :
      SelectedQuotientPostInnerProductWellDefinednessSocket

    selectedQuotientPostGlobalInnerProductWellDefinednessSocketReceipt :
      SelectedQuotientPostGlobalInnerProductWellDefinednessSocket

    selectedQuotientPostAcceptedHilbertCompletionSocketReceipt :
      SelectedQuotientPostAcceptedHilbertCompletionSocket

    selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosureReceipt :
      SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure

    gate5HilbertStonePhaseSpaceCarrierStepReceipt :
      Gate5HilbertStonePhaseSpaceCarrierStep

    gate5HilbertStoneTraversalDomainClosureWiringReceipt :
      Gate5HilbertStoneTraversalDomainClosureWiring

    selectedQuotientStrongContinuitySocketReceipt :
      SelectedQuotientStrongContinuitySocket

    formalPhysicalReversibleShadowReceipt :
      FormalPhysicalReversibleShadow

    finiteAdvanceTraversalSemigroupObstructionReceipt :
      SQD.SelectedFiniteAdvanceTraversalSemigroupObstruction

    physicalHilbertStoneBundleDataRequestReceipt :
      PhysicalHilbertStoneBundleDataRequest quotientDescentReceipt

    formalToPhysicalTraversalStoneUpgradeRequestReceipt :
      FormalToPhysicalTraversalStoneUpgradeRequest quotientDescentReceipt

    phaseSpaceTraversalGroupAndHilbertDataRequestReceipt :
      PhaseSpaceTraversalGroupAndHilbertDataRequest quotientDescentReceipt

    phaseSpacePhysicalTraversalStoneUpgradeAbsenceLedgerReceipt :
      PhaseSpacePhysicalTraversalStoneUpgradeAbsenceLedger quotientDescentReceipt

    discreteOneParameterGroupWrapperRequestReceipt :
      DiscreteOneParameterGroupWrapperRequest quotientDescentReceipt

    reversibleIntegerTraversalWrapperRequestReceipt :
      ReversibleIntegerTraversalWrapperRequest quotientDescentReceipt

    stormerVerletDiscreteStoneSurfaceRequestReceipt :
      StormerVerletDiscreteStoneSurfaceRequest quotientDescentReceipt

    hilbertTopologyScalarBlockerLedgerReceipt :
      HilbertTopologyScalarBlockerLedger quotientDescentReceipt

    formalFiniteStoneBundleConstructed :
      Bool

    formalFiniteStoneBundleConstructed-v :
      formalFiniteStoneBundleConstructed ≡ true

    realPhysicalStoneBundleConstructedFromCurrentData :
      Bool

    realPhysicalStoneBundleConstructedFromCurrentData-v :
      realPhysicalStoneBundleConstructedFromCurrentData ≡ false

    nonPromotionBoundary :
      List String

open SchrodingerSelfAdjointEvolutionReceipt public

schrodingerSelfAdjointEvolutionReceipt :
  {ℓw ℓr ℓq ℓn : Level} →
  SQD.SchrodingerQuotientDescentReceipt {ℓw} {ℓr} {ℓq} {ℓn} →
  SchrodingerSelfAdjointEvolutionReceipt {ℓw} {ℓr} {ℓq} {ℓn}
schrodingerSelfAdjointEvolutionReceipt quotientReceipt =
  record
    { quotientDescentReceipt =
        quotientReceipt
    ; openTargets =
        defaultSchrodingerSelfAdjointEvolutionOpenTargets
    ; firstMissingTheorem =
        defaultSchrodingerSelfAdjointEvolutionFirstMissingTheorem
    ; firstMissingTheorem-v =
        refl
    ; hilbertQuotientPromoted =
        false
    ; hilbertQuotientPromoted-v =
        refl
    ; oneParameterTraversalAutomorphismGroupPromoted =
        false
    ; oneParameterTraversalAutomorphismGroupPromoted-v =
        refl
    ; selfAdjointGeneratorPromoted =
        false
    ; selfAdjointGeneratorPromoted-v =
        refl
    ; stoneTheoremRoutePromoted =
        false
    ; stoneTheoremRoutePromoted-v =
        refl
    ; exponentialEvolutionFormulaPromoted =
        false
    ; exponentialEvolutionFormulaPromoted-v =
        refl
    ; schrodingerEquationTargetPromoted =
        false
    ; schrodingerEquationTargetPromoted-v =
        refl
    ; receiptStatus =
        selfAdjointEvolutionReceiptOnlyNoPromotion
    ; noPromotionWithoutAuthority =
        λ ()
    ; physicalTraversalAdapterRequest =
        SQD.physicalSchrodingerTraversalAdapterRequest
    ; advanceWavePhasePhysicalKernelExtensionalityRequest =
        SQD.advanceWavePhasePhysicalKernelExtensionalityRequest
    ; advanceWavePhaseObservationKernelPrimitiveRequest =
        SQD.advanceWavePhaseObservationKernelPrimitiveRequest
    ; shiftWavePhaseSelectedLinearPhaseEvidenceRequest =
        SQD.shiftWavePhaseSelectedLinearPhaseEvidenceRequest
    ; advanceWavePhaseKernelEqualityAdapterConstructed =
        false
    ; advanceWavePhaseKernelEqualityAdapterConstructed-v =
        refl
    ; selectedFiniteQuotientStoneAttemptReceipt =
        selectedFiniteQuotientStoneAttempt
    ; finiteSelfAdjointHamiltonianStoneDataReceipt =
        Stone.onePointFiniteSelfAdjointHamiltonianStoneData
    ; finiteDepthIdentityStoneTowerSkeletonReceipt =
        Stone.onePointFiniteDepthIdentityStoneTowerSkeleton
    ; selectedFiniteQuotientStoneGeneratorSpectralGapInterpretationSurfaceReceipt =
        selectedFiniteQuotientStoneGeneratorSpectralGapInterpretationReceipt
    ; physicalHilbertStonePrimitiveRequestReceipt =
        Stone.canonicalPhysicalHilbertStonePrimitiveRequest
    ; selectedQuotientProjectionInnerProductSurfaceReceipt =
        selectedQuotientProjectionInnerProductSurface
    ; selectedFixedDepthHilbertCompletenessSurfaceReceipt =
        selectedFiniteDepthHilbertCompletenessSurface 0
    ; selectedQuotientHilbertTopologyCompletionSurfaceReceipt =
        selectedQuotientHilbertTopologyCompletionSurface
    ; selectedQuotientNondegenerateProjectionScalarSocketReceipt =
        selectedQuotientNondegenerateProjectionScalarSocket
    ; selectedQuotientPostProjectionScalarSocketReceipt =
        selectedQuotientPostProjectionScalarSocket
    ; selectedQuotientPostInnerProductWellDefinednessSocketReceipt =
        selectedQuotientPostInnerProductWellDefinednessSocket
    ; selectedQuotientPostGlobalInnerProductWellDefinednessSocketReceipt =
        selectedQuotientPostGlobalInnerProductWellDefinednessSocket
    ; selectedQuotientPostAcceptedHilbertCompletionSocketReceipt =
        selectedQuotientPostAcceptedHilbertCompletionSocket
    ; selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosureReceipt =
        selectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure
    ; gate5HilbertStonePhaseSpaceCarrierStepReceipt =
        gate5HilbertStonePhaseSpaceCarrierStep
    ; gate5HilbertStoneTraversalDomainClosureWiringReceipt =
        gate5HilbertStoneTraversalDomainClosureWiring
    ; selectedQuotientStrongContinuitySocketReceipt =
        selectedQuotientStrongContinuitySocket
    ; formalPhysicalReversibleShadowReceipt =
        formalPhysicalReversibleShadow
    ; finiteAdvanceTraversalSemigroupObstructionReceipt =
        SQD.selectedFiniteAdvanceTraversalSemigroupObstruction
    ; physicalHilbertStoneBundleDataRequestReceipt =
        physicalHilbertStoneBundleDataRequest quotientReceipt
    ; formalToPhysicalTraversalStoneUpgradeRequestReceipt =
        formalToPhysicalTraversalStoneUpgradeRequest quotientReceipt
    ; phaseSpaceTraversalGroupAndHilbertDataRequestReceipt =
        phaseSpaceTraversalGroupAndHilbertDataRequest quotientReceipt
    ; phaseSpacePhysicalTraversalStoneUpgradeAbsenceLedgerReceipt =
        phaseSpacePhysicalTraversalStoneUpgradeAbsenceLedger quotientReceipt
    ; discreteOneParameterGroupWrapperRequestReceipt =
        discreteOneParameterGroupWrapperRequest quotientReceipt
    ; reversibleIntegerTraversalWrapperRequestReceipt =
        reversibleIntegerTraversalWrapperRequest quotientReceipt
    ; stormerVerletDiscreteStoneSurfaceRequestReceipt =
        stormerVerletDiscreteStoneSurfaceRequest quotientReceipt
    ; hilbertTopologyScalarBlockerLedgerReceipt =
        hilbertTopologyScalarBlockerLedger quotientReceipt
    ; formalFiniteStoneBundleConstructed =
        true
    ; formalFiniteStoneBundleConstructed-v =
        refl
    ; realPhysicalStoneBundleConstructedFromCurrentData =
        false
    ; realPhysicalStoneBundleConstructedFromCurrentData-v =
        refl
    ; nonPromotionBoundary =
        "SchrodingerSelfAdjointEvolutionReceipt consumes SchrodingerQuotientDescentReceipt as an upstream obligation only"
        ∷ "The physical traversal adapter request remains open: a kernel setoid plus a traversal respect proof is still required upstream"
        ∷ "The concrete advanceWavePhaseState equality fallback is inhabited, but no physical kernel instance is constructed here"
        ∷ "The non-collapsing physical route is narrowed to advanceWavePhaseKernelExtensionality and a SetoidQuotientSurface; quotient equality follows from quotientSound"
        ∷ "For observation/projection kernels, extensionality is mechanically derived from advanceWavePhaseObservationNaturality"
        ∷ "For the finite selected amplitude/phase coordinate observations, advanceWavePhaseObservationNaturality is typechecked without promoting a physical quotient"
        ∷ "The selected linear/phase primitive is inhabited only by degenerate coordinate algebra: left-projection addition, unit-scalar identity scaling, and identity finite Phase4 action"
        ∷ "The selected finite coordinate SetoidQuotientSurface is inhabited; the remaining physical primitive is any nondegenerate projection algebra needed to replace that coordinate-only evidence"
        ∷ "SelectedQuotientProjectionInnerProductSurface now ties the two-point noncollapsed precursor to the selected finite quotient carrier and proves representative-independent finite quotient inner-product well-definedness"
        ∷ "HilbertQuotientDependencyObstruction records the first missing theorem: quotient carrier plus Hilbert inner-product/completion structure"
        ∷ "PhysicalHilbertStoneBundleDataRequest is the fail-closed typed request for projection algebra, inner product, completion, traversal group, strong continuity, and Stone bundle data"
        ∷ "SelectedFiniteQuotientStoneAttempt records the exact result of trying the finite Stone route: DASHI.Quantum.Stone accepts a formal identity bundle over the selected finite quotient carrier"
        ∷ "That formal finite bundle uses zero inner product, identity U(t), identity generator, zero distance, and trivial continuity, so it is not a physical Hilbert/Stone/Schrodinger promotion"
        ∷ "The selected quotient projection inner-product surface is separate from that formal zero-inner-product Stone attempt and does not construct completion, traversal, or a physical Stone bundle"
        ∷ "SelectedQuotientHilbertTopologyCompletionSurface now packages a finite selected-quotient topology/completion precursor around that representative-independent projection inner product"
        ∷ "SelectedQuotientNondegenerateProjectionScalarSocket now isolates the first scalar/projection blocker between finite quotient evidence and physical Hilbert completion"
        ∷ "SelectedQuotientPostProjectionScalarSocket marks selected finite first-field progress and makes quotientInnerProductWellDefinednessField the next exact theorem blocker on that lane"
        ∷ "SelectedQuotientPostInnerProductWellDefinednessSocket marks selected finite second-field progress and makes globalPhysicalQuotientInnerProductWellDefinednessField the next exact theorem blocker on that lane"
        ∷ "SelectedQuotientPostGlobalInnerProductWellDefinednessSocket marks selected finite third-field progress and makes acceptedHilbertCompletionField the next exact theorem blocker on that lane"
        ∷ "SelectedQuotientPostAcceptedHilbertCompletionSocket marks selected finite fourth-field progress while keeping acceptedHilbertCompletionPromoted fixed false"
        ∷ "Gate5HilbertStonePhaseSpaceCarrierStep packages the selected finite quotient carrier, projection inner product, finite depth embedding/traversal compatibility, finite-support domain, and symmetric generator-domain target as one non-promoting typed phase-space step"
        ∷ "SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure adds finite-depth reversible identity traversal laws and StoneSelfAdjoint generator-domain closure over the selected quotient projection system, without promoting the selected irreversible finite advance"
        ∷ "Gate5HilbertStoneTraversalDomainClosureWiring composes that closure through the Gate5 carrier step and re-exports inverse, domain-closure, generator-commutation, and finite-depth StoneSelfAdjoint laws"
        ∷ "SelectedQuotientStrongContinuitySocket now pins the exact missing strong-continuity primitive against the semigroup-only selected finite advance"
        ∷ "DASHI.Quantum.Stone also supplies a one-point finite self-adjoint Hamiltonian/Stone witness with nonzero unique-point inner product"
        ∷ "That one-point witness now lifts to a reusable constant-depth identity tower: H_d is constant, iota_d is identity, U_d is identity, and depth compatibility is reflexive"
        ∷ "The constant-depth identity tower is finite-only and collapsed; it does not supply noncollapsed physical H_d, Hamiltonian domain data, Hilbert completion, or the physical Stone bridge boundary"
        ∷ "The fixed-depth Hilbert completeness surface is inhabited only at depth 0 for the finite selected quotient carrier, with colimit and physical-limit claims fixed false"
        ∷ "SelectedFiniteQuotientStoneGeneratorSpectralGapInterpretationReceipt records bounded typed progress for the selected finite quotient generator and spectral-gap interpretation while keeping global phase-space, traversal-derived Stone bundle, self-adjoint colimit generator, and real spectral-gap lower-bound targets open"
        ∷ "FormalPhysicalReversibleShadow now supplies a one-point physical reversible identity traversal plus one-point identity Stone route"
        ∷ "That formal shadow is not the selected irreversible advance: its finite shadow is constantly the held endpoint, while the selected finite table remains start -> next -> held with no preimage of start"
        ∷ "The formal shadow produces a supplied Stone route only after collapsing all quotient points to tt, and schrodingerEquationPromotedFromShadow remains false"
        ∷ "advanceWavePhaseState descends to a nontrivial finite quotient traversal, but SelectedFiniteAdvanceTraversalSemigroupObstruction proves it is not a traversal group because shiftStartPoint has no preimage"
        ∷ "SelectedFinitePhaseSpaceReversibleTraversalObstruction packages the available finite amplitude/phase transport and proves the current advance cannot supply a reversible phase-space traversal"
        ∷ "PhaseSpaceTraversalGroupAndHilbertDataRequest is the narrow supplied-interface route: candidate inverse laws plus scalar field, time inverse law, quotient inner product, strong continuity, and Stone bundle"
        ∷ "PhaseSpacePhysicalTraversalStoneUpgradeAbsenceLedger records the exact missing scalar, time, norm/inner-product, Hilbert, strong-continuity, and traversal-derived StoneBundle data"
        ∷ "FormalToPhysicalTraversalStoneUpgradeRequest names the typed bridge that would upgrade the formal finite attempt: physical projection algebra, quotient inner-product well-definedness, completion, physicalUnitary, StoneBundle, and a time-1 comparison to the finite advance"
        ∷ "DiscreteOneParameterGroupWrapperRequest records the supplied discrete time group wrapper without promoting the irreversible selected finite advance to a group"
        ∷ "ReversibleIntegerTraversalWrapperRequest fixes the requested reversible discrete wrapper to Data.Integer.ℤ while keeping the integer group laws, action laws, and finite-step comparison supplied and non-promoted"
        ∷ "StormerVerletDiscreteStoneSurfaceRequest records the supplied reversible phase-space/Störmer-Verlet route, with quotient-shadow comparison only and no inverse promotion for the selected finite advance"
        ∷ "HilbertTopologyScalarBlockerLedger names the exact remaining scalar, quotient inner-product, Hilbert topology, strong-continuity, and self-adjoint domain blockers"
        ∷ "The real physical StoneBundle from current quotient data remains false because the projection algebra, quotient inner product/completion, physical traversal group, strong continuity for that traversal, and physical generator data are absent"
        ∷ "No global spectral-gap lower-bound theorem, Clay/global mass-gap promotion, or selfAdjointColimitGeneratorPromoted claim is introduced by the bounded interpretation receipt"
        ∷ "One-parameter traversal automorphism group construction remains open"
        ∷ "Trit inversion is available as an involutive time-reversal candidate, but no traversal/Hilbert bridge is supplied"
        ∷ "StoneBundleSelfAdjointRoute records the exact supplied-bundle route: a StoneBundle gives Stone consequences and its self-adjoint generator"
        ∷ "StoneBundleConstructionObstruction records the later missing primitive: a StoneBundle built from quotient traversal, not the Stone consequence once such a bundle is supplied"
        ∷ "Self-adjoint generator and Stone theorem route remain open"
        ∷ "U(t)=exp(-iHt/hbar) and the Schrodinger equation target remain open"
        ∷ "This receipt does not prove Schrodinger closure, a self-adjoint Hamiltonian, spectral theorem, or unitary evolution"
        ∷ []
    }

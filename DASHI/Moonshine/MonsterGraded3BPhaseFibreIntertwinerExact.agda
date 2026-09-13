module DASHI.Moonshine.MonsterGraded3BPhaseFibreIntertwinerExact where

------------------------------------------------------------------------
-- RECOGNIZED 3B ACTUAL SECTOR -> GRADE-WISE SIGNED FIBRE
--
-- This consumes the repository's SAME selected Monster element used by the
-- graded-trace and literal-VOA action surfaces, plus ActualZetaSectorRecognition.
-- A grade assignment must carry an explicit membership receipt.  The actual
-- modulation exponent is then the signed trit; no trace->sign classifier is
-- invented.  Boundary gluing remains unclassified until j-geometry supplies it.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import Base369 as Base

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.MonsterGradedVOABridgeExact as Legacy
import DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact as Weld
import DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact as Selected
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Actual
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Base369Monster3BActualSectorRecognitionBidiExact as Base369Rec
import DASHI.Moonshine.MonsterGradedSignedFibreBidiExact as Fibre
import DASHI.Foundations.Base369SignedMembershipExact as Signed
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Gluing

selectedGroup :
  ∀ {Monster K} →
  Selected.Selected3BRecognizedSameElementSource Monster K →
  GR.Group Monster
selectedGroup source =
  GVOA.group
    (Legacy.voaAction
      (Weld.gradedAuthority
        (Selected.weld (Selected.selectedSource source))))

selectedGraded :
  ∀ {Monster K}
    (source : Selected.Selected3BRecognizedSameElementSource Monster K) →
  GR.GradedRepresentation Monster K (selectedGroup source)
selectedGraded source =
  GVOA.gradedRepresentation
    (Legacy.voaAction
      (Weld.gradedAuthority
        (Selected.weld (Selected.selectedSource source))))

ActualSector :
  ∀ {Monster K} →
  Selected.Selected3BRecognizedSameElementSource Monster K → Set
ActualSector source =
  Selected.selectedLiteralZetaSector (Selected.selectedSource source)

record GradeWiseRecognizedSectorAssignment
  {Monster K : Set}
  (source : Selected.Selected3BRecognizedSameElementSource Monster K) : Set₁ where
  field
    GradeMembership : Nat → ActualSector source → Set
    stateAt : (grade : Nat) → ActualSector source
    stateAtGrade : (grade : Nat) → GradeMembership grade (stateAt grade)
    axisAt : Nat → H.Axis6

open GradeWiseRecognizedSectorAssignment public

recognizedBase369 :
  ∀ {Monster K}
    (source : Selected.Selected3BRecognizedSameElementSource Monster K) →
  Base369Rec.ActualBase369SectorRecognition (ActualSector source)
recognizedBase369 source =
  Base369Rec.composeActualRecognitionWithBase369 (Selected.recognition source)

observedTritAt :
  ∀ {Monster K}
    {source : Selected.Selected3BRecognizedSameElementSource Monster K} →
  GradeWiseRecognizedSectorAssignment source → Nat → Trit
observedTritAt {source = source} assignment grade =
  Actual.actualModulationExponent
    (Selected.recognition source)
    (axisAt assignment grade)
    (stateAt assignment grade)

tritToSignedOrientation : Trit → Signed.FibredOrientation
tritToSignedOrientation neg = Signed.inverseOrientation
tritToSignedOrientation zer =
  Signed.fibredOrientation Base.tri-mid Signed.zeroBalanced
tritToSignedOrientation pos = Signed.goodOrientation

recognizedGradeSignedObserver :
  ∀ {Monster K}
    {source : Selected.Selected3BRecognizedSameElementSource Monster K} →
  GradeWiseRecognizedSectorAssignment source →
  Fibre.GradedSignedFibreObserver (selectedGroup source) (selectedGraded source)
recognizedGradeSignedObserver assignment = record
  { signedOrientationAt = λ grade →
      tritToSignedOrientation (observedTritAt assignment grade)
  ; gluingAt = λ grade → Gluing.unclassifiedBoundary
  ; observerUsesSameGradeIndex = true
  }

observedTritIntertwinesBase369 :
  ∀ {Monster K}
    {source : Selected.Selected3BRecognizedSameElementSource Monster K} →
  (assignment : GradeWiseRecognizedSectorAssignment source) →
  (grade : Nat) →
  observedTritAt assignment grade
  ≡ Base369Rec.base369ModulationExponent
      (axisAt assignment grade)
      (proj₁
        (Base369Rec.toBase369 (recognizedBase369 source)
          (stateAt assignment grade)))
observedTritIntertwinesBase369 {source = source} assignment grade =
  Base369Rec.actualModulationExponentIntertwinesBase369
    (Selected.recognition source)
    (axisAt assignment grade)
    (stateAt assignment grade)

record GradeWiseMonsterSignedFibreClosure : Set where
  constructor grade-wise-monster-signed-fibre-closure
  field
    sameSelectedElementFeedsTraceAndAction : Bool
    actualSectorRecognitionConsumed : Bool
    gradeMembershipReceiptRequired : Bool
    actualModulationTritUsed : Bool
    base369IntertwinerReused : Bool
    signedOrientationCompiledAtEveryGrade : Bool
    traceValueAloneUsedAsSign : Bool
    jBoundaryGluingInferredFromMonsterAction : Bool

canonicalGradeWiseMonsterSignedFibreClosure : GradeWiseMonsterSignedFibreClosure
canonicalGradeWiseMonsterSignedFibreClosure =
  grade-wise-monster-signed-fibre-closure
    true true true true true true false false

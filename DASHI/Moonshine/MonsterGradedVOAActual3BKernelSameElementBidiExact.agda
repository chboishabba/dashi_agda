module DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact where

------------------------------------------------------------------------
-- SELECTED LITERAL VOA 3B ELEMENT <-> ACTUAL MN3B KERNEL/CHARACTER RECEIPT
--
-- The selected-3B same-element owner gives one literal Monster element that
-- simultaneously carries:
--
--   * the legacy grade-two trace/character observation, and
--   * the literal VOA state action / zeta-eigenspace action.
--
-- Separately, Monster3BActualKernelCharacterPromotionExact owns the actual
-- AtlasRep/CTblLib kernel structure and class-character recognition.  Its
-- domain is an abstract ActualKernelClass, not a literal Monster element.
--
-- This owner makes the remaining SAME-OBJECT payment explicit: a relation
-- saying that the selected literal VOA element represents the certified
-- central-zeta kernel class.  Once that receipt is supplied, the existing
-- kernel theorem immediately yields the 65610 zeta amplitude and the
-- ninety-fold Heisenberg character isotypy for the class represented by that
-- same selected element.
--
-- Trace 53 is also attached to the selected element through an explicit
-- Nat -> K scalar embedding.  Neither trace 53 nor order three alone is allowed
-- to identify Monster class 3B.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact as Selected
import DASHI.Moonshine.Monster3BActualKernelCharacterPromotionExact as Kernel
import DASHI.Moonshine.Monster3BKernelCharacterCriterionExact as Character
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Recognition

------------------------------------------------------------------------
-- 1. Same-element attachment to the actual kernel class surface.
------------------------------------------------------------------------

record Actual3BKernelSameElementAttachment (Monster K : Set) : Setω where
  field
    selectedSource : Selected.Selected3BSameElementSource Monster K
    kernelPromotion : Kernel.ActualKernelCharacterPromotion

    -- Explicit relation between literal Monster elements and the independently
    -- certified kernel-class carrier.  This is intentionally data, not inferred
    -- from a matching trace or order.
    RepresentsKernelClass :
      Monster → Kernel.ActualKernelClass kernelPromotion → Set

    centralZetaKernelClass :
      Kernel.ClassifiedKernelClass
        kernelPromotion Character.centralZetaClass

    selectedElementRepresentsCentralZetaClass :
      RepresentsKernelClass
        (Selected.selectedCentralElement selectedSource)
        (Kernel.class centralZetaKernelClass)

    -- Attach the ordinary grade-two trace 53 to this SAME selected element.
    natScalar : Nat → K
    selectedGradeTwoTraceIs53 :
      Selected.selectedCentralGradeTwoTrace selectedSource
      ≡ natScalar 53

    -- Class fusion / element authority remains explicit rather than being
    -- inferred from 53.  This is the receipt that the represented kernel class
    -- is the certified class fusing to Monster 3B.
    representedKernelClassFusesToMonster3B : Set

open Actual3BKernelSameElementAttachment public

------------------------------------------------------------------------
-- 2. Existing actual-kernel character consequences become same-element
--    consequences once the representation receipt above is supplied.
------------------------------------------------------------------------

selectedKernelClass :
  ∀ {Monster K} →
  (attachment : Actual3BKernelSameElementAttachment Monster K) →
  Kernel.ActualKernelClass (kernelPromotion attachment)
selectedKernelClass attachment =
  Kernel.class (centralZetaKernelClass attachment)

selectedKernelClassIsCentralZeta :
  ∀ {Monster K}
    (attachment : Actual3BKernelSameElementAttachment Monster K) →
  Kernel.classifyKernelClass
    (kernelPromotion attachment)
    (selectedKernelClass attachment)
  ≡ Character.centralZetaClass
selectedKernelClassIsCentralZeta attachment =
  Kernel.classification (centralZetaKernelClass attachment)

selectedActualRestrictedCharacter :
  ∀ {Monster K} →
  (attachment : Actual3BKernelSameElementAttachment Monster K) →
  Character.CyclotomicTrace3
selectedActualRestrictedCharacter attachment =
  Kernel.actualRestrictedCharacter
    (kernelPromotion attachment)
    (selectedKernelClass attachment)

selectedCentralZetaAmplitudeIs65610 :
  ∀ {Monster K}
    (attachment : Actual3BKernelSameElementAttachment Monster K) →
  Character.coefficientZeta (selectedActualRestrictedCharacter attachment)
  ≡ 65610
selectedCentralZetaAmplitudeIs65610 attachment =
  Kernel.actualKernelCentralCharacterIsZeta
    (kernelPromotion attachment)
    (centralZetaKernelClass attachment)

selectedKernelNinetyHeisenbergIsotypy :
  ∀ {Monster K}
    (attachment : Actual3BKernelSameElementAttachment Monster K) →
  Kernel.NinetyHeisenbergCharacterIsotypy (kernelPromotion attachment)
selectedKernelNinetyHeisenbergIsotypy attachment =
  Kernel.actualZetaSectorIsNinetyHeisenbergCopies
    (kernelPromotion attachment)

selectedKernelMultiplicityIsNinety :
  ∀ {Monster K}
    (attachment : Actual3BKernelSameElementAttachment Monster K) →
  Kernel.multiplicity (selectedKernelNinetyHeisenbergIsotypy attachment) ≡ 90
selectedKernelMultiplicityIsNinety attachment =
  Kernel.multiplicityIsNinety
    (selectedKernelNinetyHeisenbergIsotypy attachment)

------------------------------------------------------------------------
-- 3. The literal VOA zeta sector remains the recognition target.  Character
--    isotypy supplies strong evidence/constraints but does not construct the
--    action intertwiner.
------------------------------------------------------------------------

selectedLiteralZetaSector :
  ∀ {Monster K} →
  Actual3BKernelSameElementAttachment Monster K → Set
selectedLiteralZetaSector attachment =
  Selected.selectedLiteralZetaSector (selectedSource attachment)

record Actual3BKernelRecognizedSameElementAttachment
    (Monster K : Set) : Setω where
  field
    attachment : Actual3BKernelSameElementAttachment Monster K
    recognition :
      Recognition.ActualZetaSectorRecognition
        (selectedLiteralZetaSector attachment)

open Actual3BKernelRecognizedSameElementAttachment public

------------------------------------------------------------------------
-- 4. BIDI boundary.
------------------------------------------------------------------------

record Actual3BKernelSameElementBoundary : Set where
  constructor actual3BKernelSameElementBoundary
  field
    literalSelectedElementAvailable : Bool
    actualKernelClassAuthorityAvailable : Bool
    explicitElementToKernelClassReceiptRequired : Bool
    selectedElementAttachedToCentralZetaClass : Bool
    selectedGradeTwoTrace53Attached : Bool
    centralZetaAmplitude65610CompilerAvailable : Bool
    ninetyHeisenbergCharacterIsotypyCompilerAvailable : Bool
    trace53AloneIdentifiesMonster3B : Bool
    characterIsotypyConstructsActionIntertwiner : Bool
    actualZetaRecognitionProvedHere : Bool
    fullHyperfabricMonsterActionProvedHere : Bool

canonicalActual3BKernelSameElementBoundary : Actual3BKernelSameElementBoundary
canonicalActual3BKernelSameElementBoundary =
  actual3BKernelSameElementBoundary
    true true true true true true true
    false false false false

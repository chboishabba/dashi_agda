module DASHI.Reasoning.Trialectic369SchrodingerHZetaRecognitionMaxCutExact where

------------------------------------------------------------------------
-- CANONICAL H_zeta MAX-CUT THROUGH THE EXPLICIT SCHRODINGER REPRESENTATION
--
-- DASHI CONTRIBUTION
--
-- The finite Schrodinger function model is now an actual repo-native linear
-- carrier/action candidate with the full Heisenberg action law paid.
--
-- Therefore CanonicalLinearHomSameObjectWeld no longer needs to choose an
-- arbitrary HilbertLift for H_zeta.  Fix it to:
--
--   Schrodinger.schrodingerHilbertLift.
--
-- Remaining source recognition is exactly:
--
--   * this explicit linear representation is the actual H_zeta constituent;
--   * its Heisenberg action is the same actual extraspecial-kernel action.
--
-- The finite model, degree 729, shared zeta scalar and irreducibility do not
-- manufacture those two same-object recognition receipts.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as Function
import DASHI.Moonshine.Monster3BFiniteSchrodingerHilbertLiftExact as Schrodinger
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core

------------------------------------------------------------------------
-- 1. Actual-source recognition of the now-fixed H_zeta candidate.
------------------------------------------------------------------------

record SchrodingerIsActualHZeta : Set₁ where
  field
    actualHZetaRecognition : Set
    actualHZetaActionIntertwiner : Set

open SchrodingerIsActualHZeta public

------------------------------------------------------------------------
-- 2. Hom-space carrier bindings to the fixed H_zeta and selected W_zeta.
------------------------------------------------------------------------

record SchrodingerHomCarrierBindings
    (producer : LinearZeta.LinearSingleActionProducer)
    (homSpace : Hom.ActualLinearMultiplicityHomSpace)
    : Set₁ where
  field
    heisenbergCarrierIsSchrodinger :
      Hom.HeisenbergCarrier homSpace
      ≡ Function.SchrodingerFunction

    chosenZetaCarrierIsSelectedLinearWZeta :
      Hom.ChosenZetaCarrier homSpace
      ≡ Linear.Vector (LinearZeta.zetaLinearCarrier producer)

open SchrodingerHomCarrierBindings public

------------------------------------------------------------------------
-- 3. Compile the canonical Hom same-object weld.
------------------------------------------------------------------------

canonicalHomWeldFromSchrodinger :
  (producer : LinearZeta.LinearSingleActionProducer) →
  (homSpace : Hom.ActualLinearMultiplicityHomSpace) →
  SchrodingerHomCarrierBindings producer homSpace →
  SchrodingerIsActualHZeta →
  Core.CanonicalLinearHomSameObjectWeld producer homSpace
canonicalHomWeldFromSchrodinger producer homSpace bindings recognition =
  record
    { actualHZetaLinearCarrier =
        Schrodinger.schrodingerHilbertLift

    ; homHeisenbergCarrierIsActualHZeta =
        heisenbergCarrierIsSchrodinger bindings

    ; homChosenZetaCarrierIsActualWZeta =
        chosenZetaCarrierIsSelectedLinearWZeta bindings

    ; actualHZetaRecognition =
        actualHZetaRecognition recognition

    ; actualHZetaActionIntertwiner =
        actualHZetaActionIntertwiner recognition
    }

------------------------------------------------------------------------
-- 4. The linear H_zeta carrier/action construction itself is now paid.
------------------------------------------------------------------------

schrodingerHilbertBoundary :
  Schrodinger.SchrodingerHilbertLiftBoundary
schrodingerHilbertBoundary =
  Schrodinger.canonicalSchrodingerHilbertLiftBoundary

linearHZetaCandidateCarrierPaid :
  Schrodinger.hilbertLiftPackaged schrodingerHilbertBoundary
  ≡ true
linearHZetaCandidateCarrierPaid = refl

linearHZetaCandidateActionPaid :
  Schrodinger.fullHeisenbergLinearActionPackaged schrodingerHilbertBoundary
  ≡ true
linearHZetaCandidateActionPaid = refl

linearHZetaCandidateActionLawPaid :
  Schrodinger.fullActionLawReceiptConsumed schrodingerHilbertBoundary
  ≡ true
linearHZetaCandidateActionLawPaid = refl

------------------------------------------------------------------------
-- 5. Firewalls.
------------------------------------------------------------------------

data Degree729CreatesMonsterHZetaRecognition : Set where
data FiniteIrreducibilityCreatesMonsterHZetaRecognition : Set where
data SharedZetaScalarCreatesMonsterHZetaRecognition : Set where
data SchrodingerConstructionCreatesHomCarrierBinding : Set where

degreeDoesNotCreateRecognition :
  Degree729CreatesMonsterHZetaRecognition → ⊥
degreeDoesNotCreateRecognition ()

irreducibilityDoesNotCreateRecognition :
  FiniteIrreducibilityCreatesMonsterHZetaRecognition → ⊥
irreducibilityDoesNotCreateRecognition ()

sameScalarDoesNotCreateRecognition :
  SharedZetaScalarCreatesMonsterHZetaRecognition → ⊥
sameScalarDoesNotCreateRecognition ()

constructionDoesNotCreateHomBinding :
  SchrodingerConstructionCreatesHomCarrierBinding → ⊥
constructionDoesNotCreateHomBinding ()

------------------------------------------------------------------------
-- 6. Machine-readable frontier.
------------------------------------------------------------------------

record Trialectic369SchrodingerHZetaRecognitionMaxCutBoundary : Set where
  constructor trialectic-369-schrodinger-hzeta-recognition-maxcut-boundary
  field
    explicitSchrodingerHilbertCarrierPaid : Bool
    explicitHeisenbergActionPaid : Bool
    fullHeisenbergActionLawPaid : Bool
    arbitraryHZetaHilbertChoiceEliminated : Bool
    canonicalHomWeldCompilerOwned : Bool
    homCarrierBindingsInhabitedHere : Bool
    actualHZetaRecognitionInhabitedHere : Bool
    actualHZetaActionIntertwinerInhabitedHere : Bool
    canonicalHomWeldInhabitedHere : Bool

canonicalTrialectic369SchrodingerHZetaRecognitionMaxCutBoundary :
  Trialectic369SchrodingerHZetaRecognitionMaxCutBoundary
canonicalTrialectic369SchrodingerHZetaRecognitionMaxCutBoundary =
  trialectic-369-schrodinger-hzeta-recognition-maxcut-boundary
    true true true true true
    false false false false

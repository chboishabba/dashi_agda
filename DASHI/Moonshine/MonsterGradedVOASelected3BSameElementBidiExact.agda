module DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact where

------------------------------------------------------------------------
-- SELECTED 3B SOURCE ON THE SAME GRADED-TRACE / LITERAL-ACTION VOA OBJECT
--
-- Previous owners now expose exactly complementary pieces:
--
--   MonsterGradedVOALiteralActionSameObjectBidiExact
--     one Monster element type simultaneously indexes
--       * exact legacy graded trace / character authority, and
--       * literal VOA state action;
--
--   Base369Monster3BVOAActionPhaseAdapterBidiExact
--     a selected central order-three candidate, inverse, cyclotomic phase
--     scalar map and normalizer preserve/invert receipts on a literal
--     MoonshineVOABridge.
--
-- This owner prevents those two surfaces from drifting apart.  The selected
-- 3B phase source must use the literal MoonshineVOABridge already welded to
-- the graded trace authority.  Consequently the chosen central element is a
-- single element that can be fed both to the exact grade-two trace probe and
-- to the literal VOA action / zeta-eigenspace machinery.
--
-- No 3B class identification is proved here merely from order/trace data, and
-- ActualZetaSectorRecognition remains a separate scientific receipt.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact as Weld
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as Phase

------------------------------------------------------------------------
-- 1. Same-bridge selected-3B package.
------------------------------------------------------------------------

record Selected3BSameElementSource (Monster K : Set) : Setω where
  field
    weld : Weld.MonsterGradedVOALiteralActionWeld Monster K

    phaseSource :
      Phase.ActualMonster3BVOAPhaseActionSource Monster K
        (GVOA.group
          (DASHI.Moonshine.MonsterGradedVOABridgeExact.voaAction
            (Weld.gradedAuthority weld)))

    -- This is the decisive same-object payment.  The phase source is not
    -- permitted to bring a second literal VOA bridge with the same-looking
    -- carrier/action.
    phaseSourceUsesWeldLiteralVOA :
      Phase.bridge phaseSource ≡ Weld.literalVOA weld

open Selected3BSameElementSource public

------------------------------------------------------------------------
-- 2. The selected element now has both observations by construction.
------------------------------------------------------------------------

selectedCentralElement :
  ∀ {Monster K} → Selected3BSameElementSource Monster K → Monster
selectedCentralElement source =
  Phase.centralElement (phaseSource source)

selectedCentralInverseElement :
  ∀ {Monster K} → Selected3BSameElementSource Monster K → Monster
selectedCentralInverseElement source =
  Phase.centralInverseElement (phaseSource source)

selectedCentralGradeTwoTrace :
  ∀ {Monster K} → Selected3BSameElementSource Monster K → K
selectedCentralGradeTwoTrace source =
  Weld.gradeTwoTrace (weld source) (selectedCentralElement source)

------------------------------------------------------------------------
-- 3. The literal zeta-sector target is inherited from that exact phase source.
------------------------------------------------------------------------

selectedLiteralZetaSector :
  ∀ {Monster K} → Selected3BSameElementSource Monster K → Set
selectedLiteralZetaSector source =
  Phase.literalVOAZetaSector (phaseSource source)

------------------------------------------------------------------------
-- 4. Recognition remains the one live representation-theoretic leaf.
------------------------------------------------------------------------

record Selected3BRecognizedSameElementSource (Monster K : Set) : Setω where
  field
    selectedSource : Selected3BSameElementSource Monster K
    recognition :
      DASHI.Moonshine.Monster3BMultiplicityEvaluationExact.ActualZetaSectorRecognition
        (selectedLiteralZetaSector selectedSource)

open Selected3BRecognizedSameElementSource public

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record Selected3BSameElementBoundary : Set where
  constructor selected3BSameElementBoundary
  field
    selectedElementSharesCharacterAndActionAuthority : Bool
    phaseSourceMustUseExactWeldedVOABridge : Bool
    gradeTwoTraceProbeAvailableOnSelectedElement : Bool
    literalZetaSectorGeneratedFromSameSelectedElement : Bool
    selectedElementProvedMonsterClass3BHere : Bool
    traceValue53AloneIdentifies3B : Bool
    actualZetaRecognitionProvedHere : Bool
    fullMonsterActionOnHyperfabricProvedHere : Bool

canonicalSelected3BSameElementBoundary : Selected3BSameElementBoundary
canonicalSelected3BSameElementBoundary =
  selected3BSameElementBoundary
    true true true true
    false false false false

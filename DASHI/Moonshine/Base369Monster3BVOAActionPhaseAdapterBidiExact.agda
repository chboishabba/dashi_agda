module DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact where

------------------------------------------------------------------------
-- VOA ACTION -> LITERAL MONSTER 3B PHASE ACTION ADAPTER
--
-- The repository already has two relevant exact owners:
--
--   * VertexOperatorAlgebraCore: an action on the literal graded-module
--     Carrier of a Moonshine-facing VOA bridge;
--   * C3CyclotomicAmplitudeAlgebraExact: exact 1, zeta, zeta^2 and zero in
--     Q(zeta_3).
--
-- This adapter keeps the roles distinct:
--
--   1, zeta, zeta^2  = eigenphase scalars;
--   zero              = additive/trace vanishing datum, NOT a fourth phase.
--
-- The scientific receipts below identify a selected order-three central
-- action and its normalizer behaviour on the SAME literal VOA carrier.  Once
-- those receipts and ActualZetaSectorRecognition on the resulting literal
-- zeta eigenspace are supplied, the existing single-action BIDI compiler owns
-- the rest.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Recognition
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single

------------------------------------------------------------------------
-- 1. Exact cyclotomic phase chart.
------------------------------------------------------------------------

phaseCyclotomic : Inertia.CentralPhase3 → C3.Cyclotomic3
phaseCyclotomic Inertia.phaseOne = C3.one
phaseCyclotomic Inertia.phaseZeta = C3.zeta
phaseCyclotomic Inertia.phaseZetaSquared = C3.zetaSquared

phaseOneIsOne : phaseCyclotomic Inertia.phaseOne ≡ C3.one
phaseOneIsOne = refl

phaseZetaIsZeta : phaseCyclotomic Inertia.phaseZeta ≡ C3.zeta
phaseZetaIsZeta = refl

phaseZetaSquaredIsZetaSquared :
  phaseCyclotomic Inertia.phaseZetaSquared ≡ C3.zetaSquared
phaseZetaSquaredIsZetaSquared = refl

-- `zero` belongs to the same amplitude algebra but is not in the image of the
-- three-phase chart.  This makes the user's remembered zeta/zeta^2/0 cluster
-- precise without turning trace/additive zero into an eigenphase.
zeroIsNotPhaseOne : C3.zero ≡ phaseCyclotomic Inertia.phaseOne → ⊥
zeroIsNotPhaseOne ()

zeroIsNotPhaseZeta : C3.zero ≡ phaseCyclotomic Inertia.phaseZeta → ⊥
zeroIsNotPhaseZeta ()

zeroIsNotPhaseZetaSquared :
  C3.zero ≡ phaseCyclotomic Inertia.phaseZetaSquared → ⊥
zeroIsNotPhaseZetaSquared ()

------------------------------------------------------------------------
-- 2. Carrier aliases from the existing Moonshine VOA owner.
------------------------------------------------------------------------

VOACarrier :
  ∀ {G K : Set} {group : GR.Group G} →
  VOA.MoonshineVOABridge G K group → Set
VOACarrier bridge =
  VOA.GradedModule.Carrier (VOA.gradedModule (VOA.voa bridge))

VOAScalar :
  ∀ {G K : Set} {group : GR.Group G} →
  VOA.MoonshineVOABridge G K group → Set
VOAScalar bridge =
  VOA.GradedModule.Scalar (VOA.gradedModule (VOA.voa bridge))

------------------------------------------------------------------------
-- 3. Same-carrier receipts attaching the order-three/cyclotomic structure to
--    the already-owned literal VOA action.
------------------------------------------------------------------------

record ActualMonster3BVOAPhaseActionSource
    (G K : Set)
    (group : GR.Group G) : Setω where
  field
    bridge : VOA.MoonshineVOABridge G K group

    centralElement : G
    centralInverseElement : G

    -- Embed the exact Q(zeta_3) amplitudes into the scalar carrier already
    -- used by this same VOA module.
    cyclotomicScalar : C3.Cyclotomic3 → VOAScalar bridge

    -- Classify actual normalizer elements as preserving or inverting the
    -- chosen central generator.
    preservesOrInverts : G → Bool

    -- The following receipts are stated directly on the literal VOA Carrier.
    inverseCentralOnEigenstate :
      (phase : Inertia.CentralPhase3) →
      (state : VOACarrier bridge) →
      VOA.VOAGroupAction.act (VOA.monsterAction bridge) centralElement state
      ≡ VOA.GradedModule._·_
          (VOA.gradedModule (VOA.voa bridge))
          (cyclotomicScalar (phaseCyclotomic phase)) state →
      VOA.VOAGroupAction.act (VOA.monsterAction bridge) centralInverseElement state
      ≡ VOA.GradedModule._·_
          (VOA.gradedModule (VOA.voa bridge))
          (cyclotomicScalar (phaseCyclotomic (Inertia.invertPhase phase))) state

    preservingIntertwiner :
      (normalizer : G) →
      preservesOrInverts normalizer ≡ true →
      (state : VOACarrier bridge) →
      VOA.VOAGroupAction.act (VOA.monsterAction bridge) centralElement
        (VOA.VOAGroupAction.act (VOA.monsterAction bridge) normalizer state)
      ≡ VOA.VOAGroupAction.act (VOA.monsterAction bridge) normalizer
          (VOA.VOAGroupAction.act (VOA.monsterAction bridge) centralElement state)

    invertingIntertwiner :
      (normalizer : G) →
      preservesOrInverts normalizer ≡ false →
      (state : VOACarrier bridge) →
      VOA.VOAGroupAction.act (VOA.monsterAction bridge) centralElement
        (VOA.VOAGroupAction.act (VOA.monsterAction bridge) normalizer state)
      ≡ VOA.VOAGroupAction.act (VOA.monsterAction bridge) normalizer
          (VOA.VOAGroupAction.act
            (VOA.monsterAction bridge) centralInverseElement state)

    phaseLinearity :
      (normalizer : G) →
      (phase : Inertia.CentralPhase3) →
      (state : VOACarrier bridge) →
      VOA.VOAGroupAction.act (VOA.monsterAction bridge) normalizer
        (VOA.GradedModule._·_
          (VOA.gradedModule (VOA.voa bridge))
          (cyclotomicScalar (phaseCyclotomic phase)) state)
      ≡ VOA.GradedModule._·_
          (VOA.gradedModule (VOA.voa bridge))
          (cyclotomicScalar (phaseCyclotomic phase))
          (VOA.VOAGroupAction.act (VOA.monsterAction bridge) normalizer state)

open ActualMonster3BVOAPhaseActionSource public

------------------------------------------------------------------------
-- 4. Compile those receipts to the existing CentralNormalizerAction on the
--    exact same VOA carrier.
------------------------------------------------------------------------

centralPhaseActionFromVOA :
  ∀ {G K : Set} {group : GR.Group G} →
  (source : ActualMonster3BVOAPhaseActionSource G K group) →
  Inertia.CentralPhaseAction (VOACarrier (bridge source))
centralPhaseActionFromVOA source =
  record
    { centralAct =
        VOA.VOAGroupAction.act
          (VOA.monsterAction (bridge source)) (centralElement source)
    ; centralInverseAct =
        VOA.VOAGroupAction.act
          (VOA.monsterAction (bridge source)) (centralInverseElement source)
    ; phaseScale = λ phase state →
        VOA.GradedModule._·_
          (VOA.gradedModule (VOA.voa (bridge source)))
          (cyclotomicScalar source (phaseCyclotomic phase)) state
    ; inverseCentralOnEigenstate = inverseCentralOnEigenstate source
    }

normalizerActionFromVOA :
  ∀ {G K : Set} {group : GR.Group G} →
  (source : ActualMonster3BVOAPhaseActionSource G K group) →
  Inertia.CentralNormalizerAction (VOACarrier (bridge source)) G
normalizerActionFromVOA source =
  record
    { phaseAction = centralPhaseActionFromVOA source
    ; act = VOA.VOAGroupAction.act (VOA.monsterAction (bridge source))
    ; preservesOrInverts = preservesOrInverts source
    ; preservingIntertwiner = preservingIntertwiner source
    ; invertingIntertwiner = invertingIntertwiner source
    ; phaseLinearity = phaseLinearity source
    }

literalVOAZetaSector :
  ∀ {G K : Set} {group : GR.Group G} →
  ActualMonster3BVOAPhaseActionSource G K group → Set
literalVOAZetaSector source =
  Inertia.CentralEigenspace
    (Inertia.phaseAction (normalizerActionFromVOA source))
    Inertia.phaseZeta

------------------------------------------------------------------------
-- 5. The remaining recognition is attached to this literal VOA eigenspace.
------------------------------------------------------------------------

record ActualMonster3BVOARecognizedActionSource
    (G K : Set)
    (group : GR.Group G) : Setω where
  field
    phaseSource : ActualMonster3BVOAPhaseActionSource G K group
    recognition :
      Recognition.ActualZetaSectorRecognition
        (literalVOAZetaSector phaseSource)

open ActualMonster3BVOARecognizedActionSource public

singleActionProducerFromVOA :
  ∀ {G K : Set} {group : GR.Group G} →
  ActualMonster3BVOARecognizedActionSource G K group →
  Single.ActualMonster3BSingleActionProducer
singleActionProducerFromVOA {G = G} source =
  record
    { State = VOACarrier (bridge (phaseSource source))
    ; Normalizer = G
    ; normalizerAction = normalizerActionFromVOA (phaseSource source)
    ; recognition = recognition source
    }

------------------------------------------------------------------------
-- 6. Boundary.  The VOA carrier/action is now the preferred recovery surface;
--    this adapter still does not fabricate the actual selected 3B receipts or
--    the Weyl recognition.
------------------------------------------------------------------------

record VOAActionPhaseAdapterBoundary : Set where
  constructor voa-action-phase-adapter-boundary
  field
    literalVOACarrierReused : Bool
    monsterVOAActionReused : Bool
    exactCyclotomicPhaseChartReused : Bool
    zeroTreatedAsFourthEigenphase : Bool
    phaseResolvedBecomesCompilerOutput : Bool
    freshMonsterStateCarrierIntroduced : Bool
    characterVanishingPromotedToEigenvectorEquation : Bool
    actualSelectedThreeBReceiptsInhabitedHere : Bool
    actualZetaRecognitionInhabitedHere : Bool

canonicalVOAActionPhaseAdapterBoundary : VOAActionPhaseAdapterBoundary
canonicalVOAActionPhaseAdapterBoundary =
  voa-action-phase-adapter-boundary
    true true true false true false false false false

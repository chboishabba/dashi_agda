module DASHI.Philosophy.TopologyChangeBoundary where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Reflexivity supplies orientation.  Relation can supply coordination.
-- Actual topology change additionally requires organisation and material
-- action.

data LeverageStage : Set where
  immersedExperience :
    LeverageStage

  reflexiveDoubling :
    LeverageStage

  selfNormalisation :
    LeverageStage

  interChartTranslation :
    LeverageStage

  collectiveAtlas :
    LeverageStage

  materialIntervention :
    LeverageStage

  changedFeedback :
    LeverageStage

canonicalLeverageSequence :
  List LeverageStage
canonicalLeverageSequence =
  immersedExperience
  ∷ reflexiveDoubling
  ∷ selfNormalisation
  ∷ interChartTranslation
  ∷ collectiveAtlas
  ∷ materialIntervention
  ∷ changedFeedback
  ∷ []

record LeveragePrerequisites : Set₁ where
  field
    collectiveOrganisation :
      Set

    materialResources :
      Set

    authorityOrAccess :
      Set

    safety :
      Set

    time :
      Set

    coordination :
      Set

    effectiveOperator :
      Set

open LeveragePrerequisites public

record TopologyChangeTarget
       (X TopologyCode : Set) : Set₁ where
  field
    oldCarrier :
      X

    newCarrier :
      X

    oldTopology :
      TopologyCode

    newTopology :
      TopologyCode

    topologyChanged :
      Set

    leverage :
      LeveragePrerequisites

open TopologyChangeTarget public

data TopologyChangePromotion : Set where

data Never : Set where

topologyChangePromotionImpossibleFromObserverAlone :
  TopologyChangePromotion →
  Never
topologyChangePromotionImpossibleFromObserverAlone ()

record ObserverTopologyBoundary : Set where
  constructor mkObserverTopologyBoundary
  field
    boundaryLabel :
      String

    selfOrientationEstablished :
      Bool

    relationBegun :
      Bool

    organisationEstablished :
      Bool

    materialEffectEstablished :
      Bool

    topologyChangePromoted :
      Bool

open ObserverTopologyBoundary public

canonicalObserverTopologyBoundary :
  ObserverTopologyBoundary
canonicalObserverTopologyBoundary =
  mkObserverTopologyBoundary
    "self-orientation and relation do not by themselves prove topology change"
    true
    true
    false
    false
    false

canonicalTopologyChangeNotPromoted :
  topologyChangePromoted canonicalObserverTopologyBoundary
  ≡
  false
canonicalTopologyChangeNotPromoted =
  refl

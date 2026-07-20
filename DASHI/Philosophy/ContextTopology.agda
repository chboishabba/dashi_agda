module DASHI.Philosophy.ContextTopology where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Clopen context cells and pants composition are kept distinct.
--
-- The context ball carries neighbourhood/inclusion meaning.  The pants
-- carrier records split/merge composition and can retain loops that a tree
-- forgets.  Clopenness is an explicit witness, not inferred from philosophy.

record ContextBall (X Radius : Set) : Set₁ where
  field
    centre :
      X

    radius :
      Radius

    member :
      X →
      Set

    openWitness :
      Set

    closedWitness :
      Set

open ContextBall public

record MultiValuationContextCell
       (X Radius : Set) : Set₁ where
  field
    conceptual :
      ContextBall X Radius

    relationalTrust :
      ContextBall X Radius

    historical :
      ContextBall X Radius

    normative :
      ContextBall X Radius

    institutionalPower :
      ContextBall X Radius

    materialDependency :
      ContextBall X Radius

    intersectionWitness :
      Set

open MultiValuationContextCell public

data PantsDirection : Set where
  split :
    PantsDirection

  merge :
    PantsDirection

record PantsContext
       (X Radius : Set) : Set₁ where
  field
    waist :
      ContextBall X Radius

    leftLeg :
      ContextBall X Radius

    rightLeg :
      ContextBall X Radius

    direction :
      PantsDirection

    boundaryCompatibility :
      Set

    reconvergenceVisible :
      Set

    residualLoopVisible :
      Set

    reducedToTree :
      Bool

open PantsContext public

record ContextTopologyBoundary : Set where
  constructor mkContextTopologyBoundary
  field
    ballsModelNeighbourhood :
      Bool

    pantsModelComposition :
      Bool

    pantsAndBallsAreIdenticalStructures :
      Bool

    recursivePantsCanRetainLoops :
      Bool

    philosophicalMetaphorProvesTopologicalTheorem :
      Bool

open ContextTopologyBoundary public

canonicalContextTopologyBoundary :
  ContextTopologyBoundary
canonicalContextTopologyBoundary =
  mkContextTopologyBoundary
    true
    true
    false
    true
    false

canonicalPantsAndBallsRemainDistinct :
  pantsAndBallsAreIdenticalStructures canonicalContextTopologyBoundary
  ≡
  false
canonicalPantsAndBallsRemainDistinct =
  refl

module DASHI.Philosophy.SituatedState where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Philosophy-native carrier.
--
-- A state is not just a proposition.  It is indexed by observation,
-- relation, commitment, history, action, perspective, constraint, authority,
-- residual, and contextual exterior.

record SituatedState : Set₁ where
  field
    Observation :
      Set

    Relation :
      Set

    Commitment :
      Set

    History :
      Set

    AvailableAction :
      Set

    AccessibleAction :
      Set

    Perspective :
      Set

    Constraint :
      Set

    Authority :
      Set

    Residual :
      Set

    Exterior :
      Set

open SituatedState public

record SituatedContext (S : SituatedState) : Set₁ where
  field
    recognisedRelation :
      Relation S →
      Set

    norm :
      Constraint S →
      Set

    grammar :
      Commitment S →
      Set

    perspectiveWitness :
      Perspective S

    contextLabel :
      String

open SituatedContext public

record ContextIndexedClaim
       (S : SituatedState)
       (C : SituatedContext S) : Set₁ where
  field
    proposition :
      Commitment S

    observationWitness :
      Observation S

    perspective :
      Perspective S

    authorityWitness :
      Authority S

    residualWitness :
      Residual S

    nonClaimExterior :
      Exterior S

open ContextIndexedClaim public

------------------------------------------------------------------------
-- Same commitments need not mean the same situated state.

record SameCommitmentDifferentSituation
       (A B : SituatedState) : Set₁ where
  field
    commitmentA :
      Commitment A

    commitmentB :
      Commitment B

    historiesRemainDistinct :
      Set

    relationsRemainDistinct :
      Set

    perspectivesRemainDistinct :
      Set

open SameCommitmentDifferentSituation public

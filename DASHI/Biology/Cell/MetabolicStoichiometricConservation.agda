module DASHI.Biology.Cell.MetabolicStoichiometricConservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Analysis.StoichiometricConservation as SC
import DASHI.Biology.Cell.OpenMetabolicNetwork as OMN

------------------------------------------------------------------------
-- Open metabolic networks exchange matter and energy with an environment, but
-- declared internal stoichiometric invariants must still be preserved by every
-- internal reaction path.  This adapter fixes an environment, identifies the
-- network step with a generic stoichiometric transition, and inherits exact
-- finite-path conservation from a single left-kernel certificate.
--
-- External fluxes are intentionally outside the theorem.  A later balance-law
-- module can add source and sink terms rather than silently treating an open
-- system as closed.
------------------------------------------------------------------------

record MetabolicStoichiometricBridge
    (N : OMN.OpenMetabolicNetwork)
    : Set₁ where
  field
    Vector : Set
    Quantity : Set

    environment :
      OMN.OpenMetabolicNetwork.Environment N

    stoichiometry :
      SC.StoichiometricSystem
        (OMN.OpenMetabolicNetwork.Reaction N)
        Vector
        Quantity
        (OMN.OpenMetabolicNetwork.NetworkState N)

    stepMatchesNetwork :
      (reaction : OMN.OpenMetabolicNetwork.Reaction N) →
      (state : OMN.OpenMetabolicNetwork.NetworkState N) →
      SC.step stoichiometry reaction state
        ≡ OMN.OpenMetabolicNetwork.step N environment reaction state

    leftKernel :
      SC.LeftKernelConservation stoichiometry

open MetabolicStoichiometricBridge public

metabolicReactionConserves :
  ∀ {N} →
  (B : MetabolicStoichiometricBridge N) →
  (reaction : OMN.OpenMetabolicNetwork.Reaction N) →
  (state : OMN.OpenMetabolicNetwork.NetworkState N) →
  SC.quantity (stoichiometry B)
    (OMN.OpenMetabolicNetwork.step N (environment B) reaction state)
    ≡ SC.quantity (stoichiometry B) state
metabolicReactionConserves B reaction state =
  trans
    (cong
      (SC.quantity (stoichiometry B))
      (sym (stepMatchesNetwork B reaction state)))
    (SC.reactionStepConserves
      (stoichiometry B)
      (leftKernel B)
      reaction
      state)

runMetabolicReactionPath :
  ∀ {N} →
  (B : MetabolicStoichiometricBridge N) →
  List (OMN.OpenMetabolicNetwork.Reaction N) →
  OMN.OpenMetabolicNetwork.NetworkState N →
  OMN.OpenMetabolicNetwork.NetworkState N
runMetabolicReactionPath B [] state = state
runMetabolicReactionPath {N} B (reaction ∷ reactions) state =
  runMetabolicReactionPath B reactions
    (OMN.OpenMetabolicNetwork.step N (environment B) reaction state)

metabolicReactionPathConserves :
  ∀ {N} →
  (B : MetabolicStoichiometricBridge N) →
  (reactions : List (OMN.OpenMetabolicNetwork.Reaction N)) →
  (state : OMN.OpenMetabolicNetwork.NetworkState N) →
  SC.quantity (stoichiometry B)
    (runMetabolicReactionPath B reactions state)
    ≡ SC.quantity (stoichiometry B) state
metabolicReactionPathConserves B [] state = refl
metabolicReactionPathConserves {N} B (reaction ∷ reactions) state =
  trans
    (metabolicReactionPathConserves B reactions
      (OMN.OpenMetabolicNetwork.step N (environment B) reaction state))
    (metabolicReactionConserves B reaction state)

record MetabolicStoichiometricCertificate
    {N : OMN.OpenMetabolicNetwork}
    (B : MetabolicStoichiometricBridge N)
    : Set₁ where
  field
    genericCertificate :
      SC.StoichiometricConservationCertificate (stoichiometry B)

    internalReactionConservation :
      (reaction : OMN.OpenMetabolicNetwork.Reaction N) →
      (state : OMN.OpenMetabolicNetwork.NetworkState N) →
      SC.quantity (stoichiometry B)
        (OMN.OpenMetabolicNetwork.step N (environment B) reaction state)
        ≡ SC.quantity (stoichiometry B) state

    internalPathConservation :
      (reactions : List (OMN.OpenMetabolicNetwork.Reaction N)) →
      (state : OMN.OpenMetabolicNetwork.NetworkState N) →
      SC.quantity (stoichiometry B)
        (runMetabolicReactionPath B reactions state)
        ≡ SC.quantity (stoichiometry B) state

open MetabolicStoichiometricCertificate public

certifyMetabolicStoichiometry :
  ∀ {N} →
  (B : MetabolicStoichiometricBridge N) →
  MetabolicStoichiometricCertificate B
certifyMetabolicStoichiometry B = record
  { genericCertificate =
      SC.certifyStoichiometricConservation
        (stoichiometry B)
        (leftKernel B)
  ; internalReactionConservation = metabolicReactionConserves B
  ; internalPathConservation = metabolicReactionPathConserves B
  }

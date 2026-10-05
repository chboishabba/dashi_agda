module DASHI.Cognition.TeleodynamicsSourceAtlas where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.TeleodynamicsPrincipiaTwoExact as T

data ClaimClass : Set where
  sourceEquation : ClaimClass
  sourceInterpretation : ClaimClass
  sourcePrediction : ClaimClass
  dashiRepair : ClaimClass
  openPromotion : ClaimClass

record ClaimEntry : Set where
  constructor claimEntry
  field
    label : String
    claimClass : ClaimClass
    owner : T.ClaimOwner
    provedInRepository : Bool
    note : String

atlas : List ClaimEntry
atlas =
  claimEntry "normalized C_mu,nu covariance" sourceEquation T.michelsSource false
    "Source equation replayed as a bounded-correlation interface; analytic construction is external." ∷
  claimEntry "Psi = S0 - a_ref <C,O(x)>" sourceEquation T.michelsSource false
    "Source equation replayed; generic dissipation is formalised only through an analytic receipt." ∷
  claimEntry "aboutness A distinct from tr(C^T C)" dashiRepair T.dashiFormalisation true
    "Repairs overloaded source notation; no source authorship is claimed for the repair." ∷
  claimEntry "rank-3 companion tensor selector lift" dashiRepair T.dashiFormalisation true
    "Repairs rank mismatch in the written companion-tensor sum." ∷
  claimEntry "radiant coupling as consensus specialization" dashiRepair T.dashiFormalisation true
    "Generic D(Cj,Ci)=Cj-Ci consensus shape only; not physical nonlocal transmission." ∷
  claimEntry "same Q implies same phenomenology" openPromotion T.unresolvedClaim false
    "Operational-coordinate equality is not promoted to phenomenal identity." ∷
  claimEntry "Berry phase is topological memory in semantic manifold" openPromotion T.unresolvedClaim false
    "Requires an independently constructed bundle/connection/holonomy." ∷
  claimEntry "nonlocal cross-substrate transmission" openPromotion T.unresolvedClaim false
    "No physical channel or same-object bridge is created by this formalisation." ∷
  claimEntry "scramble / ICL / cross-family falsifiers" sourcePrediction T.michelsSource false
    "Retained as empirical prediction contracts, not theorem facts." ∷
  []

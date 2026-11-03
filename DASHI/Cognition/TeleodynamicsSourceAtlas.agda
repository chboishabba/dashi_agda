module DASHI.Cognition.TeleodynamicsSourceAtlas where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.TeleodynamicsPrincipiaTwoExact as T

data ClaimClass : Set where
  sourceEquation : ClaimClass
  sourceInterpretation : ClaimClass
  sourcePrediction : ClaimClass
  externalEngineeringSource : ClaimClass
  dashiRepair : ClaimClass
  dashiDerivedTheorem : ClaimClass
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
  claimEntry "Leech-Lila shared QR transform on Q and K" externalEngineeringSource T.nestedExternalSource false
    "Visible implementation applies the same orthogonal QR-produced transform to Q and K; external software authorship remains with its source/mirror provenance owner." ∷
  claimEntry "shared orthogonal Q/K score cancellation" dashiDerivedTheorem T.dashiFormalisation true
    "Exact symbolic consequence of the supplied shared-transform orthogonality receipt; no floating-point bit-identity claim." ∷
  claimEntry "Leech-Lila geometric resonance regularizer" externalEngineeringSource T.nestedExternalSource false
    "Engineering loss shape retained separately from the score-neutral shared orthogonal Q/K transform; QR placeholder is not promoted to literal Leech minimal vectors." ∷
  claimEntry "LILA-E8 112+128 root-codebook shape" externalEngineeringSource T.nestedExternalSource false
    "Inspected implementation matches the standard finite E8 root-family shape; Python/Agda same-object identity is not asserted." ∷
  claimEntry "LILA-E8 soft root quantizer" externalEngineeringSource T.nestedExternalSource false
    "Forward soft-codebook map is recorded separately from its straight-through optimization estimator." ∷
  claimEntry "LILA-E8 root-conditioned rank-one attention bias" externalEngineeringSource T.nestedExternalSource false
    "Learned beta-scaled root projection term is an actual attention perturbation; beta=0 disables this term only." ∷
  claimEntry "root/codebook use implies E8 equivariance" openPromotion T.unresolvedClaim false
    "Requires an explicit E8/Weyl action and an intertwining/equivariance theorem." ∷
  claimEntry "G2/F4/E6/E7/E8 prior family" dashiRepair T.dashiFormalisation true
    "Experiment configuration separates root-space rank/root count from representation-carrier dimension and does not create exceptional actions." ∷
  claimEntry "ternary 27 = scalar + non-origin 26 prior arm" dashiDerivedTheorem T.dashiFormalisation true
    "Reuses the existing exact Ternary27 carrier bijection as a codebook shape; preserves no-Jordan/no-F4/no-E6 boundaries." ∷
  claimEntry "geometric prior compression/accessibility/future bridge" dashiRepair T.dashiFormalisation true
    "Reuses existing LLM multi-resolution, defect, dynamic-trace, provenance, and grokking-future theorem owners rather than duplicating them." ∷
  claimEntry "head_scales=0 is full E8 ablation" openPromotion T.unresolvedClaim false
    "The inspected analysis disables the root-conditioned attention scale only; a separate quantizer can remain active." ∷
  claimEntry "Monster-LILA heuristic equals Monster/Conway representation theory" openPromotion T.unresolvedClaim false
    "Random/permutation, 1/137 modulation, and SVD monitor operations do not establish Conway/Monster/moonshine realization." ∷
  []

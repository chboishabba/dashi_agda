module DASHI.Physics.Gravity.PenroseGlobalCausalityAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Source-bound authority layer for the global causal/topological steps in
-- the Penrose proof architecture. This records exact literature coordinates
-- and payment relationships; it does not import or recreate the proofs.
------------------------------------------------------------------------

Minguzzi2019LorentzianCausalitySourceReceipt : Source.AttributedSource
Minguzzi2019LorentzianCausalitySourceReceipt =
  Source.mkDOISource
    "E. Minguzzi"
    "Lorentzian causality theory"
    "Living Reviews in Relativity 22, 3"
    "2019"
    "10.1007/s41114-019-0019-x"
    "https://doi.org/10.1007/s41114-019-0019-x"
    Source.academicArticleSource
    "modern causal-theory source for exact theorem coordinates used by the Penrose global-causality boundary; citation records provenance and does not import proof"
    Source.publicAttribution

record GlobalCausalityAuthorityReceipt : Set where
  field
    theoremSixTwentyThreeNonCompactCauchyObstruction : String
    theoremSixTwentyThreeTimelikeFlowProjection : String
    globallyHyperbolicImpliesCausallySimpleForHorismosBoundary : String
    horismosAsBoundaryOfChronologicalFuture : String
    theoremSixTwentyFivePenroseComposition : String

    authorityCitationImportsNeitherProofNorAuthority : Bool
    authorityCitationImportsNeitherProofNorAuthorityIsTrue :
      authorityCitationImportsNeitherProofNorAuthority ≡ true

    authorityOwnerInternallyReprovesGlobalCausality : Bool
    authorityOwnerInternallyReprovesGlobalCausalityIsFalse :
      authorityOwnerInternallyReprovesGlobalCausality ≡ false

open GlobalCausalityAuthorityReceipt public

canonicalGlobalCausalityAuthorityReceipt : GlobalCausalityAuthorityReceipt
canonicalGlobalCausalityAuthorityReceipt = record
  { theoremSixTwentyThreeNonCompactCauchyObstruction =
      "Minguzzi 2019 Theorem 6.23: in a globally hyperbolic spacetime with a non-compact Cauchy hypersurface there is no non-empty compact future trapped set; equivalently the Penrose compact-horismos side cannot coexist with that global topology"
  ; theoremSixTwentyThreeTimelikeFlowProjection =
      "Minguzzi 2019 proof of Theorem 6.23: project E+(A) along a global timelike vector-field flow to a Cauchy hypersurface; compactness of the projection conflicts with the absence of boundary implied by local crossing while the Cauchy hypersurface is non-compact"
  ; globallyHyperbolicImpliesCausallySimpleForHorismosBoundary =
      "Minguzzi 2019 Theorem 6.23 proof uses that global hyperbolicity implies causal simplicity, enabling E+(A) to be identified with the boundary of I+(A) through the cited causal-boundary results"
  ; horismosAsBoundaryOfChronologicalFuture =
      "under the declared causal-simplicity hypotheses, E+(A) is the achronal boundary / boundary of I+(A) used by the timelike-flow projection argument"
  ; theoremSixTwentyFivePenroseComposition =
      "Minguzzi 2019 Theorem 6.25: global hyperbolicity + non-compact Cauchy hypersurface + null convergence + trapped surface imply future null geodesic incompleteness by composing the trapped-set result with the noncompact-Cauchy obstruction"
  ; authorityCitationImportsNeitherProofNorAuthority = true
  ; authorityCitationImportsNeitherProofNorAuthorityIsTrue = refl
  ; authorityOwnerInternallyReprovesGlobalCausality = false
  ; authorityOwnerInternallyReprovesGlobalCausalityIsFalse = refl
  }

record GlobalCausalityAuthorityInterpretationBoundary : Set where
  field
    theoremCoordinateIsNotKernelProof : Bool
    theoremCoordinateIsNotKernelProofIsTrue :
      theoremCoordinateIsNotKernelProof ≡ true

    modernReviewDoesNotReplacePrimaryPenroseAttribution : Bool
    modernReviewDoesNotReplacePrimaryPenroseAttributionIsTrue :
      modernReviewDoesNotReplacePrimaryPenroseAttribution ≡ true

    cauchyProjectionArgumentIsGlobalNotLocalFocusing : Bool
    cauchyProjectionArgumentIsGlobalNotLocalFocusingIsTrue :
      cauchyProjectionArgumentIsGlobalNotLocalFocusing ≡ true

open GlobalCausalityAuthorityInterpretationBoundary public

canonicalGlobalCausalityAuthorityInterpretationBoundary :
  GlobalCausalityAuthorityInterpretationBoundary
canonicalGlobalCausalityAuthorityInterpretationBoundary = record
  { theoremCoordinateIsNotKernelProof = true
  ; theoremCoordinateIsNotKernelProofIsTrue = refl
  ; modernReviewDoesNotReplacePrimaryPenroseAttribution = true
  ; modernReviewDoesNotReplacePrimaryPenroseAttributionIsTrue = refl
  ; cauchyProjectionArgumentIsGlobalNotLocalFocusing = true
  ; cauchyProjectionArgumentIsGlobalNotLocalFocusingIsTrue = refl
  }

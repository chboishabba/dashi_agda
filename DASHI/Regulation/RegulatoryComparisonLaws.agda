module DASHI.Regulation.RegulatoryComparisonLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Regulation.RegulatoryProjectionCore

agreementImpliesLeftResidualEmpty :
  (L R : RegulatoryProjection) →
  (C : CrossJurisdictionComparison L R) →
  (D : RegulatoryResidual L R C) →
  (l : ObservableSurface L) →
  (r : ObservableSurface R) →
  compareSurface C l r ≡ agrees →
  leftResidual D l r ≡ []
agreementImpliesLeftResidualEmpty L R C D = agreementLeftEmpty D

agreementImpliesRightResidualEmpty :
  (L R : RegulatoryProjection) →
  (C : CrossJurisdictionComparison L R) →
  (D : RegulatoryResidual L R C) →
  (l : ObservableSurface L) →
  (r : ObservableSurface R) →
  compareSurface C l r ≡ agrees →
  rightResidual D l r ≡ []
agreementImpliesRightResidualEmpty L R C D = agreementRightEmpty D

promotionCarriesEvidence :
  (P : RegulatoryProjection) →
  (E : ComplianceEvidence P) →
  (candidate : Candidate E) →
  Promoted E candidate →
  Σ (Receipt E) λ receipt →
  Σ (Verifier E) λ verifier →
    Σ (receiptSupports E receipt candidate) λ _ →
      verifierAccepts E verifier receipt
promotionCarriesEvidence P E candidate
  (promoted-by receipt verifier support accepted) =
  receipt , (verifier , (support , accepted))

conflictCannotBeMerelyCompatible :
  (G : RegulatoryConflictGraph) →
  (x y : Node G) →
  RegulatoryConflictGraph.Conflict G x y →
  relation G x y ≡ blocks
conflictCannotBeMerelyCompatible G x y (conflict proof) = proof

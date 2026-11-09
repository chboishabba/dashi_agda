module DASHI.Governance.CrenshawLegalRepresentationRemedyExact where

-- Primary conceptual context: Kimberle W Crenshaw (1989), Demarginalizing.
-- Judicial source owners: Moore, 708 F.2d 475 (9th Cir 1983);
-- Payne, 673 F.2d 798 (5th Cir 1982).
-- The source-indexed finite comparison is a DASHI reconstruction, not a
-- judicial theorem, empirical truth certificate, or Crenshaw-authored proof.
open import DASHI.Core.Prelude
import DASHI.Law.LegalAuthorityCitationExact as Legal
import DASHI.Core.IntersectionalNonFactorability as INF

mooreAppeal : Legal.LegalCitation
mooreAppeal = Legal.legal-citation
  Legal.judgment Legal.primaryTextEvidence
  "US federal appellate court, Ninth Circuit"
  "United States Court of Appeals for the Ninth Circuit"
  "Moore v Hughes Helicopters"
  1983
  (Legal.bibliographicLegalFallback "708 F.2d 475")
  "477-480, class scope, representation and statistical proof"
  "Affirmed the restricted class and dismissal; differentiated representative adequacy from group membership"
  false refl

payneAppeal : Legal.LegalCitation
payneAppeal = Legal.legal-citation
  Legal.judgment Legal.primaryTextEvidence
  "US federal appellate court, Fifth Circuit"
  "United States Court of Appeals for the Fifth Circuit"
  "Payne v Travenol Laboratories"
  1982
  (Legal.bibliographicLegalFallback "673 F.2d 798")
  "802-811, class scope and terms of injunctive decree"
  "Affirmed exclusion of Black male class members on an actual-conflict reasoning while separately reviewing relief and discrimination findings"
  false refl

data ClassQuestion : Set where
  plaintiffGroupMember qualifiedRepresentative liabilityFound remedySpecified : ClassQuestion

-- Finite independence witness: recognition/membership alone does not recover
-- representative adequacy. The statuses are synthetic and not the plaintiffs.
data ExampleRepresentation : Set where
  sameGroupWithConflict sameGroupWithoutConflict : ExampleRepresentation

groupMember : ExampleRepresentation → Bool
groupMember sameGroupWithConflict = true
groupMember sameGroupWithoutConflict = true

adequateRepresentation : ExampleRepresentation → Bool
adequateRepresentation sameGroupWithConflict = false
adequateRepresentation sameGroupWithoutConflict = true

mooreClassRepresentationNotClaimIdentity :
  INF.NonFactorabilityWitness groupMember adequateRepresentation
mooreClassRepresentationNotClaimIdentity =
  INF.nonFactorabilityWitness
    sameGroupWithConflict sameGroupWithoutConflict refl (λ ())

classMembershipCannotDecideRepresentativeAdequacy :
  INF.FactorsThrough groupMember adequateRepresentation → ⊥
classMembershipCannotDecideRepresentativeAdequacy =
  INF.witnessRulesOutEveryFlatFactorisation
    mooreClassRepresentationNotClaimIdentity

data RemedyModel : Set where
  limitedScopeWithRelief limitedScopeWithoutRelief : RemedyModel

classScope : RemedyModel → Bool
classScope limitedScopeWithRelief = false
classScope limitedScopeWithoutRelief = false

relief : RemedyModel → Bool
relief limitedScopeWithRelief = true
relief limitedScopeWithoutRelief = false

payneReliefNotEquivalentToRepresentationScope :
  INF.NonFactorabilityWitness classScope relief
payneReliefNotEquivalentToRepresentationScope =
  INF.nonFactorabilityWitness
    limitedScopeWithRelief limitedScopeWithoutRelief refl (λ ())

classScopeCannotDetermineRemedy :
  INF.FactorsThrough classScope relief → ⊥
classScopeCannotDetermineRemedy =
  INF.witnessRulesOutEveryFlatFactorisation
    payneReliefNotEquivalentToRepresentationScope

-- Source-specific observations, not an all-purpose claim about Rule 23.
data AppellateCase : Set where
  moore payne : AppellateCase

data BoundedAppellateReading : AppellateCase → Set where
  mooreRestriction :
    BoundedAppellateReading moore
  payneConflictBasedScope :
    BoundedAppellateReading payne

data CaseDisposition : Set where
  affirmedDismissal reviewedInterlocutoryRemedy : CaseDisposition

reportedDisposition : AppellateCase → CaseDisposition
reportedDisposition moore = affirmedDismissal
reportedDisposition payne = reviewedInterlocutoryRemedy

mooreAndPayneHaveDistinctAppellateDispositions :
  reportedDisposition moore ≡ reportedDisposition payne → ⊥
mooreAndPayneHaveDistinctAppellateDispositions ()

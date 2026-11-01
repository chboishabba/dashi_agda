module DASHI.Foundations.ClaimScopeCertificateExact where

------------------------------------------------------------------------
-- DASHI META-FORMALIZATION
--
-- A large family of repository `*Boundary` records stores Boolean flags with
-- proofs such as `flag ≡ false`.  Those proofs certify the value of the flag;
-- they are NOT, by themselves, mathematical proofs of the negation of the
-- proposition suggested by the field name.
--
-- This module gives that convention an explicit type.  `notEstablishedHere`
-- means exactly "this layer does not establish/claim the proposition".  A real
-- impossibility theorem must instead inhabit `Refutation P = P -> bottom`.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

data ClaimStatus : Set where
  establishedHere : ClaimStatus
  notEstablishedHere : ClaimStatus

record ClaimScopeCertificate (Claim : Set) : Set₁ where
  constructor claimScopeCertificate
  field
    status : ClaimStatus
    proofWhenEstablished :
      status ≡ establishedHere → Claim

open ClaimScopeCertificate public

record NonClaimCertificate (Claim : Set) : Set where
  constructor nonClaimCertificate
  field
    statusIsNotEstablished : ClaimStatus
    statusIsNotEstablishedExact :
      statusIsNotEstablished ≡ notEstablishedHere

-- A logically negative theorem has a different type and requires an actual
-- function from the proposition to bottom.
Refutation : Set → Set
Refutation Claim = Claim → ⊥

-- A non-claim certificate contains no eliminator `Claim -> bottom`.
-- This distinction is structural: the types are different, rather than being
-- left to prose around a Boolean flag.

record BoundarySemanticsClaimScope : Set where
  constructor boundarySemanticsClaimScope
  field
    nonClaimAndRefutationAreDifferentTypes : Bool
    nonClaimAndRefutationAreDifferentTypesIsTrue :
      nonClaimAndRefutationAreDifferentTypes ≡ true

    legacyFalseFlagShouldBeReadAsImpossibilityProof : Bool
    legacyFalseFlagShouldBeReadAsImpossibilityProofIsFalse :
      legacyFalseFlagShouldBeReadAsImpossibilityProof ≡ false

canonicalBoundarySemanticsClaimScope : BoundarySemanticsClaimScope
canonicalBoundarySemanticsClaimScope =
  boundarySemanticsClaimScope true refl false refl

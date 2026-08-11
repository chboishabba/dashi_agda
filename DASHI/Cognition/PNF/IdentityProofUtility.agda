module DASHI.Cognition.PNF.IdentityProofUtility where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity
import DASHI.Cognition.PNF.ProofRelevantFactorDerivations as Derivation

------------------------------------------------------------------------
-- Proof existence != operational factor applicability.
--
-- Real-corpus acceptance showed many admitted identity projections but very few
-- factor-bearing projections.  Identity admission must remain epistemically
-- independent of whether a local object currently participates in a factor.
------------------------------------------------------------------------

record FactorParticipation
    (object : ObjectId)
    (factor : FactorId) : Set where
  constructor factorParticipation
  field
    participationRole : Nat

open FactorParticipation public

record FactorApplicableIdentity : Set where
  constructor factorApplicableIdentity
  field
    identityMember : Identity.IdentityFibreMember
    premiseFactor : FactorId
    factorParticipationWitness :
      FactorParticipation
        (Identity.fibreLocalObject identityMember)
        premiseFactor

open FactorApplicableIdentity public

data IdentityAutomaticallyFactorApplicable : Set where

identityProofDoesNotImplyFactorApplicability :
  IdentityAutomaticallyFactorApplicable → ⊥
identityProofDoesNotImplyFactorApplicability ()

------------------------------------------------------------------------
-- Once factor participation is independently witnessed, the existing Level-3
-- substitution proof can be constructed without changing the identity proof.
------------------------------------------------------------------------

factorApplicableSubstitutionProof :
  FactorApplicableIdentity → Derivation.IdentitySubstitutionProof
factorApplicableSubstitutionProof applicable =
  Derivation.identitySubstitutionProof
    (premiseFactor applicable)
    (Identity.fibreLocalObject (identityMember applicable))
    (Identity.fibreEntity (identityMember applicable))
    (Identity.fibreWitness (identityMember applicable))
    (Identity.fibreSourceMatchesWitness (identityMember applicable))
    (Identity.fibreEntityMatchesWitness (identityMember applicable))

------------------------------------------------------------------------
-- Corpus/runtime coverage receipt.  These are counts, not semantic authority.
-- They make the identity -> factor -> L3 funnel explicit without demanding that
-- every valid identity proof be useful to the current factor graph.
------------------------------------------------------------------------

record IdentityUtilityCoverage : Set where
  constructor identityUtilityCoverage
  field
    admittedIdentityProjectionCount : Nat
    factorBearingIdentityProjectionCount : Nat
    levelThreeSubstitutionCount : Nat
    factorBearingWithinIdentity :
      factorBearingIdentityProjectionCount ≤ᶜ admittedIdentityProjectionCount
    levelThreeWithinFactorBearing :
      levelThreeSubstitutionCount ≤ᶜ factorBearingIdentityProjectionCount

open IdentityUtilityCoverage public

record IdentityUtilityBoundary : Set where
  constructor identityUtilityBoundary
  field
    identityAdmissionRequiresFactorUsefulness : Bool
    identityAdmissionRequiresFactorUsefulnessIsFalse :
      identityAdmissionRequiresFactorUsefulness ≡ false
    factorUsefulnessRequiresIndependentParticipationWitness : Bool
    factorUsefulnessRequiresIndependentParticipationWitnessIsTrue :
      factorUsefulnessRequiresIndependentParticipationWitness ≡ true
    proofExistenceAutomaticallyCreatesLevelThreeDerivation : Bool
    proofExistenceAutomaticallyCreatesLevelThreeDerivationIsFalse :
      proofExistenceAutomaticallyCreatesLevelThreeDerivation ≡ false

open IdentityUtilityBoundary public

canonicalIdentityUtilityBoundary : IdentityUtilityBoundary
canonicalIdentityUtilityBoundary =
  identityUtilityBoundary
    false refl
    true refl
    false refl

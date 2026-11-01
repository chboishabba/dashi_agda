module DASHI.Ontology.ProgenitorParentEthicsExamples where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Ontology.ProgenitorParentHyperfabric

------------------------------------------------------------------------
-- Concrete ontology-ethics countermodels.
--
-- These do not decree one legal or cultural definition of parenthood. They
-- prove the weaker and more important design result: genetic provenance cannot
-- determine parenthood when the coordinates vary independently in admissible
-- cases. A graph that wants genetics should model genetics explicitly rather
-- than silently overloading "parent".
------------------------------------------------------------------------

countTrue2 : Bool → Bool → Nat
countTrue2 false false = zero
countTrue2 false true = suc zero
countTrue2 true false = suc zero
countTrue2 true true = suc (suc zero)

record TwoPartyFamilyCase : Set where
  constructor twoPartyFamilyCase
  field
    primary : RelationVector
    secondary : RelationVector
open TwoPartyFamilyCase public

singleMotherAnonymousDonorCase : TwoPartyFamilyCase
singleMotherAnonymousDonorCase =
  twoPartyFamilyCase singleMother anonymousIVFDonor

familyParentCount : TwoPartyFamilyCase → Nat
familyParentCount family =
  countTrue2
    (genealogicalParent (primary family))
    (genealogicalParent (secondary family))

familyGeneticContributorCount : TwoPartyFamilyCase → Nat
familyGeneticContributorCount family =
  countTrue2
    (geneticContributor (primary family))
    (geneticContributor (secondary family))

oneParentTwoGeneticContributors :
  familyParentCount singleMotherAnonymousDonorCase ≡ suc zero
  × familyGeneticContributorCount singleMotherAnonymousDonorCase ≡ suc (suc zero)
oneParentTwoGeneticContributors = refl , refl

donorIsNotSilentlyPromotedToParent :
  geneticContributor (secondary singleMotherAnonymousDonorCase) ≡ true
  × genealogicalParent (secondary singleMotherAnonymousDonorCase) ≡ false
donorIsNotSilentlyPromotedToParent = refl , refl

motherParenthoodDoesNotDependOnDonorDisclosure :
  genealogicalParent (primary singleMotherAnonymousDonorCase) ≡ true
  × identityKnown (secondary singleMotherAnonymousDonorCase) ≡ false
  × identityDisclosable (secondary singleMotherAnonymousDonorCase) ≡ false
motherParenthoodDoesNotDependOnDonorDisclosure = refl , (refl , refl)

-- The two directions of collapse are independently falsified by ordinary
-- countermodels: donor conception and adoption.
parentGeneticsBiconditionalFailsBothDirections :
  ( geneticContributor anonymousIVFDonor ≡ true
    × genealogicalParent anonymousIVFDonor ≡ false )
  × ( genealogicalParent adoptiveParent ≡ true
      × geneticContributor adoptiveParent ≡ false )
parentGeneticsBiconditionalFailsBothDirections =
  geneticContributionCannotDetermineParenthood
  , parenthoodCannotDetermineGeneticContribution

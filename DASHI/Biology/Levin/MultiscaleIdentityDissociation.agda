module DASHI.Biology.Levin.MultiscaleIdentityDissociation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; _⊔_; lsuc)

------------------------------------------------------------------------
-- Scale-relative integration and dissociation.
--
-- This is the formal core of the Levin-style cancer interpretation: a cell
-- can remain locally viable while ceasing to participate in a tissue-level
-- objective.  The module does not assert that this is the sole or universal
-- mechanism of cancer, nor that electrical reconnection is a human therapy.

record MultiscaleIntegrationSystem
  {ℓc ℓt ℓa ℓk : Level} : Set (lsuc (ℓc ⊔ ℓt ⊔ ℓa ⊔ ℓk)) where
  field
    CellState   : Set ℓc
    TissueState : Set ℓt
    CellAction  : Set ℓa
    Coupling    : Set ℓk

    locallyViable    : CellState → CellAction → Bool
    tissueCompatible : TissueState → CellAction → Bool
    connected        : Coupling → CellState → TissueState → Bool
    act              : CellAction → TissueState → TissueState
    reconnect        : Coupling → Coupling

open MultiscaleIntegrationSystem public

record IdentityDissociationWitness
  {ℓc ℓt ℓa ℓk : Level}
  (S : MultiscaleIntegrationSystem {ℓc} {ℓt} {ℓa} {ℓk}) :
  Set (ℓc ⊔ ℓt ⊔ ℓa ⊔ ℓk) where
  field
    cell     : CellState S
    tissue   : TissueState S
    action   : CellAction S
    coupling : Coupling S

    cellRemainsLocallyViable : locallyViable S cell action ≡ true
    actionViolatesTissueGoal : tissueCompatible S tissue action ≡ false
    cellIsDisconnected : connected S coupling cell tissue ≡ false

open IdentityDissociationWitness public

record ReconnectionNormalisationWitness
  {ℓc ℓt ℓa ℓk : Level}
  (S : MultiscaleIntegrationSystem {ℓc} {ℓt} {ℓa} {ℓk}) :
  Set (ℓc ⊔ ℓt ⊔ ℓa ⊔ ℓk) where
  field
    cell     : CellState S
    tissue   : TissueState S
    action   : CellAction S
    coupling : Coupling S

    initiallyDisconnected : connected S coupling cell tissue ≡ false
    reconnected : connected S (reconnect S coupling) cell tissue ≡ true
    actionBecomesTissueCompatible :
      tissueCompatible S tissue action ≡ true

open ReconnectionNormalisationWitness public

data CancerInterpretationStatus : Set where
  abstractModelOnly       : CancerInterpretationStatus
  animalModelCandidate    : CancerInterpretationStatus
  mechanismUnderTest      : CancerInterpretationStatus
  clinicallyValidated     : CancerInterpretationStatus

canonicalIdentityDissociationNotes : List String
canonicalIdentityDissociationNotes =
  "Local viability and tissue-level compatibility are separate typed predicates"
  ∷ "Dissociation is scale-relative loss of integration, not a psychiatric diagnosis applied literally to cells"
  ∷ "A reconnection witness is model-specific and does not establish universal cancer normalisation"
  ∷ "Genomic, immune, metabolic, ecological, mechanical, and bioelectric mechanisms may coexist"
  ∷ "No human diagnostic or therapeutic authority is promoted"
  ∷ []

record IdentityDissociationBoundary : Set where
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    cancerIsNotReducedToOneMechanism : Bool
    cancerIsNotReducedToOneMechanismIsFalse :
      cancerIsNotReducedToOneMechanism ≡ false

    animalModelIsNotHumanTherapy : Bool
    animalModelIsNotHumanTherapyIsFalse :
      animalModelIsNotHumanTherapy ≡ false

    noClinicalAuthority : Bool
    noClinicalAuthorityIsFalse : noClinicalAuthority ≡ false

open IdentityDissociationBoundary public

canonicalIdentityDissociationBoundary : IdentityDissociationBoundary
canonicalIdentityDissociationBoundary = record
  { candidateOnly = true
  ; candidateOnlyIsTrue = refl
  ; cancerIsNotReducedToOneMechanism = false
  ; cancerIsNotReducedToOneMechanismIsFalse = refl
  ; animalModelIsNotHumanTherapy = false
  ; animalModelIsNotHumanTherapyIsFalse = refl
  ; noClinicalAuthority = false
  ; noClinicalAuthorityIsFalse = refl
  }

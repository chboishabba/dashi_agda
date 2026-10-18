module DASHI.Biology.AvianMagnetoreceptionSourceRegistry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

data EvidenceRole : Set where
  directCellMaterialObservation : EvidenceRole
  causalBehaviorIntervention : EvidenceRole
  controlConditionReceipt : EvidenceRole
  anatomicalProximityObservation : EvidenceRole
  proposedMechanismOnly : EvidenceRole
  unresolvedMechanism : EvidenceRole

record AvianMagnetoreceptionSource : Set where
  constructor avian-magnetoreception-source
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    roles : List EvidenceRole
    directNeuralTransductionEstablished : Bool
    brainRepresentationEstablished : Bool
    sourceBoundary : String

open AvianMagnetoreceptionSource public

lisowskiEtAl2026 : AvianMagnetoreceptionSource
lisowskiEtAl2026 =
  avian-magnetoreception-source
    "Clivia Lisowski et al."
    "Homing pigeon navigation relies on superparamagnetic macrophages under overcast conditions"
    "Science 392(6801):985-991"
    2026
    "DOI 10.1126/science.ady2486; PMID 42207892"
    ( directCellMaterialObservation
    ∷ causalBehaviorIntervention
    ∷ controlConditionReceipt
    ∷ anatomicalProximityObservation
    ∷ proposedMechanismOnly
    ∷ unresolvedMechanism
    ∷ []
    )
    false
    false
    "Promotes the reported macrophage/material observations, depletion-context behavioral effect, and visible-Sun control at source scope; does not promote a completed autonomic/vagal transduction pathway or central representation."

lisowskiDirectNeuralTransductionNotPromoted :
  directNeuralTransductionEstablished lisowskiEtAl2026 ≡ false
lisowskiDirectNeuralTransductionNotPromoted = refl

lisowskiBrainRepresentationNotPromoted :
  brainRepresentationEstablished lisowskiEtAl2026 ≡ false
lisowskiBrainRepresentationNotPromoted = refl

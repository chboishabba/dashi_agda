module DASHI.Regulation.RegulatoryFiniteExample where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Regulation.RegulatoryProjectionCore
open import DASHI.Regulation.RegulatoryAuthorityBundle

data Authority : Set where
  au eu : Authority

data Activity : Set where
  process transfer : Activity

data Surface : Set where
  recorded unrecorded : Surface

data Duty : Set where
  disclose obtainConsent retainRecord prohibitTransfer : Duty

constantSurface : Activity → Surface
constantSurface _ = recorded

auJurisdiction : Jurisdiction
auJurisdiction = record
  { jurisdictionName = "AU-example"
  ; authorityName = "AU-example authority"
  }

euJurisdiction : Jurisdiction
euJurisdiction = record
  { jurisdictionName = "EU-example"
  ; authorityName = "EU-example authority"
  }

auProjection : RegulatoryProjection
auProjection = record
  { HiddenActivity = Activity
  ; ObservableSurface = Surface
  ; Obligation = Duty
  ; jurisdiction = auJurisdiction
  ; project = constantSurface
  ; obligations = λ { recorded → disclose ∷ retainRecord ∷ []
                    ; unrecorded → [] }
  ; projectionReading = "Finite AU-shaped structural example; not a statement of Australian law."
  }

euProjection : RegulatoryProjection
euProjection = record
  { HiddenActivity = Activity
  ; ObservableSurface = Surface
  ; Obligation = Duty
  ; jurisdiction = euJurisdiction
  ; project = constantSurface
  ; obligations = λ { recorded → obtainConsent ∷ prohibitTransfer ∷ []
                    ; unrecorded → [] }
  ; projectionReading = "Finite EU-shaped structural example; not a statement of EU law."
  }

noSectionConstant :
  (P : RegulatoryProjection) →
  project P process ≡ recorded →
  project P transfer ≡ recorded →
  ((o : ObservableSurface P) → project P (process) ≡ o) → ⊥
noSectionConstant P p q all with all (project P transfer)
... | equality = λ ()

-- Direct no-section proofs: the observable value `unrecorded` has no preimage.
auNoSection : NoSection auProjection
auNoSection (recover , section) with recover unrecorded | section unrecorded
... | process  | ()
... | transfer | ()

euNoSection : NoSection euProjection
euNoSection (recover , section) with recover unrecorded | section unrecorded
... | process  | ()
... | transfer | ()

promotionEvidenceExtraction :
  (P : RegulatoryProjection) →
  (E : ComplianceEvidence P) →
  (candidate : Candidate E) →
  Promoted E candidate →
  Σ (Receipt E) λ receipt →
  Σ (Verifier E) λ verifier →
    Σ (receiptSupports E receipt candidate) λ _ →
      verifierAccepts E verifier receipt
promotionEvidenceExtraction P E candidate
  (promoted-by receipt verifier support accepted) =
  receipt , (verifier , (support , accepted))

auGuards : RegulatoryGuardBundle auProjection
auGuards = record
  { noGlobalReconstruction = auNoSection
  ; noAutomaticPromotion = promotionEvidenceExtraction auProjection
  }

euGuards : RegulatoryGuardBundle euProjection
euGuards = record
  { noGlobalReconstruction = euNoSection
  ; noAutomaticPromotion = promotionEvidenceExtraction euProjection
  }

projectionAtExample : Authority → RegulatoryProjection
projectionAtExample au = auProjection
projectionAtExample eu = euProjection

exampleBundle : AuthorityBundle
exampleBundle = record
  { SharedActivity = Activity
  ; AuthorityIndex = Authority
  ; projectionAt = projectionAtExample
  ; embedActivity = λ _ activity → activity
  ; bundleReading = "Two independent authority projections over one activity carrier."
  }

exampleEffectiveSurface : EffectiveObligationSurface exampleBundle
exampleEffectiveSurface = record
  { normalize = λ x → x
  ; normalizationStable = λ _ → refl
  ; effectiveReading = "Effective obligations are derived and retain authority provenance."
  }

exampleRelation :
  ObligationRelation exampleBundle exampleEffectiveSurface
exampleRelation = record
  { relation = λ { (au , disclose) (eu , prohibitTransfer) → blocks
                 ; _ _ → compatible }
  ; relationReading = "The finite model includes one explicit cross-authority blocking edge."
  }

exampleConflict :
  ConflictWitness exampleBundle exampleEffectiveSurface exampleRelation
exampleConflict = record
  { leftObligation = au , disclose
  ; rightObligation = eu , prohibitTransfer
  ; conflictProof = refl
  ; conflictReading = "A conflict witness must prove that the indexed relation is blocks."
  }

exampleGraph : RegulatoryConflictGraph
exampleGraph = record
  { Node = TaggedObligation exampleBundle
  ; relation = relation exampleRelation
  ; graphReading = "Provenance-tagged obligation conflict graph."
  }

guardsAtExample :
  (i : Authority) → RegulatoryGuardBundle (projectionAtExample i)
guardsAtExample au = auGuards
guardsAtExample eu = euGuards

exampleTheoryBundle : RegulatoryTheoryBundle
exampleTheoryBundle = record
  { authorities = exampleBundle
  ; obligations = exampleEffectiveSurface
  ; obligationRelation = exampleRelation
  ; conflictGraph = exampleGraph
  ; guardsAt = guardsAtExample
  ; theoryReading = "Finite nontrivial regulatory anatomy witness bundle."
  }

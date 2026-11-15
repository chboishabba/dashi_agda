module DASHI.Governance.CrenshawRightsReformDualEffectExact where

-- Source motivation: Kimberle W. Crenshaw, "Race, Reform, and
-- Retrenchment: Transformation and Legitimation in Antidiscrimination
-- Law", Harvard Law Review 101 (1988), 1331-1387.
-- Crenshaw analyses the tension between pragmatic use of rights and
-- legal legitimation of persistent racial hierarchy. The finite
-- demonstration below is a DASHI construction, NOT a reproduction of
-- a historical event or a universal theorem that reform fails.
-- No inference about judicial motivation or individual psychology.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF

data ReformWorld : Set where
  formalRightsWithoutMaterialTransfer
  formalRightsWithMaterialTransfer : ReformWorld

formalRecognition : ReformWorld → Bool
formalRecognition _ = true

materialReallocation : ReformWorld → Bool
materialReallocation formalRightsWithoutMaterialTransfer = false
materialReallocation formalRightsWithMaterialTransfer = true

legalRightsUsable : ReformWorld → Bool
legalRightsUsable _ = true

-- A statutory recognition may be a real legal resource and nevertheless
-- fail to determine the distribution of material institutional power.
sameFormalRightDifferentMaterialOutcome :
  INF.NonFactorabilityWitness formalRecognition materialReallocation
sameFormalRightDifferentMaterialOutcome =
  INF.nonFactorabilityWitness
    formalRightsWithoutMaterialTransfer
    formalRightsWithMaterialTransfer
    refl (λ ())

formalRightDoesNotGuaranteeMaterialTransformation :
  INF.FactorsThrough formalRecognition materialReallocation → ⊥
formalRightDoesNotGuaranteeMaterialTransformation =
  INF.witnessRulesOutEveryFlatFactorisation
    sameFormalRightDifferentMaterialOutcome

arbitraryRightsRechartCannotRecoverMaterialOutcome :
  ∀ {R : Set} (rechart : Bool → R) →
  INF.FactorsThrough
    (λ w → rechart (formalRecognition w))
    materialReallocation → ⊥
arbitraryRightsRechartCannotRecoverMaterialOutcome rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart sameFormalRightDifferentMaterialOutcome

rightsStillInstrumentallyUsableInBothWorlds :
  legalRightsUsable formalRightsWithoutMaterialTransfer ≡ true
  × legalRightsUsable formalRightsWithMaterialTransfer ≡ true
rightsStillInstrumentallyUsableInBothWorlds = refl , refl

-- This explicitly blocks the false dichotomy 'rights are liberation' vs
-- 'rights are wholly useless'. Rights' strategic availability, judicial
-- recognition and material redistribution occupy distinct coordinates.
record RightsAmbivalenceWitness : Set where
  constructor rights-ambivalence
  field
    identicalFormalRecognition :
      formalRecognition formalRightsWithoutMaterialTransfer
      ≡ formalRecognition formalRightsWithMaterialTransfer
    noGuaranteedMaterialGain :
      materialReallocation formalRightsWithoutMaterialTransfer
      ≡ false
    materialGainPossible :
      materialReallocation formalRightsWithMaterialTransfer
      ≡ true
    formalRightsStillUseful :
      legalRightsUsable formalRightsWithoutMaterialTransfer ≡ true

rightsReformAmbivalenceCountermodel : RightsAmbivalenceWitness
rightsReformAmbivalenceCountermodel =
  rights-ambivalence refl refl refl refl

-- Historically grounded connections from slavery to contemporary legal
-- institutions require independently supplied archival and causal records.
-- We do not make a causal historical arrow true by a model constructor.
record HistoricalInstitutionalEvidence (Era Agency : Set) : Set₁ where
  field
    legallyDocumentedTransition : Era → Era → Set
    institutionDocumentedInEra : Agency → Era → Set
    enforceableLegalRule : Agency → Era → Set
    evidenceOfMaterialEffect : Agency → Era → Set
    archivalProvenanceReviewed : Era → Set

-- Similarly, incarceration and school discipline need separate source
-- evidence; neither can be inferred from employment Title VII litigation.
record CarceralBridgeRequirements (School Enforcement : Set) : Set₁ where
  field
    schoolPolicyReceipt : School → Set
    disciplinaryConsequenceReceipt : School → Set
    enforcementPracticeReceipt : Enforcement → Set
    validatedCrossInstitutionalLink : School → Enforcement → Set

module DASHI.Physics.Closure.YMResidualSpatialSupportCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMEffectiveActionSpatialOnlyBridge as Bridge

------------------------------------------------------------------------
-- Sprint 82 residual spatial-support core.
--
-- This module supplies the missing typed term/link layer below
-- ResidualEffectiveActionSpatialSupportEvidence.  It proves the internal
-- support theorem once the actual temporal-term absorption and term-use
-- classification evidence is supplied.  It does not derive those analytic
-- evidence objects from the older receipt booleans.

data ActionTermSector : Set where
  transferSector : ActionTermSector
  residualSector : ActionTermSector

transferNotResidual :
  transferSector ≡ residualSector →
  ⊥
transferNotResidual ()

record ActionTerm : Set where
  constructor actionTerm
  field
    actionTermId : Support.Identifier
    actionTermSector : ActionTermSector

open ActionTerm public

record TemporalOrMixedTerm (t : ActionTerm) : Set where
  constructor temporalOrMixedTerm
  field
    temporalOrMixedWitness : Support.Identifier
    temporalOrMixedIsTransfer :
      actionTermSector t ≡ transferSector

record TransferMatrixTerm (t : ActionTerm) : Set where
  constructor transferMatrixTerm
  field
    transferMatrixSector :
      actionTermSector t ≡ transferSector

record ResidualActionTerm (t : ActionTerm) : Set where
  constructor residualActionTerm
  field
    residualActionSector :
      actionTermSector t ≡ residualSector

record TermUsesLink (t : ActionTerm) (e : Support.Link) : Set where
  constructor termUsesLink
  field
    termUseWitness : Support.Identifier
    temporalUseImpliesTransfer :
      Support.TemporalLink e →
      actionTermSector t ≡ transferSector

record AbsorbedNotResidual (t : ActionTerm) : Set where
  constructor absorbedNotResidual
  field
    absorbedAsTransferMatrixTerm :
      TransferMatrixTerm t
    notResidualAfterTransferAbsorption :
      ResidualActionTerm t → ⊥

record TemporalTermAbsorbedNotResidualEvidence : Set₁ where
  field
    temporalTermIsTransferMatrixTerm :
      (t : ActionTerm) →
      TemporalOrMixedTerm t →
      TransferMatrixTerm t

    transferMatrixTermNotResidual :
      (t : ActionTerm) →
      TransferMatrixTerm t →
      ResidualActionTerm t →
      ⊥

open TemporalTermAbsorbedNotResidualEvidence public

temporalTermAbsorbedNotResidual :
  TemporalTermAbsorbedNotResidualEvidence →
  (t : ActionTerm) →
  TemporalOrMixedTerm t →
  AbsorbedNotResidual t
temporalTermAbsorbedNotResidual evidence t temporal =
  record
    { absorbedAsTransferMatrixTerm =
        temporalTermIsTransferMatrixTerm evidence t temporal
    ; notResidualAfterTransferAbsorption =
        transferMatrixTermNotResidual
          evidence
          t
          (temporalTermIsTransferMatrixTerm evidence t temporal)
    }

record TemporalLinkUseClassifiesTemporalTerm : Set₁ where
  field
    temporalLinkUseIsTemporalOrMixed :
      (t : ActionTerm) →
      (e : Support.Link) →
      TermUsesLink t e →
      Support.TemporalLink e →
      TemporalOrMixedTerm t

open TemporalLinkUseClassifiesTemporalTerm public

canonicalTemporalLinkUseClassifiesTemporalTerm :
  TemporalLinkUseClassifiesTemporalTerm
canonicalTemporalLinkUseClassifiesTemporalTerm =
  record
    { temporalLinkUseIsTemporalOrMixed =
        λ t e use temporalLink →
          temporalOrMixedTerm
            (actionTermId t)
            (TermUsesLink.temporalUseImpliesTransfer use temporalLink)
    }

transferMatrixTermNotResidualBySector :
  (t : ActionTerm) →
  TransferMatrixTerm t →
  ResidualActionTerm t →
  ⊥
transferMatrixTermNotResidualBySector t (transferMatrixTerm refl) (residualActionTerm ())

temporalTermAbsorbedNotResidualFromSectors :
  TemporalTermAbsorbedNotResidualEvidence
temporalTermAbsorbedNotResidualFromSectors =
  record
    { temporalTermIsTransferMatrixTerm =
        λ t temporal →
          transferMatrixTerm
            (TemporalOrMixedTerm.temporalOrMixedIsTransfer temporal)
    ; transferMatrixTermNotResidual =
        transferMatrixTermNotResidualBySector
    }

record ResidualTermHasNoTemporalSupportEvidence : Set₁ where
  field
    residualTermHasNoTemporalSupport :
      (t : ActionTerm) →
      (e : Support.Link) →
      ResidualActionTerm t →
      TermUsesLink t e →
      Support.TemporalLink e →
      ⊥

open ResidualTermHasNoTemporalSupportEvidence public

residualTermHasNoTemporalSupportFromAbsorption :
  TemporalTermAbsorbedNotResidualEvidence →
  TemporalLinkUseClassifiesTemporalTerm →
  ResidualTermHasNoTemporalSupportEvidence
residualTermHasNoTemporalSupportFromAbsorption absorption classifier =
  record
    { residualTermHasNoTemporalSupport =
        λ t e residual use temporalLink →
          transferMatrixTermNotResidual
            absorption
            t
            (temporalTermIsTransferMatrixTerm
              absorption
              t
              (temporalLinkUseIsTemporalOrMixed
                classifier
                t
                e
                use
                temporalLink))
            residual
    }

data AllTermUsesLinks (t : ActionTerm) : List Support.Link → Set where
  allTermUsesNil :
    AllTermUsesLinks t []
  allTermUsesCons :
    {e : Support.Link} →
    {es : List Support.Link} →
    TermUsesLink t e →
    AllTermUsesLinks t es →
    AllTermUsesLinks t (e ∷ es)

notTemporalLinkImpliesSpatialLink :
  (e : Support.Link) →
  (Support.TemporalLink e → ⊥) →
  Support.SpatialLink e
notTemporalLinkImpliesSpatialLink (Support.link linkId Support.temporal) noTemporal =
  ⊥-elim (noTemporal refl)
notTemporalLinkImpliesSpatialLink (Support.link linkId Support.spatial) noTemporal =
  refl

allSpatialFromNoTemporalTermSupport :
  {t : ActionTerm} →
  {links : List Support.Link} →
  ((e : Support.Link) →
   TermUsesLink t e →
   Support.TemporalLink e →
   ⊥) →
  AllTermUsesLinks t links →
  Support.AllSpatialLinks links
allSpatialFromNoTemporalTermSupport noTemporal allTermUsesNil =
  Support.allSpatialNil
allSpatialFromNoTemporalTermSupport noTemporal
  (allTermUsesCons {e = e} use uses) =
  Support.allSpatialCons
    (notTemporalLinkImpliesSpatialLink e (noTemporal e use))
    (allSpatialFromNoTemporalTermSupport noTemporal uses)

record ResidualPolymerTermSupportSemantics : Set₁ where
  field
    residualTermForPolymer :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      Support.PolymerIn S γ →
      ActionTerm

    residualTermForPolymerIsResidual :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      (member : Support.PolymerIn S γ) →
      ResidualActionTerm (residualTermForPolymer S γ member)

    polymerSupportLinksUseResidualTerm :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      (member : Support.PolymerIn S γ) →
      AllTermUsesLinks
        (residualTermForPolymer S γ member)
        (Support.supportLinks γ)

open ResidualPolymerTermSupportSemantics public

residualSpatialSupportEvidenceFromTermNoTemporal :
  ResidualTermHasNoTemporalSupportEvidence →
  ResidualPolymerTermSupportSemantics →
  Bridge.ResidualEffectiveActionSpatialSupportEvidence
residualSpatialSupportEvidenceFromTermNoTemporal noTemporal semantics =
  record
    { residualSpatialSupport =
        λ S γ member →
          allSpatialFromNoTemporalTermSupport
            (λ e use temporalLink →
              residualTermHasNoTemporalSupport
                noTemporal
                (residualTermForPolymer semantics S γ member)
                e
                (residualTermForPolymerIsResidual semantics S γ member)
                use
                temporalLink)
            (polymerSupportLinksUseResidualTerm semantics S γ member)
    }

residualSpatialSupportEvidenceFromAbsorption :
  TemporalTermAbsorbedNotResidualEvidence →
  TemporalLinkUseClassifiesTemporalTerm →
  ResidualPolymerTermSupportSemantics →
  Bridge.ResidualEffectiveActionSpatialSupportEvidence
residualSpatialSupportEvidenceFromAbsorption absorption classifier semantics =
  residualSpatialSupportEvidenceFromTermNoTemporal
    (residualTermHasNoTemporalSupportFromAbsorption absorption classifier)
    semantics

record Sprint82ResidualSpatialSupportCoreDefined : Set₂ where
  field
    actionTermCarrierDefined :
      ActionTerm ≡ ActionTerm
    temporalOrMixedTermPredicateDefined :
      TemporalOrMixedTerm ≡ TemporalOrMixedTerm
    transferMatrixTermPredicateDefined :
      TransferMatrixTerm ≡ TransferMatrixTerm
    residualActionTermPredicateDefined :
      ResidualActionTerm ≡ ResidualActionTerm
    termUsesLinkPredicateDefined :
      TermUsesLink ≡ TermUsesLink
    temporalAbsorptionEvidenceDefined :
      TemporalTermAbsorbedNotResidualEvidence
        ≡ TemporalTermAbsorbedNotResidualEvidence
    temporalLinkClassificationEvidenceDefined :
      TemporalLinkUseClassifiesTemporalTerm
        ≡ TemporalLinkUseClassifiesTemporalTerm
    residualNoTemporalEvidenceDefined :
      ResidualTermHasNoTemporalSupportEvidence
        ≡ ResidualTermHasNoTemporalSupportEvidence
    residualPolymerSupportSemanticsDefined :
      ResidualPolymerTermSupportSemantics
        ≡ ResidualPolymerTermSupportSemantics
    residualSpatialSupportAssemblyDefined :
      residualSpatialSupportEvidenceFromAbsorption
        ≡ residualSpatialSupportEvidenceFromAbsorption

sprint82ResidualSpatialSupportCoreDefined :
  Sprint82ResidualSpatialSupportCoreDefined
sprint82ResidualSpatialSupportCoreDefined =
  record
    { actionTermCarrierDefined = refl
    ; temporalOrMixedTermPredicateDefined = refl
    ; transferMatrixTermPredicateDefined = refl
    ; residualActionTermPredicateDefined = refl
    ; termUsesLinkPredicateDefined = refl
    ; temporalAbsorptionEvidenceDefined = refl
    ; temporalLinkClassificationEvidenceDefined = refl
    ; residualNoTemporalEvidenceDefined = refl
    ; residualPolymerSupportSemanticsDefined = refl
    ; residualSpatialSupportAssemblyDefined = refl
    }

temporalTermAbsorbedNotResidualEvidenceProved : Bool
temporalTermAbsorbedNotResidualEvidenceProved = false

temporalLinkUseClassifiesTemporalTermProved : Bool
temporalLinkUseClassifiesTemporalTermProved = true

residualPolymerTermSupportSemanticsProved : Bool
residualPolymerTermSupportSemanticsProved = false

residualEffectiveActionSpatialSupportEvidenceUnconditional : Bool
residualEffectiveActionSpatialSupportEvidenceUnconditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data Sprint82ResidualSpatialSupportPromotion : Set where

sprint82ResidualSpatialSupportPromotionImpossibleHere :
  Sprint82ResidualSpatialSupportPromotion →
  ⊥
sprint82ResidualSpatialSupportPromotionImpossibleHere ()

record Sprint82ResidualSpatialSupportCoreBoundary : Set₂ where
  field
    coreDefined :
      Sprint82ResidualSpatialSupportCoreDefined
    temporalAbsorptionEvidenceStillOpen :
      temporalTermAbsorbedNotResidualEvidenceProved ≡ false
    temporalLinkClassificationStillOpen :
      temporalLinkUseClassifiesTemporalTermProved ≡ true
    residualPolymerSupportSemanticsStillOpen :
      residualPolymerTermSupportSemanticsProved ≡ false
    residualSpatialSupportStillConditional :
      residualEffectiveActionSpatialSupportEvidenceUnconditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      Sprint82ResidualSpatialSupportPromotion → ⊥

sprint82ResidualSpatialSupportCoreBoundary :
  Sprint82ResidualSpatialSupportCoreBoundary
sprint82ResidualSpatialSupportCoreBoundary =
  record
    { coreDefined = sprint82ResidualSpatialSupportCoreDefined
    ; temporalAbsorptionEvidenceStillOpen = refl
    ; temporalLinkClassificationStillOpen = refl
    ; residualPolymerSupportSemanticsStillOpen = refl
    ; residualSpatialSupportStillConditional = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere =
        sprint82ResidualSpatialSupportPromotionImpossibleHere
    }

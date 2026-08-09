module DASHI.Culture.AmalekAuthorityProjectionBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.SemioticPhallicLackAmalekBridge as Semiotic
import DASHI.Governance.DependentAuthorityCoercionKernel as Coercion

data AuthorityProjectionSurface : Set where
  sacredLegitimationSurface authorityTruthCollapseSurface doubtPenaltySurface : AuthorityProjectionSurface
  dissentEnemySurface disclosureAttackSurface survivorCastrationSurface : AuthorityProjectionSurface
  humanPollutantSurface missionShieldSurface neutralReviewSurface : AuthorityProjectionSurface

canonicalAuthorityProjectionSurfaces : List AuthorityProjectionSurface
canonicalAuthorityProjectionSurfaces =
  sacredLegitimationSurface ∷ authorityTruthCollapseSurface ∷ doubtPenaltySurface
  ∷ dissentEnemySurface ∷ disclosureAttackSurface ∷ survivorCastrationSurface
  ∷ humanPollutantSurface ∷ missionShieldSurface ∷ neutralReviewSurface ∷ []

data ProjectionTargetKind : Set where
  propositionTarget behaviourTarget institutionalRoleTarget namedPersonTarget : ProjectionTargetKind
  childTarget survivorTarget humanGroupTarget : ProjectionTargetKind

data AdmissibleAmalekUse : Set where
  recursiveTerminalisationUse rememberedHarmToDominationProtocolUse enemyProductionRiskUse : AdmissibleAmalekUse

data ForbiddenAmalekUse : Set where
  childAsEnemyUse dissenterAsEnemyUse survivorAsEnemyUse religionAsEnemyUse : ForbiddenAmalekUse
  ethnicGroupAsEnemyUse nationalGroupAsEnemyUse inheritedCollectiveGuiltUse exterminatoryPermissionUse : ForbiddenAmalekUse

data ForbiddenAmalekPromotion : Set where

forbiddenAmalekPromotionImpossible : ForbiddenAmalekPromotion → ⊥
forbiddenAmalekPromotionImpossible ()

record ClosedAuthorityLoop : Set where
  constructor closedAuthorityLoop
  field
    authoritySelfValidates externalEvidenceDelegitimised doubtPenalised : Bool
    dissentReclassifiedAsFault correctionChannelIndependent : Bool
    loopReading : String

open ClosedAuthorityLoop public

canonicalClosedAuthorityRisk : ClosedAuthorityLoop
canonicalClosedAuthorityRisk = closedAuthorityLoop true true true true false
  "Authority validates its own authority, rejects external correction, penalises doubt, and converts dissent into confirming fault."

canonicalClosedAuthorityRiskHasNoIndependentCorrection : correctionChannelIndependent canonicalClosedAuthorityRisk ≡ false
canonicalClosedAuthorityRiskHasNoIndependentCorrection = refl

record CorrectionInterface : Set where
  constructor correctionInterface
  field
    safeDisclosure independentReview evidenceParticularised retaliationBlocked : Bool
    childOrDependentWelfarePriority institutionCanRevise : Bool

open CorrectionInterface public

canonicalCorrectionInterface : CorrectionInterface
canonicalCorrectionInterface = correctionInterface true true true true true true

record AmalekAuthorityProjectionBoundary : Set where
  constructor amalekAuthorityProjectionBoundary
  field
    semioticBridge : Semiotic.SemioticPhallicLackAmalekBridge
    coercionBoundary : Coercion.DependentAuthorityCoercionBoundary
    authorityProjectionSurfaces : List AuthorityProjectionSurface
    admissibleUses : List AdmissibleAmalekUse
    correctionInterface : CorrectionInterface
    authorityClosureTracked : Bool
    authorityClosureTrackedIsTrue : authorityClosureTracked ≡ true
    childDissentAsEnemyPromotion : Bool
    childDissentAsEnemyPromotionIsFalse : childDissentAsEnemyPromotion ≡ false
    survivorDisclosureAsAttackPromotion : Bool
    survivorDisclosureAsAttackPromotionIsFalse : survivorDisclosureAsAttackPromotion ≡ false
    humanGroupAsPollutantPromotion : Bool
    humanGroupAsPollutantPromotionIsFalse : humanGroupAsPollutantPromotion ≡ false
    institutionalMissionShieldPromotion : Bool
    institutionalMissionShieldPromotionIsFalse : institutionalMissionShieldPromotion ≡ false
    sacredAuthorityEqualsTruthPromotion : Bool
    sacredAuthorityEqualsTruthPromotionIsFalse : sacredAuthorityEqualsTruthPromotion ≡ false
    rememberedHarmLicencesDominationPromotion : Bool
    rememberedHarmLicencesDominationPromotionIsFalse : rememberedHarmLicencesDominationPromotion ≡ false
    ethnicOrReligiousEssentialismPromotion : Bool
    ethnicOrReligiousEssentialismPromotionIsFalse : ethnicOrReligiousEssentialismPromotion ≡ false
    boundaryReading : String

open AmalekAuthorityProjectionBoundary public

canonicalAmalekAuthorityProjectionBoundary : AmalekAuthorityProjectionBoundary
canonicalAmalekAuthorityProjectionBoundary =
  amalekAuthorityProjectionBoundary
    Semiotic.canonicalSemioticPhallicLackAmalekBridge
    Coercion.canonicalDependentAuthorityCoercionBoundary
    canonicalAuthorityProjectionSurfaces
    (recursiveTerminalisationUse ∷ rememberedHarmToDominationProtocolUse ∷ enemyProductionRiskUse ∷ [])
    canonicalCorrectionInterface
    true refl false refl false refl false refl false refl false refl false refl false refl
    "Amalek is restricted to the recursive operator-pattern by which remembered injury becomes a warrant for enemy production or repeatable domination. Child dissent, survivor disclosure, religion, ethnicity, nationality, and human groups cannot inhabit the predicate. Independent correction and safe disclosure interrupt the loop."

canonicalChildDissentAsEnemyPromotionFalse : childDissentAsEnemyPromotion canonicalAmalekAuthorityProjectionBoundary ≡ false
canonicalChildDissentAsEnemyPromotionFalse = childDissentAsEnemyPromotionIsFalse canonicalAmalekAuthorityProjectionBoundary

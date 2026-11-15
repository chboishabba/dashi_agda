module DASHI.Governance.MonsterThreeLocalCognitiveOriginNonIdentificationExact where

-- Original DASHI cross-owner negative control.
-- The two 3-local Monster subgroup charts are sourced mathematical
-- symmetry objects; none is a forensic classifier for real people,
-- social networks, institutional intentions, or covert coordination.
-- Provenance remains query-indexed to the actual observer.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.CognitiveWarfareAdmissibleDetectionExact as CW
import DASHI.Moonshine.MoonshineZ3OrbifoldThreeLocalSiblingExact as ThreeLocal

-- Same target-local observation, different independently selected origins:
-- the exact original cognitive-warfare counterexample.
sameLocalNetworkAppearance :
  CW.targetProject CW.organicHidden
    ≡ CW.targetProject CW.influenceHidden
sameLocalNetworkAppearance = CW.targetLocalCollision

sameNetworkAppearanceDifferentOrigin :
  NF.NonFactorabilityWitness CW.targetProject CW.origin
sameNetworkAppearanceDifferentOrigin =
  NF.nonFactorabilityWitness
    CW.organicHidden CW.influenceHidden
    CW.targetLocalCollision
    CW.organicOriginNotInfluence

-- Any attempt to classify source-controller origin by first reducing
-- observed interaction appearance to a 3-local Monster label still loses
-- the witness pair, independent of which label is assigned.
threeLocalSymmetryLabelCannotIdentifyController :
  (chart : CW.TargetObservation → ThreeLocal.ThreeLocalSiblingName) →
  NF.FactorsThrough
    (λ history → chart (CW.targetProject history))
    CW.origin → ⊥
threeLocalSymmetryLabelCannotIdentifyController chart =
  NF.rechartingCannotRecoverErasedPhenomenon
    chart sameNetworkAppearanceDifferentOrigin

-- Nor can an arbitrary group character/stabilizer/normal-form label
-- applied to the same original target projection repair missing provenance.
arbitraryNetworkSymmetryRechartCannotIdentifyOrigin :
  ∀ {SymmetrySummary : Set}
  (chart : CW.TargetObservation → SymmetrySummary) →
  NF.FactorsThrough
    (λ history → chart (CW.targetProject history))
    CW.origin → ⊥
arbitraryNetworkSymmetryRechartCannotIdentifyOrigin chart =
  NF.rechartingCannotRecoverErasedPhenomenon
    chart sameNetworkAppearanceDifferentOrigin

-- The non-promotion theorem does not forbid an independently sourced
-- detection channel with new information: original admissible provenance
-- inspection already supplies that richer observer.
-- The same-sector number 65610 in the 3-local chart is never a
-- certificate of the same action or of source-controller identity.

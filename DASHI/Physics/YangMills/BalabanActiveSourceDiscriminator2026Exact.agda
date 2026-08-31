module DASHI.Physics.YangMills.BalabanActiveSourceDiscriminator2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Physics.YangMills.BalabanUnifiedPresentCutSchwingerRecoveryRound140Exact as YM

------------------------------------------------------------------------
-- ACTIVE SOURCE DISCRIMINATION FOR THE CURRENT BALABAN FRONTIER
--
-- This is repository-native proof-search machinery.  It does not attribute an
-- experiment/discriminator calculus to Balaban and it does not assert that the
-- remaining literal source equalities are proved.
--
-- Current same-object spine inherited from merged R132--R144:
--   density -> repository RG state -> BC1/BC2 action
--   -> whole localized D1 sum -> selected stress -> Schwinger endpoint,
-- with explicit coupling-history/scale/domain welds.
--
-- The remaining physical work is therefore represented as source-recovery
-- coordinates rather than as another parallel analytic object.
------------------------------------------------------------------------

data SourceSeam : Set where
  densityToRepositoryState
  repositoryStateToBC1Potential
  stressVariationToWholeLocalizedD1
  metricPerturbationAdmissibility
  a1A2ToBetaDensityHistory
  cmp119MeasureSchwingerEndpoint
  : SourceSeam

seamReference : SourceSeam → String
seamReference densityToRepositoryState =
  "literal CMP122 density -> existing CombinedRG repository-state realization"
seamReference repositoryStateToBC1Potential =
  "selected repository state -> exact BC1 effective-potential realization"
seamReference stressVariationToWholeLocalizedD1 =
  "selected stress first variation -> exact finite localized CMP116 D1 sum"
seamReference metricPerturbationAdmissibility =
  "metric perturbation/tangent admissibility on the canonical BC1 radius"
seamReference a1A2ToBetaDensityHistory =
  "A1/A2 physical couplings -> same beta-driven density history"
seamReference cmp119MeasureSchwingerEndpoint =
  "CMP119 / finite-measure / Schwinger endpoint source receipts"

------------------------------------------------------------------------
-- Fine source-recovery hypotheses.  These are search states, not claims about
-- what Balaban's source actually proves.
------------------------------------------------------------------------

data SourceWorld : Set where
  labelsOnly
  actionRealised
  stressRealised
  literalRecoveryReady
  : SourceWorld

-- Public/narrative naming cannot distinguish these worlds.
data CoarseSourceSurface : Set where sameBalabanRecoveryClaim : CoarseSourceSurface

coarseSource : SourceWorld → CoarseSourceSurface
coarseSource _ = sameBalabanRecoveryClaim

------------------------------------------------------------------------
-- A consumer-directed probe asks the decisive question: has the complete
-- literal same-object recovery package been established?  In a real source
-- reconstruction this observation must be supplied by source inspection or an
-- exact proof/certificate; this finite fixture only proves the planner shape.
------------------------------------------------------------------------

fullLiteralProbe : SourceWorld → Bool
fullLiteralProbe labelsOnly = false
fullLiteralProbe actionRealised = false
fullLiteralProbe stressRealised = false
fullLiteralProbe literalRecoveryReady = true

literalRecoveryBundle : Synthesis.ExperimentBundle SourceWorld
literalRecoveryBundle =
  Synthesis.experimentBundle
    Bool
    fullLiteralProbe
    1
    "Balaban literal same-object recovery discriminator"
    "source-exact reconstruction receipt; not numerical calibration"

literalRecoveryCollision : Synthesis.CurrentObserverCollision coarseSource
literalRecoveryCollision =
  Synthesis.currentObserverCollision labelsOnly literalRecoveryReady refl

literalRecoverySeparates :
  Synthesis.BundleSeparates literalRecoveryBundle labelsOnly literalRecoveryReady
literalRecoverySeparates = Synthesis.bundleSeparates λ ()

literalRecoveryLanguageExtension :
  Synthesis.DiscriminatingLanguageExtension coarseSource
literalRecoveryLanguageExtension =
  Synthesis.discriminatingLanguageExtension
    literalRecoveryCollision
    literalRecoveryBundle
    literalRecoverySeparates

------------------------------------------------------------------------
-- Sequential planner instantiation.
--
-- The downstream consumer here is only the decision whether literal source
-- recovery is ready.  We deliberately do NOT ask the experiment planner to
-- identify the whole source world.  This mirrors the generic consumer-relative
-- closure theorem already owned by the repository.
------------------------------------------------------------------------

data InitialEvidence : Set where sourceAuditOpen : InitialEvidence

compatible : InitialEvidence → SourceWorld → Set
compatible sourceAuditOpen _ = ⊤

recoveryDecision : SourceWorld → Bool
recoveryDecision = fullLiteralProbe

literalProbeClosesDecision :
  Synthesis.ProspectivelyClosesConsumer compatible recoveryDecision literalRecoveryBundle
literalProbeClosesDecision sourceAuditOpen witness witnessCompatible x y hx hy =
  trans (proj₂ hx) (sym (proj₂ hy))

literalRecoverySequentialPlan :
  Planner.SequentialConsumerPlan recoveryDecision (compatible sourceAuditOpen)
literalRecoverySequentialPlan =
  Planner.oneShotConsumerClosingPlan
    compatible
    recoveryDecision
    sourceAuditOpen
    literalRecoveryBundle
    literalProbeClosesDecision

------------------------------------------------------------------------
-- Current authority boundary inherited from the actual YM compiler.
------------------------------------------------------------------------

compilerLevel = YM.unifiedPresentCutSchwingerRecoveryCompilerLevel
literalRecoveryLevel = YM.literalUnifiedPresentCutSchwingerRecoveryLevel

record BalabanActiveSourceBoundary : Set where
  constructor balabanActiveSourceBoundary
  field
    matchingSourceLabelsCloseLiteralRecovery : Bool
    matchingSourceLabelsCloseLiteralRecoveryIsFalse :
      matchingSourceLabelsCloseLiteralRecovery ≡ false
    sourceProbeMayRefineRecoveryFibre : Bool
    sourceProbeMayRefineRecoveryFibreIsTrue : sourceProbeMayRefineRecoveryFibre ≡ true
    consumerClosureRequiresWholeSourceIdentity : Bool
    consumerClosureRequiresWholeSourceIdentityIsFalse :
      consumerClosureRequiresWholeSourceIdentity ≡ false
    machineCheckedCompilerImpliesLiteralSourceInhabitation : Bool
    machineCheckedCompilerImpliesLiteralSourceInhabitationIsFalse :
      machineCheckedCompilerImpliesLiteralSourceInhabitation ≡ false

canonicalBalabanActiveSourceBoundary : BalabanActiveSourceBoundary
canonicalBalabanActiveSourceBoundary =
  balabanActiveSourceBoundary
    false refl
    true refl
    false refl
    false refl

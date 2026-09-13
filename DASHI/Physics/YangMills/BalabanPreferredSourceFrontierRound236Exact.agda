{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredSourceFrontierRound236Exact where

------------------------------------------------------------------------
-- ROUND236 / DEPENDENCY-ACCURATE PREFERRED SOURCE FRONTIER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as ESource
import DASHI.Physics.YangMills.BalabanSourceFixedR108EffectiveActionFamilyRound213Exact as Semantics
import DASHI.Physics.YangMills.BalabanSourceFixedRegularESemanticsRound234Exact as EWeld
import DASHI.Physics.YangMills.BalabanSourceFixedLocalizationRadiusSplitRound235Exact as Localization
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as D2
import DASHI.Physics.YangMills.BalabanPreferredA2FrontierRound231Exact as A2
import DASHI.Physics.YangMills.BalabanPreferredD1SemanticsFrontierRound228Exact as D1
import DASHI.Physics.YangMills.BalabanCMP119RegularEPreferredContinuationRound222Exact as Continue
import DASHI.Physics.YangMills.BalabanCMP119RegularEPreferredBC1Round223Exact as BC1


data PreferredSourceLeaf236 : Set where
  literalCMP122EffectiveDensitySemantics : PreferredSourceLeaf236
  literalCMP119RegularESourceProjection : PreferredSourceLeaf236
  sourceDensitySemanticsIsCMP119RegularE : PreferredSourceLeaf236
  literalSourceFixedCMP116Localization : PreferredSourceLeaf236
  literalUniformCMP116CommonRadius : PreferredSourceLeaf236
  regularEContinuationCompiler : PreferredSourceLeaf236
  regularEToBC1PotentialSameObject : PreferredSourceLeaf236
  physicalSecondVariationLinearity : PreferredSourceLeaf236
  literalCMP109Equation51Binding : PreferredSourceLeaf236
  literalCMP109LocalBetaDerivativeBound : PreferredSourceLeaf236
  generatedHistoryDerivativeIsCMP116BetaMark : PreferredSourceLeaf236
  literalCMP109MarginalPlusIrrelevantDecomposition : PreferredSourceLeaf236
  physicalBC2FirstVariationSemantics : PreferredSourceLeaf236
  literalCMP116SubstitutionTangentIdentification : PreferredSourceLeaf236

data LeafState236 : Set where
  closed open blocked : LeafState236

preferredSourceLeafState236 : PreferredSourceLeaf236 → LeafState236
preferredSourceLeafState236 literalCMP122EffectiveDensitySemantics = open
preferredSourceLeafState236 literalCMP119RegularESourceProjection = open
preferredSourceLeafState236 sourceDensitySemanticsIsCMP119RegularE = blocked
preferredSourceLeafState236 literalSourceFixedCMP116Localization = blocked
preferredSourceLeafState236 literalUniformCMP116CommonRadius = open
preferredSourceLeafState236 regularEContinuationCompiler = closed
preferredSourceLeafState236 regularEToBC1PotentialSameObject = closed
preferredSourceLeafState236 physicalSecondVariationLinearity = open
preferredSourceLeafState236 literalCMP109Equation51Binding = blocked
preferredSourceLeafState236 literalCMP109LocalBetaDerivativeBound = open
preferredSourceLeafState236 generatedHistoryDerivativeIsCMP116BetaMark = open
preferredSourceLeafState236 literalCMP109MarginalPlusIrrelevantDecomposition = blocked
preferredSourceLeafState236 physicalBC2FirstVariationSemantics = open
preferredSourceLeafState236 literalCMP116SubstitutionTangentIdentification = open

-- Independent roots that can be attacked without first paying another leaf.
data IndependentRoot236 : Set where
  rootDensitySemantics : IndependentRoot236
  rootRegularEProjection : IndependentRoot236
  rootCommonRadius : IndependentRoot236
  rootD2Calculus : IndependentRoot236
  rootLocalBetaDerivative : IndependentRoot236
  rootBetaMarkWeld : IndependentRoot236
  rootBC2D1Calculus : IndependentRoot236
  rootSubstitutionTangent : IndependentRoot236

preferredFirstRoot236 : IndependentRoot236
preferredFirstRoot236 = rootDensitySemantics

literalCMP122EffectiveDensitySemanticsLevel : ProofLevel
literalCMP122EffectiveDensitySemanticsLevel =
  Semantics.literalCMP122EffectiveDensitySemanticsLevel

literalCMP119RegularESourceProjectionLevel : ProofLevel
literalCMP119RegularESourceProjectionLevel =
  ESource.literalCMP119RegularESourceProjectionLevel

sourceDensitySemanticsIsCMP119RegularELevel : ProofLevel
sourceDensitySemanticsIsCMP119RegularELevel =
  EWeld.literalSourceDensitySemanticsIsCMP119RegularELevel

literalSourceFixedCMP116LocalizationLevel : ProofLevel
literalSourceFixedCMP116LocalizationLevel =
  Localization.literalSourceFixedCMP116LocalizationLevel

literalUniformCMP116CommonRadiusLevel : ProofLevel
literalUniformCMP116CommonRadiusLevel =
  Radius.literalCMP116UniformCommonRadiusInstantiationLevel

regularEContinuationCompilerLevel : ProofLevel
regularEContinuationCompilerLevel = Continue.preferredRegularEContinuationCompilerLevel

regularEBC1SameObjectCompilerLevel : ProofLevel
regularEBC1SameObjectCompilerLevel = BC1.preferredRegularEBC1CompilerLevel

secondVariationLinearityCompilerLevel : ProofLevel
secondVariationLinearityCompilerLevel = D2.finiteSecondVariationLinearityLevel

literalCMP109Equation51BindingLevel : ProofLevel
literalCMP109Equation51BindingLevel = Eq51.literalCMP109Equation51RepositoryBindingLevel

literalCMP109LocalBetaDerivativeBoundLevel : ProofLevel
literalCMP109LocalBetaDerivativeBoundLevel = A2.localBetaDerivativeLevel

generatedHistoryDerivativeIsCMP116BetaMarkLevel : ProofLevel
generatedHistoryDerivativeIsCMP116BetaMarkLevel = A2.betaMarkSameObjectLevel

literalCMP109MarginalPlusIrrelevantDecompositionLevel : ProofLevel
literalCMP109MarginalPlusIrrelevantDecompositionLevel =
  A2.marginalPlusIrrelevantDecompositionLevel

physicalBC2FirstVariationSemanticsLevel : ProofLevel
physicalBC2FirstVariationSemanticsLevel = D1.physicalBC2FirstVariationSemanticsLevel

literalCMP116SubstitutionTangentIdentificationLevel : ProofLevel
literalCMP116SubstitutionTangentIdentificationLevel =
  D1.literalCMP116SubstitutionTangentIdentificationLevel

round236PhysicalSourceClosure : Bool
round236PhysicalSourceClosure = false

round236ClayPromotion : Bool
round236ClayPromotion = false

round236PhysicalSourceClosureIsFalse : round236PhysicalSourceClosure ≡ false
round236PhysicalSourceClosureIsFalse = refl

round236ClayPromotionIsFalse : round236ClayPromotion ≡ false
round236ClayPromotionIsFalse = refl

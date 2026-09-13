{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredRegularEFrontierRound240Exact where

------------------------------------------------------------------------
-- ROUND240 / CURRENT PREFERRED BC1 SOURCE FRONTIER
--
-- R239 removes the need for a total or post-hoc density -> potential map on the
-- preferred route.  The source semantics consumed by BC1 now starts from the
-- literal CMP119 regular-E coordinate itself:
--
--   S_E1 : selected density rho_k carries the literal CMP119 regular E_k;
--   S_E2 : that literal regular-E carrier has its source-fixed pointwise
--          evaluation B |-> E_k(B).
--
-- Selected density semantics and the equality between the selected effective
-- potential and E_k are compiler output from those two coordinates.  The
-- remaining independent BC1 leaves are localization, common analytic domain,
-- concrete D2 calculus semantics and Eq. (5.1) binding.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as ESource
import DASHI.Physics.YangMills.BalabanRegularEPointwiseSemanticsRound239Exact as Pointwise
import DASHI.Physics.YangMills.BalabanSourceFixedLocalizationRadiusSplitRound235Exact as Localize
import DASHI.Physics.YangMills.BalabanPreferredCommonRadiusFrontierRound232Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51

data PreferredBC1Leaf240 : Set where
  literalCMP119RegularESourceProjection : PreferredBC1Leaf240
  literalCMP119RegularEPointwiseSemantics : PreferredBC1Leaf240
  literalCMP116SelectedLocalization : PreferredBC1Leaf240
  literalCMP116UniformCommonRadius : PreferredBC1Leaf240
  physicalSecondVariationCalculus : PreferredBC1Leaf240
  literalCMP109Equation51Binding : PreferredBC1Leaf240
  selectedDensitySemanticsCompiler : PreferredBC1Leaf240
  regularEToBC1SameObjectCompiler : PreferredBC1Leaf240

data LeafState240 : Set where
  closed open blocked : LeafState240

preferredBC1LeafState240 : PreferredBC1Leaf240 → LeafState240
preferredBC1LeafState240 literalCMP119RegularESourceProjection = open
preferredBC1LeafState240 literalCMP119RegularEPointwiseSemantics = blocked
preferredBC1LeafState240 literalCMP116SelectedLocalization = blocked
preferredBC1LeafState240 literalCMP116UniformCommonRadius = open
preferredBC1LeafState240 physicalSecondVariationCalculus = open
preferredBC1LeafState240 literalCMP109Equation51Binding = blocked
preferredBC1LeafState240 selectedDensitySemanticsCompiler = closed
preferredBC1LeafState240 regularEToBC1SameObjectCompiler = closed

preferredFirstBC1Coordinate240 : PreferredBC1Leaf240
preferredFirstBC1Coordinate240 = literalCMP119RegularESourceProjection

selectedDensitySemanticsCompilerClosed :
  preferredBC1LeafState240 selectedDensitySemanticsCompiler ≡ closed
selectedDensitySemanticsCompilerClosed = refl

regularEToBC1SameObjectCompilerClosed :
  preferredBC1LeafState240 regularEToBC1SameObjectCompiler ≡ closed
regularEToBC1SameObjectCompilerClosed = refl

regularESourceProjectionLevel : ProofLevel
regularESourceProjectionLevel = ESource.literalCMP119RegularESourceProjectionLevel

regularEPointwiseSemanticsLevel : ProofLevel
regularEPointwiseSemanticsLevel = Pointwise.literalCMP119RegularEPointwiseSemanticsLevel

selectedLocalizationLevel : ProofLevel
selectedLocalizationLevel = Localize.literalSourceFixedCMP116LocalizationLevel

uniformCommonRadiusLevel : ProofLevel
uniformCommonRadiusLevel = Radius.literalUniformCommonRadiusLevel

-- There is no narrower existing source-level ProofLevel for just the concrete
-- D2 operator semantics.  Older BC1 surfaces bundle this with Eq.(5.1) and
-- radius inputs, so keep this coordinate explicitly conditional rather than
-- aliasing an over-strong receipt.
physicalSecondVariationCalculusLevel : ProofLevel
physicalSecondVariationCalculusLevel = conditional

literalEquation51BindingLevel : ProofLevel
literalEquation51BindingLevel = Eq51.literalCMP109Equation51RepositoryBindingLevel

round240BC1PhysicalClosure : Bool
round240BC1PhysicalClosure = false

round240BC1PhysicalClosureIsFalse : round240BC1PhysicalClosure ≡ false
round240BC1PhysicalClosureIsFalse = refl

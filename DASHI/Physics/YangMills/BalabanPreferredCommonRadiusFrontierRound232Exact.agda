{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredCommonRadiusFrontierRound232Exact where

------------------------------------------------------------------------
-- ROUND232 / COMMON DOMAIN IS THE CONSUMER; FOUR DEMANDS ARE A PRODUCER
--
-- The differentiated CMP109/CMP116 consumers require one uniform positive
-- common analytic radius on which the background, source, local-activity and
-- substituted-background coordinates all stay inside their source domains.
--
-- Round104's four normalized rational demands are a constructive way to choose
-- such a radius.  They are not the least-privilege physical consumer contract.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Demands
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as Bridge


data PreferredCommonRadiusLeaf232 : Set where
  literalUniformCMP116CommonRadius : PreferredCommonRadiusLeaf232
  firstSecondDerivativeUseSameRadius : PreferredCommonRadiusLeaf232

data LeafState232 : Set where
  closed open blocked : LeafState232

preferredCommonRadiusLeafState232 : PreferredCommonRadiusLeaf232 → LeafState232
preferredCommonRadiusLeafState232 literalUniformCMP116CommonRadius = open
preferredCommonRadiusLeafState232 firstSecondDerivativeUseSameRadius = blocked

preferredFirstCommonRadiusCoordinate232 : PreferredCommonRadiusLeaf232
preferredFirstCommonRadiusCoordinate232 = literalUniformCMP116CommonRadius

commonAnalyticDomainSourceAuthorityLevel : ProofLevel
commonAnalyticDomainSourceAuthorityLevel = Common.cmp116CommonAnalyticDomainSourceLevel

literalUniformCommonRadiusLevel : ProofLevel
literalUniformCommonRadiusLevel = Common.literalCMP116UniformCommonRadiusInstantiationLevel

-- Stronger constructive fallback: extract four normalized finite demands and
-- use the existing canonical rational choice to build a common positive radius.
fourDemandExtractionFallbackLevel : ProofLevel
fourDemandExtractionFallbackLevel = Demands.literalCMP116FiniteNormalizedDemandExtractionLevel

fourDemandsToCommonDomainCompilerLevel : ProofLevel
fourDemandsToCommonDomainCompilerLevel = Bridge.canonicalRadiusToCommonDomainCompilerLevel

round232CommonRadiusPhysicalClosure : Bool
round232CommonRadiusPhysicalClosure = false

round232CommonRadiusPhysicalClosureIsFalse :
  round232CommonRadiusPhysicalClosure ≡ false
round232CommonRadiusPhysicalClosureIsFalse = refl

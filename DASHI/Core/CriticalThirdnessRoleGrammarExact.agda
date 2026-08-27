module DASHI.Core.CriticalThirdnessRoleGrammarExact where

------------------------------------------------------------------------
-- CRITICAL THIRDNESS / OTHERING / GENERATIVE-SPACE ROLE GRAMMARS
--
-- SOURCE CONTEXT
--
-- Simone de Beauvoir, The Second Sex, original French 1949; Vintage 2011
-- English edition, ISBN 9780307277787.
-- Gloria Anzaldua, Borderlands / La Frontera: The New Mestiza, Aunt Lute
-- Books, 1987, ISBN 9781879960138.
-- Homi K. Bhabha, The Location of Culture, Routledge, 1994,
-- ISBN 9780415016353.
--
-- These sources motivate distinct relational readings.  The finite directed
-- graphs below are DASHI reconstructions; none is attributed to an author as a
-- published graph theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.RelationalRoleGrammarExact as Grammar

------------------------------------------------------------------------
-- Beauvoir: binary One/Other asymmetry, not a ternary chart.
------------------------------------------------------------------------

data BeauvoirPosition : Set where
  onePosition otherPosition : BeauvoirPosition

data BeauvoirRole : Set where
  selfGroundedSubject relationalOther : BeauvoirRole

beauvoirRole : BeauvoirPosition → BeauvoirRole
beauvoirRole onePosition = selfGroundedSubject
beauvoirRole otherPosition = relationalOther

beauvoirOtheringEdge : BeauvoirPosition → BeauvoirPosition → Bool
beauvoirOtheringEdge onePosition otherPosition = true
beauvoirOtheringEdge _ _ = false

oneConstitutesOther : beauvoirOtheringEdge onePosition otherPosition ≡ true
oneConstitutesOther = refl

otherDoesNotSymmetricallyConstituteOne :
  beauvoirOtheringEdge otherPosition onePosition ≡ false
otherDoesNotSymmetricallyConstituteOne = refl

------------------------------------------------------------------------
-- Anzaldua: a positively inhabitable border/interstitial role.
--
-- code0 is a DASHI address for the border/mestiza role.  The source does not
-- number mestiza consciousness as zero, one or two.
------------------------------------------------------------------------

data AnzalduaRole : Set where
  borderMestizaPosition inheritedPoleA inheritedPoleB : AnzalduaRole

anzalduaRole : Ternary.TernaryRoleCode → AnzalduaRole
anzalduaRole Ternary.code0 = borderMestizaPosition
anzalduaRole Ternary.code1 = inheritedPoleA
anzalduaRole Ternary.code2 = inheritedPoleB

anzalduaPluralEdge :
  Ternary.TernaryRoleCode → Ternary.TernaryRoleCode → Bool
anzalduaPluralEdge Ternary.code0 Ternary.code1 = true
anzalduaPluralEdge Ternary.code0 Ternary.code2 = true
anzalduaPluralEdge Ternary.code1 Ternary.code0 = true
anzalduaPluralEdge Ternary.code2 Ternary.code0 = true
anzalduaPluralEdge _ _ = false

borderRelatesToFirstPole : anzalduaPluralEdge Ternary.code0 Ternary.code1 ≡ true
borderRelatesToFirstPole = refl

borderRelatesToSecondPole : anzalduaPluralEdge Ternary.code0 Ternary.code2 ≡ true
borderRelatesToSecondPole = refl

------------------------------------------------------------------------
-- Bhabha: Third Space is represented by a generative-direction graph.
--
-- code0 is again only a DASHI address.  The graph records the bounded reading
-- that the Third Space destabilizes pure-origin priority rather than being a
-- simple result of two independently pure endpoints.
------------------------------------------------------------------------

data BhabhaRole : Set where
  thirdSpace retroactiveOriginA retroactiveOriginB : BhabhaRole

bhabhaRole : Ternary.TernaryRoleCode → BhabhaRole
bhabhaRole Ternary.code0 = thirdSpace
bhabhaRole Ternary.code1 = retroactiveOriginA
bhabhaRole Ternary.code2 = retroactiveOriginB

bhabhaGenerativeEdge :
  Ternary.TernaryRoleCode → Ternary.TernaryRoleCode → Bool
bhabhaGenerativeEdge Ternary.code0 Ternary.code1 = true
bhabhaGenerativeEdge Ternary.code0 Ternary.code2 = true
bhabhaGenerativeEdge _ _ = false

thirdGeneratesFirstOriginRole :
  bhabhaGenerativeEdge Ternary.code0 Ternary.code1 ≡ true
thirdGeneratesFirstOriginRole = refl

firstOriginDoesNotGenerateThird :
  bhabhaGenerativeEdge Ternary.code1 Ternary.code0 ≡ false
firstOriginDoesNotGenerateThird = refl

------------------------------------------------------------------------
-- Exact grammar differences on the same ternary carrier.
------------------------------------------------------------------------

anzaldua≠bhabhaGrammar :
  Grammar.GrammarDifferenceWitness anzalduaPluralEdge bhabhaGenerativeEdge
anzaldua≠bhabhaGrammar =
  Grammar.grammar-difference-witness
    Ternary.code1 Ternary.code0 (λ ())

record CriticalThirdnessBoundary : Set where
  constructor critical-thirdness-boundary
  field
    beauvoirBinaryIsTernaryByDefinition : Bool
    beauvoirBinaryIsTernaryByDefinitionIsFalse :
      beauvoirBinaryIsTernaryByDefinition ≡ false
    anzalduaBorderPositionMeansNumericZero : Bool
    anzalduaBorderPositionMeansNumericZeroIsFalse :
      anzalduaBorderPositionMeansNumericZero ≡ false
    bhabhaThirdSpaceMeansThirdAfterTwoPureOrigins : Bool
    bhabhaThirdSpaceMeansThirdAfterTwoPureOriginsIsFalse :
      bhabhaThirdSpaceMeansThirdAfterTwoPureOrigins ≡ false
    sameThirdSpaceVocabularyImpliesSameGrammar : Bool
    sameThirdSpaceVocabularyImpliesSameGrammarIsFalse :
      sameThirdSpaceVocabularyImpliesSameGrammar ≡ false
    finiteGraphsExhaustHistoricalTheories : Bool
    finiteGraphsExhaustHistoricalTheoriesIsFalse :
      finiteGraphsExhaustHistoricalTheories ≡ false

canonicalCriticalThirdnessBoundary : CriticalThirdnessBoundary
canonicalCriticalThirdnessBoundary =
  critical-thirdness-boundary
    false refl false refl false refl false refl false refl

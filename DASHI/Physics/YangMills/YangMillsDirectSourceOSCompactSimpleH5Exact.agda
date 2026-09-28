{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSCompactSimpleH5Exact where

------------------------------------------------------------------------
-- H5 SOURCE-FIRST: EVERY COMPACT SIMPLE G GETS THE SAME H1/H2/H3 PACKAGE.
--
-- Classification/package lookup is already compiler-owned.  The physical H5
-- theorem is one parametric continuation from QuantitativeCompactLiePackage G
-- to the actual direct-source construction used by the mass-gap proof.
--
-- To prevent a parallel group universe, this owner also carries an exact
-- roundtrip between the repository's classified CompactSimpleLieGroup and the
-- literal endpoint CompactSimpleGroup carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Compact
import DASHI.Physics.YangMills.YangMillsCompactSimpleParametricPromotionReductionExact as Groups
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSameHGapExact as H1H3
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSelectedWilsonH2Exact as H2
import DASHI.Physics.YangMills.YangMillsDirectSourceOSReconstructedSpectrumH3Exact as H3

record LiteralGroupDirectSourcePackage
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (G : Top.CompactSimpleGroup C)
    : Set₂ where
  field
    h1h3 :
      H1H3.LiteralGroupDirectSourceSameHGap Y G

    h2SelectedWilson :
      H2.LiteralSelectedWilsonExpectationApplication h1h3

    h3SameOS :
      H3.LiteralSelectedSpectrumIsSameOSHamiltonian h1h3

open LiteralGroupDirectSourcePackage public

record LiteralCompactSimpleDirectSourceContinuation
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    : Set₂ where
  field
    LieElement GroupElement : Set

    authority :
      Compact.CompactSimpleQuantitativeAuthority
        ℚ LieElement GroupElement

    classifiedToLiteral :
      Compact.CompactSimpleLieGroup →
      Top.CompactSimpleGroup C

    literalToClassified :
      Top.CompactSimpleGroup C →
      Compact.CompactSimpleLieGroup

    classifiedLiteralRoundtrip :
      ∀ G →
      classifiedToLiteral (literalToClassified G) ≡ G

    continueLiteralDirectSource :
      (G : Compact.CompactSimpleLieGroup) →
      Compact.QuantitativeCompactLiePackage
        ℚ LieElement GroupElement G →
      LiteralGroupDirectSourcePackage
        Y (classifiedToLiteral G)

open LiteralCompactSimpleDirectSourceContinuation public

asParametricContinuation :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  (source : LiteralCompactSimpleDirectSourceContinuation Y) →
  Groups.CompactSimpleParametricYMContinuation
    ℚ (LieElement source) (GroupElement source)
asParametricContinuation {Y = Y} source = record
  { Groups.CompactSimpleParametricYMContinuation.authority =
      authority source
  ; Groups.CompactSimpleParametricYMContinuation.PhysicalConstruction =
      λ G →
        LiteralGroupDirectSourcePackage
          Y (classifiedToLiteral source G)
  ; Groups.CompactSimpleParametricYMContinuation.continueFromQuantitativePackage =
      continueLiteralDirectSource source
  }

classifiedConstruction :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : LiteralCompactSimpleDirectSourceContinuation Y)
    G →
  LiteralGroupDirectSourcePackage
    Y (classifiedToLiteral source G)
classifiedConstruction source G =
  Groups.allCompactSimpleConstruction
    (asParametricContinuation source) G

constructionForEveryLiteralCompactSimpleGroup :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : LiteralCompactSimpleDirectSourceContinuation Y)
    G →
  LiteralGroupDirectSourcePackage Y G
constructionForEveryLiteralCompactSimpleGroup {Y = Y} source G =
  subst
    (LiteralGroupDirectSourcePackage Y)
    (classifiedLiteralRoundtrip source G)
    (classifiedConstruction source (literalToClassified source G))

sameHGapForEveryLiteralGroup :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralCompactSimpleDirectSourceContinuation Y →
  H1H3.LiteralDirectSourceSameHMassGap Y
sameHGapForEveryLiteralGroup source = record
  { H1H3.LiteralDirectSourceSameHMassGap.forGroup =
      λ G →
        h1h3
          (constructionForEveryLiteralCompactSimpleGroup source G)
  }

h2ForEveryLiteralGroup :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : LiteralCompactSimpleDirectSourceContinuation Y)
    G →
  H2.LiteralSelectedWilsonExpectationApplication
    (H1H3.forGroup (sameHGapForEveryLiteralGroup source) G)
h2ForEveryLiteralGroup source G =
  h2SelectedWilson
    (constructionForEveryLiteralCompactSimpleGroup source G)

h3ForEveryLiteralGroup :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : LiteralCompactSimpleDirectSourceContinuation Y)
    G →
  H3.LiteralSelectedSpectrumIsSameOSHamiltonian
    (H1H3.forGroup (sameHGapForEveryLiteralGroup source) G)
h3ForEveryLiteralGroup source G =
  h3SameOS
    (constructionForEveryLiteralCompactSimpleGroup source G)

directH5ClassificationCompilerLevel : ProofLevel
directH5ClassificationCompilerLevel =
  Groups.compactSimpleClassificationToParametricFamilyLevel

-- The single remaining H5 physical theorem is continueLiteralDirectSource:
-- construct the literal selected-background/CMP116/continuum/spectral package
-- from QuantitativeCompactLiePackage G for arbitrary classified G.
directH5PhysicalParametricContinuationLevel : ProofLevel
directH5PhysicalParametricContinuationLevel = conditional

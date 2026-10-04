{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyLateCutoffB1B2JointWitnessExact where

------------------------------------------------------------------------
-- JOINT B1/B2 CUTOFF COMPILER.
--
-- Once B1 is proved uniformly on the actual selected finite sequence, B2 is
-- allowed to choose a sufficiently late cutoff from dyadic tail decay.  This
-- module packages the SAME chosen cutoff with:
--
--   * the direct R136 <= finite-R144 + tail B1 anchor, and
--   * the B2 coefficient margin base + tail < ceiling.
--
-- Hence cutoff coordination is compiler-owned.  No hand-selected k remains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _<_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyB1SelectedSameSequenceMaxCutExact as B1
import DASHI.Physics.Foundations.CMP119CosmologyB2StrictSourceGapEventuallyPaysTailExact as B2
import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as Direct
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

module _
    {Configuration : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient : Quotient.RealQuotientConvergenceAuthority
      (RealLimit.Converges sequenceLimit)}
    {division : Division.RealDivisionAlgebra
      (RealLimit.canonicalCylinderAlgebra limitLaws) quotient}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    (source : R109.SourceNativeStressScaleCauchy)
    (observable : Configuration → ℝ)
    (embedding : Additive.OrderedAdditiveRationalRealEmbedding)
  where

  module Same = B1 family source observable embedding

  record LateCutoffB1B2Witness
      (completed : ℚ)
      (finiteRationalDGamma : Nat → ℚ)
      (base ceiling : ℚ) : Set₁ where
    field
      cutoff : Nat

      b1Anchor :
        Direct.DirectR144R109TailAnchor
          embedding source completed (finiteRationalDGamma cutoff) cutoff

      b2CoefficientMargin :
        base + Tail.r109RemainingTail source cutoff < ceiling

  open LateCutoffB1B2Witness public

  compileLateCutoffB1B2Witness :
    (limitOrder : B1.RealTailLimitOrderAuthority sequenceLimit) →
    (tailDecay : B2.R109TailEventuallyFitsStrictGap source) →
    ∀ {completed finiteRationalDGamma base ceiling} →
    Same.SelectedR109SameSequenceCompletion completed →
    Same.AllCutoffR144FiniteExpectationAttachment finiteRationalDGamma →
    base < ceiling →
    LateCutoffB1B2Witness completed finiteRationalDGamma base ceiling
  compileLateCutoffB1B2Witness
      limitOrder tailDecay sameSequence finiteAttachment strictGap =
    let
      chosen = B2.strictSourceGapEventuallyPaysQuantitativeB2
        source tailDecay strictGap
      k = proj₁ chosen
      margin = proj₂ chosen
    in record
      { LateCutoffB1B2Witness.cutoff = k
      ; LateCutoffB1B2Witness.b1Anchor =
          Same.directAnchorAtAnyCutoff
            limitOrder sameSequence finiteAttachment k
      ; LateCutoffB1B2Witness.b2CoefficientMargin = margin
      }

lateCutoffSelectionIsCompilerOwned : Bool
lateCutoffSelectionIsCompilerOwned = true

b1AndB2UseSameChosenCutoff : Bool
b1AndB2UseSameChosenCutoff = true

noHandSelectedCutoffRequired : Bool
noHandSelectedCutoffRequired = true

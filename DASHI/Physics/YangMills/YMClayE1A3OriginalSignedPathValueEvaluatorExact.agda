module DASHI.Physics.YangMills.YMClayE1A3OriginalSignedPathValueEvaluatorExact where

------------------------------------------------------------------------
-- E1/A3 direct, finite-valued original signed-path evaluator.
--
-- Every sampled coordinate below is an ACTUAL original positive Wilson
-- link variable; negative path steps use the original predecessor
-- positive link and apply group inverse at the evaluation site.
--
-- Unlike a quotient/extensional-factorisation lemma, this constructs
-- the finite-tuple evaluator and proves it computes the original
-- nonabelian holonomy and real-valued SU(N) Wilson word.
--
-- No limit, RG comparison, projective measure, OS gap or nontrivial
-- continuum claim is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality using (cong₂)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 1ℝ; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Rooted
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClayD1OriginalWilsonPathSupportExtensionalExact as Source
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words

data SignedPositiveLinkValues (Value : Set)
    : List Rooted.SignedAxis4 → Set where
  valuesStop : SignedPositiveLinkValues Value []
  valuesStep :
    ∀ {direction directions} →
    Value → SignedPositiveLinkValues Value directions →
    SignedPositiveLinkValues Value (direction ∷ directions)

-- The *value* in a negative direction remains a sampled original
-- positive link. Inversion is a property of the oriented evaluator.
orientSample :
  ∀ {Value : Set} (group : Bond.ExactLinkGroup Value) →
  Rooted.SignedAxis4 → Value → Value
orientSample group (Torus.pair axis true) value = value
orientSample group (Torus.pair axis false) value =
  Bond.inverse group value

sampleOriginalSignedPath :
  ∀ {n : Nat} {Value : Set} {group : Bond.ExactLinkGroup Value} →
  (realization : Bond.PeriodicBondGaugeRealization n Value group) →
  (site : Blocks.PeriodicBlock n) →
  (directions : List Rooted.SignedAxis4) →
  SignedPositiveLinkValues Value directions
sampleOriginalSignedPath realization site [] = valuesStop
sampleOriginalSignedPath realization site (direction ∷ directions) =
  valuesStep
    (Bond.bondField realization
      (Source.sourceBondAtSignedStep site direction))
    (sampleOriginalSignedPath realization
      (Bond.walkStep site direction) directions)

evaluateOriginalSignedPath :
  ∀ {Value : Set} (group : Bond.ExactLinkGroup Value) →
  (directions : List Rooted.SignedAxis4) →
  SignedPositiveLinkValues Value directions → Value
evaluateOriginalSignedPath group [] valuesStop =
  Bond.identity group
evaluateOriginalSignedPath group (direction ∷ directions)
    (valuesStep value tail) =
  Bond.multiply group
    (orientSample group direction value)
    (evaluateOriginalSignedPath group directions tail)

-- This proof is on the original positive-bond lookup interpreter,
-- including the negative predecessor source variable, not on an
-- independently selected path or arbitrary finite test.
sampledOriginalSignedPathComputesHolonomy :
  ∀ {n : Nat} {Value : Set} {group : Bond.ExactLinkGroup Value} →
  (realization : Bond.PeriodicBondGaugeRealization n Value group) →
  (site : Blocks.PeriodicBlock n) →
  (directions : List Rooted.SignedAxis4) →
  evaluateOriginalSignedPath group directions
    (sampleOriginalSignedPath realization site directions)
  ≡ Bond.pathHolonomy realization site directions
sampledOriginalSignedPathComputesHolonomy realization site [] = refl
sampledOriginalSignedPathComputesHolonomy {group = group}
    realization site ((Torus.pair axis true) ∷ directions) =
  cong₂ (Bond.multiply group) refl
    (sampledOriginalSignedPathComputesHolonomy
      realization
      (Bond.walkStep site (Torus.pair axis true))
      directions)
sampledOriginalSignedPathComputesHolonomy {group = group}
    realization site ((Torus.pair axis false) ∷ directions) =
  cong₂ (Bond.multiply group) refl
    (sampledOriginalSignedPathComputesHolonomy
      realization
      (Bond.walkStep site (Torus.pair axis false))
      directions)

data OriginalWordPositiveLinkValues
    {n : Nat} (Value : Set)
    : List (Plaquette.PeriodicPlaquette n) → Set where
  wordValuesStop :
    OriginalWordPositiveLinkValues Value []
  wordValuesStep :
    ∀ {p ps} →
    SignedPositiveLinkValues Value
      (Bond.plaquetteBoundaryDirections (Torus.second p)) →
    OriginalWordPositiveLinkValues Value ps →
    OriginalWordPositiveLinkValues Value (p ∷ ps)

sampleOriginalWilsonWord :
  ∀ {n : Nat} {Value : Set} {group : Bond.ExactLinkGroup Value} →
  (realization : Bond.PeriodicBondGaugeRealization n Value group) →
  (word : List (Plaquette.PeriodicPlaquette n)) →
  OriginalWordPositiveLinkValues Value word
sampleOriginalWilsonWord realization [] = wordValuesStop
sampleOriginalWilsonWord realization (p ∷ ps) =
  wordValuesStep
    (sampleOriginalSignedPath realization
      (Torus.first p)
      (Bond.plaquetteBoundaryDirections (Torus.second p)))
    (sampleOriginalWilsonWord realization ps)

evaluateOriginalWilsonWord :
  ∀ {n : Nat} {Value : Set}
    (group : Bond.ExactLinkGroup Value)
    (classValue : Value → ℝ)
    (word : List (Plaquette.PeriodicPlaquette n)) →
  OriginalWordPositiveLinkValues Value word → ℝ
evaluateOriginalWilsonWord group classValue [] wordValuesStop = 1ℝ
evaluateOriginalWilsonWord group classValue (p ∷ ps)
    (wordValuesStep values tail) =
  classValue
    (evaluateOriginalSignedPath group
      (Bond.plaquetteBoundaryDirections (Torus.second p))
      values)
  *ℝ evaluateOriginalWilsonWord group classValue ps tail

-- Independent of the analytic Haar/partition arguments: this is the
-- same original nonabelian Wilson *integrand* at each finite cutoff.
module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  originalWilsonRealization :
    (n : Nat) (links : Variable.SUNPeriodicLinks theory n) →
    Bond.PeriodicBondGaugeRealization n
      (SUN.SUNMatrixElement theory)
      (Variable.Native.sunExactSignedLinkGroup theory)
  originalWilsonRealization n links =
    Variable.periodicSUNRealization theory n links
      (λ _ → SUN.sunIdentity theory)

  originalWilsonWordSampledValues :
    (n : Nat) (word : List (Plaquette.PeriodicPlaquette n))
    (links : Variable.SUNPeriodicLinks theory n) →
    OriginalWordPositiveLinkValues (SUN.SUNMatrixElement theory) word
  originalWilsonWordSampledValues n word links =
    sampleOriginalWilsonWord (originalWilsonRealization n links) word

  originalWilsonWordDirectFiniteEvaluation :
    (n : Nat) (word : List (Plaquette.PeriodicPlaquette n))
    (links : Variable.SUNPeriodicLinks theory n) →
    evaluateOriginalWilsonWord
      (Variable.Native.sunExactSignedLinkGroup theory)
      (Trace.matrixWilsonValue traceData)
      word
      (originalWilsonWordSampledValues n word links)
    ≡
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide
      n word links
  originalWilsonWordDirectFiniteEvaluation n [] links = refl
  originalWilsonWordDirectFiniteEvaluation n (p ∷ ps) links =
    cong₂ _*ℝ_
      (cong (Trace.matrixWilsonValue traceData)
        (sampledOriginalSignedPathComputesHolonomy
          (originalWilsonRealization n links)
          (Torus.first p)
          (Bond.plaquetteBoundaryDirections (Torus.second p))))
      (originalWilsonWordDirectFiniteEvaluation n ps links)

module DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact where

-- Original changing-cutoff SU(N) Wilson finite plaquette-word compiler.
-- Genuine original real Gibbs/Haar source; no new measure or scalar.
-- Formal mixed-J coefficient is NOT analytic CMP116 differentiation.
-- No uniform decay or continuum convergence is asserted.

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 1ℝ; _*ℝ_; _-ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayD1OriginalPeriodicPlaquetteFourBondSupportExact as FourBond
import DASHI.Physics.YangMills.YMClayD1OriginalPlaquetteSupportDecisionExact as DisjointSupport
import DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact as Wilson
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Jet
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

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

  PlaquetteWord : Nat → Set
  PlaquetteWord n = List (Plaquette.PeriodicPlaquette n)


  -- SOURCE EXACT: every literal original Wilson word carries its
  -- original four-positive-bond plaquette dependency lists. No
  -- alternative geometry or synthetic observables are constructed.
  originalWordPositiveBondSupports :
    (n : Nat) → PlaquetteWord n →
    List (List (Torus.PositiveBond (suc n)))
  originalWordPositiveBondSupports n [] = []
  originalWordPositiveBondSupports n (p ∷ rest) =
    FourBond.originalFourPositiveBonds p ∷
    originalWordPositiveBondSupports n rest

  data EveryOriginalPlaquetteHasFour {A : Set} :
    List (List A) → Set where
    emptySupport : EveryOriginalPlaquetteHasFour []
    appendFour :
      ∀ {head tail} →
      FourBond.length head ≡ 4 →
      EveryOriginalPlaquetteHasFour tail →
      EveryOriginalPlaquetteHasFour (head ∷ tail)

  originalWordAllPositiveBondSupportsHaveFour :
    (n : Nat) (word : PlaquetteWord n) →
    EveryOriginalPlaquetteHasFour
      (originalWordPositiveBondSupports n word)
  originalWordAllPositiveBondSupportsHaveFour n [] = emptySupport
  originalWordAllPositiveBondSupportsHaveFour n (p ∷ rest) =
    appendFour (FourBond.originalPlaquetteReadsExactlyFourBondSlots p)
      (originalWordAllPositiveBondSupportsHaveFour n rest)


  -- This native original two-plaquette decision procedure returns an
  -- actual PROOF of disjoint positive-bond support when successful.
  -- It is a dependency on the SAME native Wilson source, not a
  -- new synthetic link graph or assumed independence condition.
  originalPlaquettesHaveDisjointLinkSupports :
    (n : Nat) (left right : Plaquette.PeriodicPlaquette n) →
    Torus.Dec (DisjointSupport.OriginalPlaquettesDisjoint left right)
  originalPlaquettesHaveDisjointLinkSupports n left right =
    DisjointSupport.decideOriginalPlaquettesDisjoint left right

  originalWordObservable :
    (n : Nat) → PlaquetteWord n →
    Wilson.Test theory traceData exponential beta oneLink bilateral divide n
  originalWordObservable n [] links = 1ℝ
  originalWordObservable n (p ∷ rest) links =
    Wilson.originalLocalPlaquetteTraceAt
      theory traceData exponential beta oneLink bilateral divide n p links
    *ℝ originalWordObservable n rest links

  originalAllLengthWordsAreGaugeInvariant :
    (n : Nat) (word : PlaquetteWord n) →
    Wilson.originalGaugeInvariant
      theory traceData exponential beta oneLink bilateral divide n
      (originalWordObservable n word)
  originalAllLengthWordsAreGaugeInvariant n [] gamma links = refl
  originalAllLengthWordsAreGaugeInvariant n (p ∷ rest) =
    Wilson.originalGaugeInvariantProduct
      theory traceData exponential beta oneLink bilateral divide n
      (Wilson.originalLocalPlaquetteTraceAt
        theory traceData exponential beta oneLink bilateral divide n p)
      (originalWordObservable n rest)
      (Wilson.originalLocalPlaquetteTraceAtGaugeInvariant
        theory traceData exponential beta oneLink bilateral divide n p)
      (originalAllLengthWordsAreGaugeInvariant n rest)

  OriginalChangingWord : Set
  OriginalChangingWord = (n : Nat) → PlaquetteWord n

  originalChangingWordSection :
    OriginalChangingWord →
    Wilson.OriginalCylinderSection
      theory traceData exponential beta oneLink bilateral divide
  originalChangingWordSection selection n =
    originalWordObservable n (selection n)

  originalChangingWordGaugeInvariant :
    (selection : OriginalChangingWord) →
    Wilson.OriginalGaugeInvariantSection
      theory traceData exponential beta oneLink bilateral divide
      (originalChangingWordSection selection)
  originalChangingWordGaugeInvariant selection n =
    originalAllLengthWordsAreGaugeInvariant n (selection n)

  originalAllLengthWordE1D1CovarianceIdentity :
    (left right : OriginalChangingWord) (n : Nat) →
    Wilson.originalWilsonConnectedCovariance
      theory traceData exponential beta oneLink bilateral divide n
      (originalWordObservable n (left n))
      (originalWordObservable n (right n))
    ≡
    Wilson.actualE1CylinderExpectation
      theory traceData exponential beta oneLink bilateral divide n
      (λ cutoff links →
        originalWordObservable cutoff (left cutoff) links
        *ℝ originalWordObservable cutoff (right cutoff) links)
    -ℝ
    (Wilson.actualE1CylinderExpectation
      theory traceData exponential beta oneLink bilateral divide n
      (originalChangingWordSection left)
     *ℝ
     Wilson.actualE1CylinderExpectation
      theory traceData exponential beta oneLink bilateral divide n
      (originalChangingWordSection right))
  originalAllLengthWordE1D1CovarianceIdentity left right n =
    Wilson.actualE1D1SameWilsonConnectedCovariance
      theory traceData exponential beta oneLink bilateral divide n
      (originalChangingWordSection left)
      (originalChangingWordSection right)

  originalAllLengthWordMixedJetIsD1Covariance :
    (n : Nat) (left right : PlaquetteWord n) →
    Cumulant.literalMixedSecondLogDerivative
      (Jet.originalWilsonLiteralJetDirections
        theory traceData exponential beta oneLink bilateral divide n)
      (Cumulant.sourceDirectionOf
        (Jet.originalWilsonLiteralJetDirections
          theory traceData exponential beta oneLink bilateral divide n)
        (originalWordObservable n left))
      (Cumulant.sourceDirectionOf
        (Jet.originalWilsonLiteralJetDirections
          theory traceData exponential beta oneLink bilateral divide n)
        (originalWordObservable n right))
    ≡
    Wilson.originalWilsonConnectedCovariance
      theory traceData exponential beta oneLink bilateral divide n
      (originalWordObservable n left)
      (originalWordObservable n right)
  originalAllLengthWordMixedJetIsD1Covariance n left right =
    Jet.originalWilsonMixedJetIsSameFiniteCovariance
      theory traceData exponential beta oneLink bilateral divide n
      (originalWordObservable n left)
      (originalWordObservable n right)

-- All-length finite original-source identities, not Clay E1/D1
-- analytic limit / full small-large CMP116 / OS spectral theorem.

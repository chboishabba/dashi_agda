module DASHI.Physics.YangMills.YMClayE1A3OriginalFiniteCoordinateProjectionExact where

------------------------------------------------------------------------
-- ORIGINAL E1/A3 FINITE LINK-COORDINATE FACTORIZATION.
--
-- Unlike a projection whose "finite coordinate" is a full field, the
-- source map below returns a literal finite LIST of group values,
-- indexed by the ACTUAL positive bonds read by signed Wilson paths.
--
-- Proof: equality of the projected values implies equality of every
-- original bond field entry on that finite list; the existing exact
-- original Wilson all-word extensional theorem then establishes
-- equality of the real Wilson word. No functional extensionality,
-- postulate, projective-measure assumption or density argument.
--
-- Unpaid: embedding these actual finite value projections into the
-- independently selected continuum projective coordinate system,
-- original Wilson projective consistency, continuum/OS limit.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClayE1A3OriginalAllWordPathSupportExtensionalExact as Support
import DASHI.Physics.YangMills.YMClayD1OriginalWilsonPathSupportExtensionalExact as Path
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words

-- Elementary injectivity of list constructors; no equality axioms.
consHeadInjective :
  ∀ {A : Set} {x y : A} {xs ys : List A} →
  x ∷ xs ≡ y ∷ ys → x ≡ y
consHeadInjective refl = refl

consTailInjective :
  ∀ {A : Set} {x y : A} {xs ys : List A} →
  x ∷ xs ≡ y ∷ ys → xs ≡ ys
consTailInjective refl = refl

-- An actual finite list of sampled link values, never a complete field
-- masquerading as a finite coordinate.
originalNativeFiniteBondValues :
  ∀ {n : Nat} {Value : Set} →
  List (Torus.PositiveBond (suc n)) →
  (Torus.PositiveBond (suc n) → Value) →
  List Value
originalNativeFiniteBondValues [] field = []
originalNativeFiniteBondValues (bond ∷ bonds) field =
  field bond ∷ originalNativeFiniteBondValues bonds field

-- Exact finite-coordinate reflection lemma. The proof checks all
-- repeated input bonds too; distinctness of the support is unnecessary.
sameOriginalFiniteBondValuesImpliesPointwiseAgreement :
  ∀ {n : Nat} {Value : Set}
    (bonds : List (Torus.PositiveBond (suc n)))
    (left right : Torus.PositiveBond (suc n) → Value) →
  originalNativeFiniteBondValues bonds left
    ≡ originalNativeFiniteBondValues bonds right →
  ∀ bond → Torus._∈_ bond bonds → left bond ≡ right bond
sameOriginalFiniteBondValuesImpliesPointwiseAgreement []
  left right same bond ()
sameOriginalFiniteBondValuesImpliesPointwiseAgreement
  (head ∷ tail) left right same .head Torus.here =
  consHeadInjective same
sameOriginalFiniteBondValuesImpliesPointwiseAgreement
  (head ∷ tail) left right same bond (Torus.there member) =
  sameOriginalFiniteBondValuesImpliesPointwiseAgreement
    tail left right (consTailInjective same) bond member


-- Restriction of an actual link field to a concatenated source-support
-- list commutes with concatenation of the finite coordinate values.
-- This is an actual finite-coordinate compatibility theorem and does
-- not assume probability-measure projective consistency.
originalFiniteValuesAppend :
  ∀ {n : Nat} {Value : Set}
    (left right : List (Torus.PositiveBond (suc n)))
    (field : Torus.PositiveBond (suc n) → Value) →
  originalNativeFiniteBondValues
    (Support.appendSource left right) field
  ≡ Support.appendSource
      (originalNativeFiniteBondValues left field)
      (originalNativeFiniteBondValues right field)
originalFiniteValuesAppend [] right field = refl
originalFiniteValuesAppend (head ∷ rest) right field =
  cong (λ tail → field head ∷ tail)
    (originalFiniteValuesAppend rest right field)

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

  -- Real, finite, group-valued original Wilson projection for each
  -- arbitrary-length original plaquette word at each actual cutoff.
  originalWilsonWordFiniteValues :
    (n : Nat) →
    List (Plaquette.PeriodicPlaquette n) →
    Variable.SUNPeriodicLinks theory n →
    List (SUN.SUNMatrixElement theory)
  originalWilsonWordFiniteValues n word links =
    originalNativeFiniteBondValues
      (Support.originalWordActualFlatPositiveBondSupport word) links

  originalWilsonWordFactorsThroughActualFiniteValues :
    (n : Nat) (word : List (Plaquette.PeriodicPlaquette n))
    (left right : Variable.SUNPeriodicLinks theory n) →
    originalWilsonWordFiniteValues n word left
      ≡ originalWilsonWordFiniteValues n word right →
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide
      n word left
    ≡
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide
      n word right
  originalWilsonWordFactorsThroughActualFiniteValues
    n word left right sameValues =
    Support.originalWordRealSourceExtensional
      theory traceData exponential beta oneLink bilateral divide
      n word left right
      (sameOriginalFiniteBondValuesImpliesPointwiseAgreement
        (Support.originalWordActualFlatPositiveBondSupport word)
        left right sameValues)

  -- This statement identifies exactly the finite projection used.
  -- The number of lookup slots is 4 times the plaquette word length,
  -- as proved in Support.originalWordActualLookupSlotsExactlyFourPerPlaquette.
  -- Periodic identifications may make some slots duplicate coordinates.

  -- For each original word extension, its actual finite projection is
  -- exactly the head-plaquette projection concatenated with the
  -- previously selected tail-word projection. No new chosen projection
  -- or carrier appears at the inductive step.
  originalWilsonWordFiniteCoordinateCons :
    (n : Nat) (p : Plaquette.PeriodicPlaquette n)
    (rest : List (Plaquette.PeriodicPlaquette n))
    (links : Variable.SUNPeriodicLinks theory n) →
    originalWilsonWordFiniteValues n (p ∷ rest) links
    ≡ Support.appendSource
        (originalNativeFiniteBondValues
          (Path.sourcePlaquettePositiveBondSupport p) links)
        (originalWilsonWordFiniteValues n rest links)
  originalWilsonWordFiniteCoordinateCons n p rest links =
    originalFiniteValuesAppend
      (Path.sourcePlaquettePositiveBondSupport p)
      (Support.originalWordActualFlatPositiveBondSupport rest)
      links

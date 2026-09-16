module DASHI.Wikimedia.IbrahimMonster6BPositiveDegreeNormalizationAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster236BMcKayThompsonNormalizationInvariantOEISExact as Normalization
import DASHI.Wikimedia.IbrahimMonster6BWeightTwoC6FourierOEISExact as C6

------------------------------------------------------------------------
-- 6B POSITIVE-DEGREE NORMALIZATION ACQUISITION
--
-- OEIS currently exposes three 6B McKay--Thompson manifestations:
--
--   A007255 : normalized, a(0)=0,
--   A045485 : a(0)=7,
--   A121665 : a(0)=12.
--
-- A007255 explicitly cross-references A045485/A121665 and states that the
-- sequences agree apart from n=0.  All three published value lists therefore
-- expose the same positive-degree prefix
--
--   78, 364, 1365, 4380, 12520, 32772, ...
--
-- This owner acquires that source-bounded normalization invariance through
-- q^6.  It then records the positive bridge signal to the independently
-- derived weight-two C6 Fourier spectrum where m1=m5=32772.
--
-- Neither equality creates a same-object graded piece, a literal selected 6B
-- action, or a spectral projector intertwiner.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Source manifests.
------------------------------------------------------------------------

oeisA007255 : Attribution.AttributedSource
oeisA007255 = Attribution.mkNoDOISource
  "N. J. A. Sloane; OEIS contributors"
  "A007255: McKay-Thompson series of class 6B for Monster"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-16"
  "https://oeis.org/A007255"
  (Attribution.namedSourceKind "integer-sequence database record")
  "normalized 6B series; OEIS explicitly says A045485/A121665 agree apart from n=0; positive-degree coefficients include q^1=78 through q^6=32772"
  Attribution.publicAttribution

oeisA045485 : Attribution.AttributedSource
oeisA045485 = Attribution.mkNoDOISource
  "N. J. A. Sloane; OEIS contributors"
  "A045485: McKay-Thompson series of class 6B for Monster with a(0)=7"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-16"
  "https://oeis.org/A045485"
  (Attribution.namedSourceKind "integer-sequence database record")
  "alternate 6B normalization; positive-degree coefficient list matches A007255 through q^6=32772"
  Attribution.publicAttribution

oeisA121665 : Attribution.AttributedSource
oeisA121665 = Attribution.mkNoDOISource
  "OEIS contributors"
  "A121665: McKay-Thompson series of class 6B for the Monster group with a(0)=12"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-16"
  "https://oeis.org/A121665"
  (Attribution.namedSourceKind "integer-sequence database record")
  "alternate 6B normalization; positive-degree coefficient list matches A007255 through q^6=32772"
  Attribution.publicAttribution

a007255Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA007255
a045485Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA045485
a121665Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA121665

normalizationFamilyBoundary : Normalization.NormalizationInvariantOEISFrontier
normalizationFamilyBoundary = Normalization.currentNormalizationInvariantOEISFrontier

------------------------------------------------------------------------
-- 2. Acquired positive-degree prefix.
------------------------------------------------------------------------

record SixBPositiveDegreeNormalizationAcquisition : Set where
  constructor six-b-positive-degree-normalization-acquisition
  field
    variantCount : Nat
    normalizedOEIS : String
    plusSevenOEIS : String
    plusTwelveOEIS : String
    qOne : Nat
    qTwo : Nat
    qThree : Nat
    qFour : Nat
    qFive : Nat
    qSix : Nat
    positiveDegreeAgreementThroughQSixPaid : Bool
    qZeroNormalizationDependent : Bool
    qSixMatchesC6WeightTwoM1M5 : Bool
    sameMonsterClassRetained : Bool
    sameSourceFamilyRetained : Bool
    positiveBridgeSearchSignal : Bool
    normalizationAgreementCreatesSameObject : Bool
    oeisPositiveDegreeAgreementCreatesLiteralAction : Bool
    qSixEqualityCreatesSpectralProjectorIntertwiner : Bool
    nextResidual : String
open SixBPositiveDegreeNormalizationAcquisition public

currentSixBPositiveDegreeNormalizationAcquisition :
  SixBPositiveDegreeNormalizationAcquisition
currentSixBPositiveDegreeNormalizationAcquisition =
  six-b-positive-degree-normalization-acquisition
    3
    "A007255" "A045485" "A121665"
    78 364 1365 4380 12520 32772
    true true true true true true
    false false false
    "Use normalization-stable q^6=32772 as positive source-bounded bridge evidence to the independently derived C6 weight-two spectrum m1=m5=32772. Next inspect whether a graded-trace/spectral-projector identity, replicability relation, or same selected 6B action explains the equality. Do not infer same-object, literal action, or projector intertwining from OEIS coefficient agreement alone."

------------------------------------------------------------------------
-- 3. Bind the independent C6 spectral side literally.
------------------------------------------------------------------------

c6Spectrum : C6.C6WeightTwoMultiplicitySpectrum
c6Spectrum = C6.canonicalC6WeightTwoMultiplicitySpectrum

c6M1Is32772 : C6.m1 c6Spectrum ≡ qSix currentSixBPositiveDegreeNormalizationAcquisition
c6M1Is32772 = refl

c6M5Is32772 : C6.m5 c6Spectrum ≡ qSix currentSixBPositiveDegreeNormalizationAcquisition
c6M5Is32772 = refl

------------------------------------------------------------------------
-- 4. WrongType firewalls.
------------------------------------------------------------------------

data NormalizationStableCoefficientCreatesSameObject : Set where
data OEISPositiveDegreeAgreementCreatesLiteralAction : Set where
data QSixEqualityCreatesSpectralProjectorIntertwiner : Set where

normalizationStableCoefficientDoesNotCreateSameObject :
  NormalizationStableCoefficientCreatesSameObject → ⊥
normalizationStableCoefficientDoesNotCreateSameObject ()

oeisPositiveDegreeAgreementDoesNotCreateLiteralAction :
  OEISPositiveDegreeAgreementCreatesLiteralAction → ⊥
oeisPositiveDegreeAgreementDoesNotCreateLiteralAction ()

qSixEqualityDoesNotCreateSpectralProjectorIntertwiner :
  QSixEqualityCreatesSpectralProjectorIntertwiner → ⊥
qSixEqualityDoesNotCreateSpectralProjectorIntertwiner ()

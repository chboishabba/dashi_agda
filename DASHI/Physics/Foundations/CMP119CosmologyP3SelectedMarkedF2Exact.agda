{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3SelectedMarkedF2Exact where

------------------------------------------------------------------------
-- S3a MAX-CUT: ONE SELECTED MARKED F^2 SOURCE, NOT A UNIVERSAL FAMILY.
--
-- The anomaly/cosmology route consumes exactly one curvature composite: the
-- selected renormalized F^2 operator.  Requiring a
--
--   CurvaturePolynomial -> SameFamilyMarkedSourceData
--
-- family repays source/Hilbert-modulus work for curvature polynomials unused by
-- this proof.  The minimal physical object is one selected marked source on the
-- completed state, together with gauge/local semantics for its completed
-- composite.  Nuclear continuity then follows from the existing compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked

record SelectedMarkedF2Source
    (CurvaturePolynomial Position : Set)
    (continuityScale : Nuclear.ContinuityScale)
    (CompletedState Composite : Set) : Set₁ where
  field
    fieldStrengthSquarePolynomial : CurvaturePolynomial

    markedF2Source :
      Marked.SameFamilyMarkedSourceData
        continuityScale CompletedState Composite

    GaugeInvariant : Composite → Set
    LocalAt : Composite → Position → Set

    completedF2GaugeInvariant :
      GaugeInvariant
        (Marked.continuumComposite
          (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
            markedF2Source))

    completedF2Local : ∀ position →
      LocalAt
        (Marked.continuumComposite
          (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
            markedF2Source))
        position

open SelectedMarkedF2Source public

selectedF2 :
  ∀ {CurvaturePolynomial Position continuityScale CompletedState Composite} →
  SelectedMarkedF2Source
    CurvaturePolynomial Position continuityScale CompletedState Composite →
  Composite
selectedF2 source =
  Marked.continuumComposite
    (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
      (markedF2Source source))

selectedF2NuclearContinuous :
  ∀ {CurvaturePolynomial Position continuityScale CompletedState Composite}
    (source :
      SelectedMarkedF2Source
        CurvaturePolynomial Position continuityScale CompletedState Composite) →
  Nuclear.ContinuousAtZeroWith continuityScale
    (Marked.nuclearNear (markedF2Source source))
    (Marked.fieldFunctional
      (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
        (markedF2Source source)))
selectedF2NuclearContinuous source =
  Marked.fieldNuclearContinuous
    (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
      (markedF2Source source))

selectedF2GaugeInvariant :
  ∀ {CurvaturePolynomial Position continuityScale CompletedState Composite}
    (source :
      SelectedMarkedF2Source
        CurvaturePolynomial Position continuityScale CompletedState Composite) →
  GaugeInvariant source (selectedF2 source)
selectedF2GaugeInvariant = completedF2GaugeInvariant

selectedF2Local :
  ∀ {CurvaturePolynomial Position continuityScale CompletedState Composite}
    (source :
      SelectedMarkedF2Source
        CurvaturePolynomial Position continuityScale CompletedState Composite)
    position →
  LocalAt source (selectedF2 source) position
selectedF2Local = completedF2Local

universalMarkedCurvatureFamilyRequiredForCosmology : Bool
universalMarkedCurvatureFamilyRequiredForCosmology = false

oneSelectedMarkedF2SourceSuffices : Bool
oneSelectedMarkedF2SourceSuffices = true

remainingSelectedF2SourceWorkIsPhysicalMarkedSourceDataAndSemantics : Bool
remainingSelectedF2SourceWorkIsPhysicalMarkedSourceDataAndSemantics = true

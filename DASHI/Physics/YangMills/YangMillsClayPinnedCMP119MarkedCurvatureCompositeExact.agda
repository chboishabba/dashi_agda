{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact where

------------------------------------------------------------------------
-- C / COMPLETED MARKED SOURCE -> RENORMALIZED CURVATURE COMPOSITE FIELD
--
-- The generic marked-source theorem already turns one same-family completed
-- source derivative with a Hilbertian modulus into a nuclear-continuous field.
-- Specialize that construction to every curvature polynomial and expose the
-- resulting completed composite as the local-operator carrier.
--
-- Gauge invariance and localization remain physical semantic identifications;
-- nuclear completion itself is compiler-owned.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked

record MarkedCurvatureCompositeFamily
    (CurvaturePolynomial Position : Set)
    (continuityScale : Nuclear.ContinuityScale)
    (CompletedState Composite : Set) : Set₁ where
  field
    markedSource :
      CurvaturePolynomial →
      Marked.SameFamilyMarkedSourceData
        continuityScale CompletedState Composite

    GaugeInvariant : Composite → Set
    LocalAt : Composite → Position → Set

    completedCompositeGaugeInvariant :
      ∀ polynomial →
      GaugeInvariant
        (Marked.continuumComposite
          (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
            (markedSource polynomial)))

    completedCompositeLocal :
      ∀ polynomial position →
      LocalAt
        (Marked.continuumComposite
          (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
            (markedSource polynomial)))
        position

open MarkedCurvatureCompositeFamily public

localOperator :
  ∀ {CurvaturePolynomial Position continuityScale CompletedState Composite} →
  MarkedCurvatureCompositeFamily
    CurvaturePolynomial Position continuityScale CompletedState Composite →
  CurvaturePolynomial → Composite
localOperator family polynomial =
  Marked.continuumComposite
    (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
      (markedSource family polynomial))

localOperatorGaugeInvariant :
  ∀ {CurvaturePolynomial Position continuityScale CompletedState Composite}
    (family :
      MarkedCurvatureCompositeFamily
        CurvaturePolynomial Position continuityScale CompletedState Composite)
    polynomial →
  GaugeInvariant family (localOperator family polynomial)
localOperatorGaugeInvariant = completedCompositeGaugeInvariant

localOperatorLocal :
  ∀ {CurvaturePolynomial Position continuityScale CompletedState Composite}
    (family :
      MarkedCurvatureCompositeFamily
        CurvaturePolynomial Position continuityScale CompletedState Composite)
    polynomial position →
  LocalAt family (localOperator family polynomial) position
localOperatorLocal = completedCompositeLocal

localOperatorFieldNuclearContinuous :
  ∀ {CurvaturePolynomial Position continuityScale CompletedState Composite}
    (family :
      MarkedCurvatureCompositeFamily
        CurvaturePolynomial Position continuityScale CompletedState Composite)
    polynomial →
  Nuclear.ContinuousAtZeroWith continuityScale
    (Marked.nuclearNear (markedSource family polynomial))
    (Marked.fieldFunctional
      (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
        (markedSource family polynomial)))
localOperatorFieldNuclearContinuous family polynomial =
  Marked.fieldNuclearContinuous
    (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
      (markedSource family polynomial))

markedCurvatureCompositeNuclearCompilerLevel : ProofLevel
markedCurvatureCompositeNuclearCompilerLevel =
  Marked.markedSourceToNuclearCompositeFieldCompilerLevel

-- C1a is now exactly the physical production of the same-family marked source
-- data (linearity + common Hilbert modulus + completed-state identity), plus
-- gauge/local semantics for the resulting completed curvature composites.
literalMarkedCurvatureCompositeSourceLevel : ProofLevel
literalMarkedCurvatureCompositeSourceLevel = conditional

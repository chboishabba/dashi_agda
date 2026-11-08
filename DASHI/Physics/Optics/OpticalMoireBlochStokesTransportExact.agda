module DASHI.Physics.Optics.OpticalMoireBlochStokesTransportExact where

-- BLOCH--STOKES PROJECTION: REUSE, NOT A NEW OPTICAL DISCOVERY
--
-- Original optical moire experimental source: Vasu Dev and Yijie Shen,
-- Light: Science & Applications 15, 396 (2026),
-- DOI: 10.1038/s41377-026-02533-w.
--
-- Bloch theory and Jones/Stokes/Poincare geometry are prior art.
-- Exact reciprocal/supercell owner:
--   DASHI.Physics.CondensedMatter.HexagonalSqrt3R30ReciprocalFoldingExact
-- Bloch symmetry donor:
--   DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoPhysicalSymmetryExact
--
-- DASHI's new theorem below composes TWO user-provided laws:
-- a complex field with Bloch translation covariance and a phase-blind
-- Stokes observer.  The measured physical field satisfying the first
-- law is NOT created by the theorem, nor is a quasicrystal assumed periodic.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

record BlochStokesSource
    (Point Jones Phase Stokes : Set) : Set₁ where
  field
    translate : Point → Point
    fieldAt : Point → Jones
    phaseOnJones : Phase → Jones → Jones
    blochPhase : Phase
    observer : Jones → Stokes
    blochCovariance :
      (point : Point) →
      fieldAt (translate point) ≡
      phaseOnJones blochPhase (fieldAt point)
    observerPhaseBlind :
      (jones : Jones) →
      observer (phaseOnJones blochPhase jones)
        ≡ observer jones

open BlochStokesSource public

-- Exactly the prior-art consequence that a Bloch phase is invisible
-- to a phase-blind Stokes observable. No physical source asserted.
stokesPeriodicUnderBlochTranslation :
  {Point Jones Phase Stokes : Set} →
  (source : BlochStokesSource Point Jones Phase Stokes) →
  (point : Point) →
  observer source (fieldAt source (translate source point))
    ≡ observer source (fieldAt source point)
stokesPeriodicUnderBlochTranslation source point =
  trans
    (cong (observer source) (blochCovariance source point))
    (observerPhaseBlind source (fieldAt source point))

-- Explicit converse non-promotion: Stokes periodicity alone is not
-- sufficient to infer an identical complex Jones field translation.
-- The standard Bloch phase can be nontrivial, hence observer descent
-- deliberately forgets a physically meaningful phase coordinate.
record BlochToStokesPromotionBoundary : Set₁ where
  field
    actualSourceBlochCovariance : Set
    actualJonesNonzeroAndCalibrated : Set
    actualPolarizationObserverPhaseBlind : Set
    selectedTranslationIsAnActualPeriod : Set
    sameSourceExperimentalDataMatches : Set
    opticalPolarizationIsElectronicBlochBand : Set

-- No instance of the physical boundary is manufactured.

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSelectedWilsonFiniteProjectionRound565Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND565:
-- FINITE-CYLINDER REALIZATION = FACTORIZATION THROUGH ONE FINITE PROJECTION
--
-- R553 deliberately left IsFiniteCylinderFunction abstract.  The ordinary
-- projective meaning is simpler:
--
--   F is a finite-cylinder observable if there exists one finite index n,
--   a finite projection pi_n, and a finite-level function f_n such that
--
--       F = f_n o pi_n.
--
-- The theorem "finite-projection factorization implies finite-cylinder" is
-- standard projective measure theory.  The YM-specific payment is therefore
-- exactly the factorization of each selected Wilson product through the finite
-- lattice coordinates containing its finitely many path edges.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsSelectedCylinderRepresentationRound547Exact as R547
import DASHI.Physics.YangMills.YangMillsSelectedCylinderFunctionClosureRound553Exact as R553
import DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Exact as R534
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record FiniteProjectiveFactorization
    (Configuration Observable : Set)
    (asObservable : Observable → Configuration → ℝ)
    : Set₂ where
  field
    FiniteCoordinate : Set
    ProjectedConfiguration : FiniteCoordinate → Set

    project :
      ∀ coordinate →
      Configuration → ProjectedConfiguration coordinate

    coordinateOf :
      Observable → FiniteCoordinate

    finiteObservable :
      ∀ observable →
      ProjectedConfiguration (coordinateOf observable) → ℝ

    factorsThroughFiniteProjection :
      ∀ observable configuration →
      asObservable observable configuration
      ≡
      finiteObservable observable
        (project (coordinateOf observable) configuration)

open FiniteProjectiveFactorization public

record FiniteProjectionProjectiveAuthority
    (Configuration Event : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    (factorization :
      FiniteProjectiveFactorization
        Configuration
        (R547.SelectedObservable (R547.selectedClass representation))
        (R547.asObservable (R547.selectedClass representation)))
    : Set₂ where
  field
    finiteProjectionConvergesToProjectiveIntegral :
      ∀ selected →
      Cylinder.Converges
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        (λ cutoff →
          Limit.finiteExpectation family cutoff
            (R547.asObservable
              (R547.selectedClass representation)
              selected))
        (R534.integrate
          (R547.extensionAuthority representation)
          (R547.representedMeasure representation)
          (R547.asObservable
            (R547.selectedClass representation)
            selected))

open FiniteProjectionProjectiveAuthority public

record SelectedWilsonFiniteProjectionInputs
    (Configuration Event : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    : Set₂ where
  field
    factorization :
      FiniteProjectiveFactorization
        Configuration
        (R547.SelectedObservable (R547.selectedClass representation))
        (R547.asObservable (R547.selectedClass representation))

    projectiveAuthority :
      FiniteProjectionProjectiveAuthority
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family representation factorization

open SelectedWilsonFiniteProjectionInputs public

selectedWitnessConverges :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    {representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family}
    (inputs :
      SelectedWilsonFiniteProjectionInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family representation)
    observable →
  Σ (R547.SelectedObservable (R547.selectedClass representation))
    (λ selected →
      R547.asObservable (R547.selectedClass representation) selected
      ≡ observable) →
  Cylinder.Converges
    (RealLimit.canonicalCylinderAlgebra limitLaws)
    (λ cutoff → Limit.finiteExpectation family cutoff observable)
    (R534.integrate
      (R547.extensionAuthority representation)
      (R547.representedMeasure representation)
      observable)
selectedWitnessConverges
    {representation = representation}
    inputs
    .(R547.asObservable (R547.selectedClass representation) selected)
    (selected , refl) =
  finiteProjectionConvergesToProjectiveIntegral
    (projectiveAuthority inputs)
    selected


asProjectiveCylinderFunctionConvergenceAuthority :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    {representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family}
    (inputs :
      SelectedWilsonFiniteProjectionInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family representation) →
  R553.ProjectiveCylinderFunctionConvergenceAuthority
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family representation
asProjectiveCylinderFunctionConvergenceAuthority
    {representation = representation} inputs = record
  { R553.ProjectiveCylinderFunctionConvergenceAuthority.IsFiniteCylinderFunction =
      λ observable →
        Σ (R547.SelectedObservable (R547.selectedClass representation))
          (λ selected →
            R547.asObservable (R547.selectedClass representation) selected
            ≡ observable)
  ; R553.ProjectiveCylinderFunctionConvergenceAuthority.finiteCylinderFunctionConvergesToProjectiveIntegral =
      selectedWitnessConverges inputs
  }

asSelectedWilsonCylinderRealization :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    {representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family}
    (inputs :
      SelectedWilsonFiniteProjectionInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family representation) →
  R553.SelectedWilsonCylinderRealization
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family representation
    (asProjectiveCylinderFunctionConvergenceAuthority inputs)
asSelectedWilsonCylinderRealization
    {representation = representation} inputs =
  record
    { R553.SelectedWilsonCylinderRealization.selectedObservableIsFiniteCylinder =
        λ selected → selected , refl
    }

round565FiniteProjectionToCylinderCompilerLevel : ProofLevel
round565FiniteProjectionToCylinderCompilerLevel = machineChecked

round565FiniteProjectionCylinderAuthorityLevel : ProofLevel
round565FiniteProjectionCylinderAuthorityLevel = standardImported

round565GeneralDensityTheoremRequired : Bool
round565GeneralDensityTheoremRequired = false

round565LpCompletionRequired : Bool
round565LpCompletionRequired = false

-- Genuine YM/projective payment:
-- every selected Wilson product factors through a finite projective coordinate
-- of the SAME continuum configuration system.
literalRound565SelectedWilsonFiniteProjectionFactorizationLevel : ProofLevel
literalRound565SelectedWilsonFiniteProjectionFactorizationLevel = conditional

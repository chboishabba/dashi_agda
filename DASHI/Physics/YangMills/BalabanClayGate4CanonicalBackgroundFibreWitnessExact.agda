module DASHI.Physics.YangMills.BalabanClayGate4CanonicalBackgroundFibreWitnessExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3PrincipalFibreCoordinatesExact as Fibre

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Relationship: the physical background map remains an input, but once it is
-- a section of the coarse map, the identity fluctuation is automatically in
-- the nonlinear fibre over every coarse field. This is exact group algebra,
-- not an additional analytic estimate.
------------------------------------------------------------------------

canonicalBackgroundReconstruction :
  ∀ {Coarse Fine Jacobian}
    (dataSet : Fibre.PrincipalFibreCoordinateData Coarse Fine Jacobian)
    coarse →
  Fibre.reconstruct dataSet coarse (Fibre.identity (Fibre.group dataSet))
  ≡ Fibre.backgroundFine dataSet coarse
canonicalBackgroundReconstruction dataSet coarse =
  Fibre.rightIdentity (Fibre.group dataSet)
    (Fibre.backgroundFine dataSet coarse)

identityFluctuationSatisfiesFibreConstraint :
  ∀ {Coarse Fine Jacobian}
    (dataSet : Fibre.PrincipalFibreCoordinateData Coarse Fine Jacobian)
    coarse →
  Fibre.FluctuationConstraint dataSet coarse
    (Fibre.identity (Fibre.group dataSet))
identityFluctuationSatisfiesFibreConstraint dataSet coarse =
  trans
    (cong (Fibre.coarseOf dataSet)
      (canonicalBackgroundReconstruction dataSet coarse))
    (Fibre.backgroundIsSection dataSet coarse)

canonicalBackgroundHasIdentityFluctuation :
  ∀ {Coarse Fine Jacobian}
    (dataSet : Fibre.PrincipalFibreCoordinateData Coarse Fine Jacobian)
    coarse →
  Fibre.fluctuationOf dataSet (Fibre.backgroundFine dataSet coarse)
  ≡ Fibre.identity (Fibre.group dataSet)
canonicalBackgroundHasIdentityFluctuation dataSet coarse =
  subst
    (λ selectedCoarse →
      Fibre.multiply (Fibre.group dataSet)
        (Fibre.inverse (Fibre.group dataSet)
          (Fibre.backgroundFine dataSet selectedCoarse))
        (Fibre.backgroundFine dataSet coarse)
      ≡ Fibre.identity (Fibre.group dataSet))
    (sym (Fibre.backgroundIsSection dataSet coarse))
    (Fibre.leftInverse (Fibre.group dataSet)
      (Fibre.backgroundFine dataSet coarse))

canonicalBackgroundCoordinatesRoundTrip :
  ∀ {Coarse Fine Jacobian}
    (dataSet : Fibre.PrincipalFibreCoordinateData Coarse Fine Jacobian)
    coarse →
  Fibre.reconstruct dataSet
    (Fibre.coarseOf dataSet (Fibre.backgroundFine dataSet coarse))
    (Fibre.fluctuationOf dataSet (Fibre.backgroundFine dataSet coarse))
  ≡ Fibre.backgroundFine dataSet coarse
canonicalBackgroundCoordinatesRoundTrip dataSet coarse =
  Fibre.reconstructs dataSet (Fibre.backgroundFine dataSet coarse)

canonicalBackgroundFibreConstraintLevel : ProofLevel
canonicalBackgroundFibreConstraintLevel = machineChecked

canonicalBackgroundIdentityFluctuationLevel : ProofLevel
canonicalBackgroundIdentityFluctuationLevel = machineChecked

canonicalBackgroundCoordinateRoundTripLevel : ProofLevel
canonicalBackgroundCoordinateRoundTripLevel = machineChecked

physicalBackgroundSectionInstantiationInputsLevel : ProofLevel
physicalBackgroundSectionInstantiationInputsLevel = conditional

physicalIdentityFluctuationChartMembershipInputsLevel : ProofLevel
physicalIdentityFluctuationChartMembershipInputsLevel = conditional

physicalBackgroundSupportGaugeBoundaryInputsLevel : ProofLevel
physicalBackgroundSupportGaugeBoundaryInputsLevel = conditional

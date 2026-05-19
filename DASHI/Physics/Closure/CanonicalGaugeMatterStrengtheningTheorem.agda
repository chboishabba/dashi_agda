module DASHI.Physics.Closure.CanonicalGaugeMatterStrengtheningTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAGMI

------------------------------------------------------------------------
-- Smallest honest strengthening theorem over the canonical gauge/matter
-- bundle. This does not claim full gauge/matter or stronger GR/QFT recovery.
-- It only packages the now-landed stronger payload already present on the
-- canonical bundle:
--
-- * the canonical gauge/matter recovery theorem
-- * the transport-backed natural/coarse-conserved strengthening theorem
-- * the current theorem-bearing continuum witness
--
-- This file exists so downstream known-limits bundles can depend on an
-- explicit stronger canonical gauge/matter payload owner rather than only the
-- thinner matter/gauge wrapper.

record CanonicalGaugeMatterStrengtheningTheorem : Setω where
  field
    canonicalBundle : AGMB.AbstractGaugeMatterBundle
    gaugeMatterRecovery :
      AGMB.GaugeMatterRecoveryTheorem canonicalBundle
    transportBackedNaturalCoarse :
      CAGMI.CanonicalTransportBackedNaturalCoarseTheorem
    strengthenedConserved :
      AGMB.ConservedObservableWitness canonicalBundle
    strengthenedContinuum :
      AGMB.ContinuumWitness canonicalBundle

canonicalGaugeMatterStrengtheningTheorem :
  CanonicalGaugeMatterStrengtheningTheorem
canonicalGaugeMatterStrengtheningTheorem =
  record
    { canonicalBundle = CAGMI.canonicalAbstractGaugeMatterBundle
    ; gaugeMatterRecovery = CAGMI.canonicalGaugeMatterRecoveryTheorem
    ; transportBackedNaturalCoarse =
        CAGMI.canonicalTransportBackedNaturalCoarseTheorem
    ; strengthenedConserved =
        CAGMI.canonicalConservedObservableWitness
    ; strengthenedContinuum =
        CAGMI.canonicalContinuumWitness
    }

module DASHI.Physics.Closure.OSAxiomAvailability where

open import Agda.Builtin.Bool using (Bool; false; true)

-- OS axiom availability record.
-- os1-euclidean-covariance is structurally isolated because its
-- only viable external route is:
--   balabanRGStillOpen → WC1-WC3 → Zenodo-18824739 anisotropy-O(a²)
-- or the Haar-blocking route (Zenodo-19614728).
-- All other axioms have internal proof routes.
record OSAxiomAvailability : Set where
  field
    os0-temperedness          : Bool
    os1-euclidean-covariance  : Bool  -- external authority only
    os2-reflection-positivity : Bool
    os3-permutation-symmetry  : Bool
    os4-cluster-decomposition : Bool

-- The current honest instance: OS0/OS2/OS3/OS4 have internal routes
-- defined (not yet closed); OS1 is permanently false until Balaban closes.
currentOSStatus : OSAxiomAvailability
currentOSStatus = record
  { os0-temperedness          = false  -- route defined, not closed
  ; os1-euclidean-covariance  = false  -- external only, Balaban gate open
  ; os2-reflection-positivity = false  -- route: CM witness, not closed
  ; os3-permutation-symmetry  = false  -- route defined, not closed
  ; os4-cluster-decomposition = false  -- route: exp decay, not closed
  }

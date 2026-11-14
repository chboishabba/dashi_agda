module DASHI.Moonshine.Monster3BFiniteStoneVonNeumannIrreducibilityClosureExact where

------------------------------------------------------------------------
-- CURRENT FINITE STONE--VON NEUMANN IRREDUCIBILITY CLOSURE
--
-- Historical `Monster3BFiniteStoneVonNeumannFrontierExact` still records the
-- earlier open leaf `extractNonzeroCoordinateFromNonzeroVector`.  That leaf is
-- now paid by `Monster3BFiniteSchrodingerNonzeroWitnessExtractionExact`:
--
-- * decidable zero on Q(zeta_3);
-- * a constructive recursive search of TritCube 6 = 3^6 = 729 states;
-- * ordinary pointwise nonzeroness -> a concrete X6 point with nonzero value;
-- * nonzero value -> norm-qualified cyclotomic inverse witness;
-- * the existing delta extraction/orbit/basis route then forces every
--   nonzero Heisenberg-invariant subspace to be the whole Schrodinger module.
--
-- Hence the repo-local Schrodinger irreducibility leaf is CLOSED.  The next
-- genuine Stone--von Neumann seam is fixed-nontrivial-central-character
-- uniqueness, followed by identification/intertwining of the actual Monster
-- degree-729 constituent with this explicit Schrodinger action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerNonzeroWitnessExtractionExact as Witness

------------------------------------------------------------------------
-- 1. Re-export the unconditional irreducibility theorem at the current cut.
------------------------------------------------------------------------

schrodingerIrreducible :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    Witness.OrdinaryNonzeroInvariantVector inv →
    (f : V.SchrodingerFunction) →
    Member f
schrodingerIrreducible = Witness.ordinaryNonzeroInvariantSubspaceIsWholeCarrier

------------------------------------------------------------------------
-- 2. Machine-readable current authority boundary.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    decidableCyclotomicZeroPaid : Bool
    recursiveTritCube729SearchPaid : Bool
    arbitraryNonzeroVectorYieldsSelectedNonzeroCoordinate : Bool
    normQualifiedAmplitudeFromOrdinaryNonzeroPaid : Bool
    deltaOrbitBasisSpanningRoutePaid : Bool
    schrodingerIrreducibilityPaid : Bool
    fixedCentralCharacterUniquenessPaid : Bool
    actualMonster729IdentificationPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true
  true
  true
  true
  true
  true
  false
  false

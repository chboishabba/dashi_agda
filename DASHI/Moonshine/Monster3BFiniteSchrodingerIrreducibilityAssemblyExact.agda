module DASHI.Moonshine.Monster3BFiniteSchrodingerIrreducibilityAssemblyExact where

------------------------------------------------------------------------
-- SCHRODINGER IRREDUCIBILITY ASSEMBLY
--
-- Monster-specific work is now separated from ordinary finite-module
-- bookkeeping.  The branch already proves:
--   * extraction of one delta line from any nonzero invariant vector;
--   * transport of that delta line to every X6 point using only the six
--     Heisenberg translation generators.
--
-- The only ordinary ingredient consumed here is a finite delta synthesis
-- receipt for the finite carrier X6.  It says that finite linear closure of all
-- scalar delta terms reconstructs an arbitrary Q(zeta_3)-valued function.
-- This receipt carries no Monster/Heisenberg semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaExtractionExact as Extract
import DASHI.Moonshine.Monster3BFiniteSchrodingerFullDeltaOrbitExact as Orbit

------------------------------------------------------------------------
-- 1. Ordinary finite delta synthesis interface.
------------------------------------------------------------------------

record FiniteDeltaSynthesis : Set₁ where
  field
    synthesize :
      (coefficients : H.X6 → C3.Cyclotomic3) → V.SchrodingerFunction

    synthesizePointwise :
      (coefficients : H.X6 → C3.Cyclotomic3) →
      V.PointwiseEqual (synthesize coefficients) coefficients

    synthesisClosedFromDeltaTerms :
      ∀ {Member}
        (inv : V.HeisenbergInvariantSubspace Member)
        (coefficients : H.X6 → C3.Cyclotomic3) →
        ((x : H.X6) →
          Member
            (V.cyclotomicScaleFunction
              (coefficients x)
              (Extract.comparisonDelta x))) →
        Member (synthesize coefficients)
open FiniteDeltaSynthesis public

------------------------------------------------------------------------
-- 2. Once one extracted delta is present, every delta is present.
------------------------------------------------------------------------

allDeltaMembersFromNonzeroWitness :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    (witness : Extract.NonzeroInvariantVector inv) →
    (target : H.X6) →
    Member (Extract.comparisonDelta target)
allDeltaMembersFromNonzeroWitness inv witness target =
  Orbit.allDeltaOrbitMember inv
    (Extract.selected witness)
    target
    (Extract.deltaLineMember inv witness)

allScaledDeltaMembersFromNonzeroWitness :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    (witness : Extract.NonzeroInvariantVector inv) →
    (coefficients : H.X6 → C3.Cyclotomic3) →
    (target : H.X6) →
    Member
      (V.cyclotomicScaleFunction
        (coefficients target)
        (Extract.comparisonDelta target))
allScaledDeltaMembersFromNonzeroWitness inv witness coefficients target =
  V.closedUnderCyclotomicScaling inv
    (coefficients target)
    (Extract.comparisonDelta target)
    (allDeltaMembersFromNonzeroWitness inv witness target)

------------------------------------------------------------------------
-- 3. Irreducibility conclusion in proof-relevant form.
------------------------------------------------------------------------

record WholeSchrodingerSubspace
    (Member : V.SchrodingerFunction → Set) : Set where
  constructor whole-schrodinger-subspace
  field
    everyFunctionMember : (f : V.SchrodingerFunction) → Member f
open WholeSchrodingerSubspace public

schrodingerInvariantSubspaceIsWhole :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    FiniteDeltaSynthesis →
    Extract.NonzeroInvariantVector inv →
    WholeSchrodingerSubspace Member
schrodingerInvariantSubspaceIsWhole inv finite witness =
  whole-schrodinger-subspace λ f →
    V.closedUnderPointwiseEquality inv
      (synthesize finite f)
      f
      (synthesisClosedFromDeltaTerms finite inv f
        (allScaledDeltaMembersFromNonzeroWitness inv witness f))
      (synthesizePointwise finite f)

record SchrodingerIrreducibilityReceipt : Set₁ where
  constructor schrodinger-irreducibility-receipt
  field
    finiteDeltaSynthesis : FiniteDeltaSynthesis
    everyNonzeroInvariantSubspaceIsWhole :
      ∀ {Member}
        (inv : V.HeisenbergInvariantSubspace Member) →
        Extract.NonzeroInvariantVector inv →
        WholeSchrodingerSubspace Member
open SchrodingerIrreducibilityReceipt public

assembleSchrodingerIrreducibility :
  (finite : FiniteDeltaSynthesis) → SchrodingerIrreducibilityReceipt
assembleSchrodingerIrreducibility finite =
  schrodinger-irreducibility-receipt finite
    (λ inv witness → schrodingerInvariantSubspaceIsWhole inv finite witness)

record IrreducibilityAssemblyBoundary : Set where
  constructor irreducibility-assembly-boundary
  field
    deltaExtractionConsumed : Bool
    fullDeltaOrbitConsumed : Bool
    ordinaryFiniteDeltaSynthesisSeparated : Bool
    MonsterSpecificEnumerationReprovedHere : Bool
    fixedCentralCharacterUniquenessProvedHere : Bool
open IrreducibilityAssemblyBoundary public

canonicalIrreducibilityAssemblyBoundary : IrreducibilityAssemblyBoundary
canonicalIrreducibilityAssemblyBoundary =
  irreducibility-assembly-boundary true true true false false

module DASHI.Physics.Closure.NSTriadKNClayNavierStokesTheoremLanguageRound359Exact where

------------------------------------------------------------------------
-- ROUND359 / BIDI: EXPLICIT FULL-DATA CLAY NAVIER-STOKES THEOREM LANGUAGE
--
-- R356--R358 deliberately left the Clay conclusion abstract.  Repository
-- archaeology found scoped/global-regularity ledgers, but no reusable theorem
-- proposition for the full Clay quantifier:
--
--   every admissible smooth divergence-free finite-energy datum
--     -> a global smooth Navier-Stokes solution, unique in the declared class.
--
-- The key BIDI correction is quantifier ownership.  R240/R354 are indexed by
-- physical Galerkin trajectories; the Clay statement is indexed by INITIAL
-- DATA.  This module defines only the theorem language.  It proves no PDE fact
-- and does not identify a Galerkin trajectory with an initial datum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

module ClayNavierStokesTheoremLanguage
    (InitialDatum Solution : Set)
    (AdmissibleSmoothDatum : InitialDatum → Set)
    (SolvesGlobalSmoothNS : InitialDatum → Solution → Set)
    (UniqueInDeclaredSmoothClass : InitialDatum → Solution → Set) where

  record GlobalSmoothUniqueSolution (datum : InitialDatum) : Set where
    field
      solution : Solution
      solvesGlobalSmoothNS : SolvesGlobalSmoothNS datum solution
      uniqueInDeclaredSmoothClass :
        UniqueInDeclaredSmoothClass datum solution

  open GlobalSmoothUniqueSolution public

  ClayNavierStokesConclusion : Set
  ClayNavierStokesConclusion =
    (datum : InitialDatum) →
    AdmissibleSmoothDatum datum →
    GlobalSmoothUniqueSolution datum

round359ClayQuantifierCarrierIsInitialData : Bool
round359ClayQuantifierCarrierIsInitialData = true

round359GlobalSmoothExistenceAndUniquenessAreProofFields : Bool
round359GlobalSmoothExistenceAndUniquenessAreProofFields = true

round359GalerkinTrajectoryIdentifiedWithInitialDatum : Bool
round359GalerkinTrajectoryIdentifiedWithInitialDatum = false

round359PDETheoremProvedHere : Bool
round359PDETheoremProvedHere = false

round359ClayQuantifierCarrierIsInitialDataIsTrue :
  round359ClayQuantifierCarrierIsInitialData ≡ true
round359ClayQuantifierCarrierIsInitialDataIsTrue = refl

round359GalerkinTrajectoryIdentifiedWithInitialDatumIsFalse :
  round359GalerkinTrajectoryIdentifiedWithInitialDatum ≡ false
round359GalerkinTrajectoryIdentifiedWithInitialDatumIsFalse = refl

round359PDETheoremProvedHereIsFalse : round359PDETheoremProvedHere ≡ false
round359PDETheoremProvedHereIsFalse = refl

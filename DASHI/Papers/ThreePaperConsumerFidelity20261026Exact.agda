module DASHI.Papers.ThreePaperConsumerFidelity20261026Exact where

-- Source-faithful theorem/admission guards for the three-paper cut.
--
-- Original research: Evan Miller (2021), DOI 10.1090/bproc/74;
-- Weiping Yan and Vicenţiu D. Rădulescu (2021),
-- DOI 10.1007/s12215-020-00540-3;
-- Jeremy Rodgers (2026-10-23), DOI as printed in the supplied manuscript
-- 10.5281/zenodo.23591626.
--
-- Methodology crosscheck (NOT source of these DASHI finite theorems):
-- Alexander Bastounis, Fabian Circelli, Anders C. Hansen (2026-10-06),
-- "Navier-Stokes lost in translation: Why Lean verification of AI
-- autoformalisation does not guarantee correct natural language proofs",
-- arXiv:2610.08144. Their paper *argues* semantic noncorrespondence in a
-- particular autoformalisation, not invalidity of Lean's kernel.
--
-- All finite collision results below are DASHI extensions built with the
-- pre-existing canonical IntersectionalNonFactorability owner; their role
-- is to prohibit erasing hypotheses in *this repository's* adapters.
-- No third-party theorem is imported here by being cited.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.InterpretiveFormalisationCoreExact as Interpretation
import DASHI.Foundations.ClaimScopeCertificateExact as ClaimScope

------------------------------------------------------------------------
-- Yan-Rădulescu: dropping div(f) erases a required pressure correction.
-- The finite source cases are synthetic semantic witnesses, not claimed
-- solutions of the physical PDE. Their actual scalar countermodel lives
-- in dashi_lean4 PR #87 under YanRadulescuPressureCountermodel.
------------------------------------------------------------------------

data StationaryForcingSource : Set where
  divergenceFreeForcing : StationaryForcingSource
  forcingWithNonzeroDivergence : StationaryForcingSource

data PrintedPressureShape : Set where
  pressureWithoutForceDivergence : PrintedPressureShape

data PhysicalPressureShape : Set where
  noForcingCorrection : PhysicalPressureShape
  nonzeroForcingCorrection : PhysicalPressureShape

eraseForceDivergence :
  StationaryForcingSource → PrintedPressureShape
eraseForceDivergence divergenceFreeForcing =
  pressureWithoutForceDivergence
eraseForceDivergence forcingWithNonzeroDivergence =
  pressureWithoutForceDivergence

requiredPressureCorrection :
  StationaryForcingSource → PhysicalPressureShape
requiredPressureCorrection divergenceFreeForcing =
  noForcingCorrection
requiredPressureCorrection forcingWithNonzeroDivergence =
  nonzeroForcingCorrection

differentPressureCorrections :
  noForcingCorrection ≡ nonzeroForcingCorrection → ⊥
differentPressureCorrections ()

pressureSourceLossWitness :
  NF.NonFactorabilityWitness
    eraseForceDivergence requiredPressureCorrection
pressureSourceLossWitness =
  NF.nonFactorabilityWitness
    divergenceFreeForcing forcingWithNonzeroDivergence
    refl differentPressureCorrections

erasedForcingCannotRecoverSourcePressureCorrection :
  NF.FactorsThrough
    eraseForceDivergence requiredPressureCorrection → ⊥
erasedForcingCannotRecoverSourcePressureCorrection =
  NF.witnessRulesOutEveryFlatFactorisation
    pressureSourceLossWitness

------------------------------------------------------------------------
-- Miller: unforced whole-space and periodic Galerkin are different
-- physical source types. A source-blind proposition does not prove
-- the original source/domain required by Miller's Theorem 1.6.
-- The finite pair only models hypothesis erasure, not physical dynamics.
------------------------------------------------------------------------

data NavierStokesDomain : Set where
  unforcedWholeSpaceR3 : NavierStokesDomain
  periodicGalerkinT3 : NavierStokesDomain

data DomainErasedObservation : Set where
  navierStokesEstimateLabel : DomainErasedObservation

data PhysicalDomainTruth : Set where
  physicalR3 : PhysicalDomainTruth
  physicalT3 : PhysicalDomainTruth

erasePhysicalDomain :
  NavierStokesDomain → DomainErasedObservation
erasePhysicalDomain unforcedWholeSpaceR3 =
  navierStokesEstimateLabel
erasePhysicalDomain periodicGalerkinT3 =
  navierStokesEstimateLabel

actualPhysicalDomain :
  NavierStokesDomain → PhysicalDomainTruth
actualPhysicalDomain unforcedWholeSpaceR3 = physicalR3
actualPhysicalDomain periodicGalerkinT3 = physicalT3

differentPhysicalDomains :
  physicalR3 ≡ physicalT3 → ⊥
differentPhysicalDomains ()

sourceDomainLossWitness :
  NF.NonFactorabilityWitness erasePhysicalDomain actualPhysicalDomain
sourceDomainLossWitness =
  NF.nonFactorabilityWitness
    unforcedWholeSpaceR3 periodicGalerkinT3
    refl differentPhysicalDomains

domainBlindEstimateCannotDetermineMillerSource :
  NF.FactorsThrough erasePhysicalDomain actualPhysicalDomain → ⊥
domainBlindEstimateCannotDetermineMillerSource =
  NF.witnessRulesOutEveryFlatFactorisation
    sourceDomainLossWitness

------------------------------------------------------------------------
-- Existing meta-owners already keep:
-- formalization ≠ equivalence; kernel proof ≠ empirical confirmation;
-- a "not established here" Boolean/claim scope ≠ refutation.
-- Import canonical objects instead of defining duplicate metatheories.
------------------------------------------------------------------------

translationAndEmpiricalBoundaries :
  Interpretation.InterpretiveFormalisationBoundary
translationAndEmpiricalBoundaries =
  Interpretation.canonicalInterpretiveFormalisationBoundary

nonclaimIsNotARefutation :
  ClaimScope.BoundarySemanticsClaimScope
nonclaimIsNotARefutation =
  ClaimScope.canonicalBoundarySemanticsClaimScope

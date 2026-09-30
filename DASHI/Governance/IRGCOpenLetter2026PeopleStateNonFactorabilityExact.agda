module DASHI.Governance.IRGCOpenLetter2026PeopleStateNonFactorabilityExact where

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.IRGCOpenLetter2026StrategicCommunicationExact as Letter

------------------------------------------------------------------------
-- Exact counterexample to collapsing nationality into source-local target.
------------------------------------------------------------------------

data AmericanSituatedRole : Set where
  ordinaryPeople governingElite : AmericanSituatedRole

data NationalSurface : Set where
  american : NationalSurface

data SourceLocalTarget : Set where
  addressedAsPotentialPartner targetedAsPoliticalAdversary : SourceLocalTarget

nationalProjection : AmericanSituatedRole → NationalSurface
nationalProjection _ = american

sourceLocalTarget : AmericanSituatedRole → SourceLocalTarget
sourceLocalTarget ordinaryPeople = addressedAsPotentialPartner
sourceLocalTarget governingElite = targetedAsPoliticalAdversary

targetsDiffer :
  sourceLocalTarget ordinaryPeople ≡
  sourceLocalTarget governingElite → ⊥
targetsDiffer ()

peopleStateTargetDefect :
  NF.NonFactorabilityWitness nationalProjection sourceLocalTarget
peopleStateTargetDefect =
  NF.nonFactorabilityWitness ordinaryPeople governingElite refl targetsDiffer

americanIdentityCannotDetermineSourceTarget :
  NF.FactorsThrough nationalProjection sourceLocalTarget → ⊥
americanIdentityCannotDetermineSourceTarget =
  NF.witnessRulesOutEveryFlatFactorisation peopleStateTargetDefect

anyNationalityRechartStillCannotDetermineTarget :
  ∀ {Chart : Set} (chart : NationalSurface → Chart) →
  NF.FactorsThrough (λ role → chart (nationalProjection role)) sourceLocalTarget →
  ⊥
anyNationalityRechartStillCannotDetermineTarget chart =
  NF.rechartingCannotRecoverErasedPhenomenon chart peopleStateTargetDefect

module DASHI.Governance.SexedHistoricalSubjectDialecticBidiExact where

------------------------------------------------------------------------
-- SEXED / GENDERED HISTORICAL SUBJECT DIALECTIC, BIDI
--
-- This module does NOT assign dialectical roles intrinsically to biological
-- males/females.  It models historically constructed masculine-coded and
-- feminine-coded subject positions whose role changes with the comparison
-- frame.  Both can appear as inherited norm, lived form, counter-formation,
-- or reconstituted form.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ContextualDialecticRoleExact as Dialectic
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as LacanIrigaray
import DASHI.Core.LacanSexuationTernarySeparationExact as Sexuation
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Constructed positions, not biological essences.
------------------------------------------------------------------------

data HistoricalGenderedPosition : Set where
  masculineCoded feminineCoded : HistoricalGenderedPosition

data HistoricalComparisonFrame : Set where
  inheritedPatriarchalFrame
  feministCounterFrame
  masculineCounterReactionFrame
  reciprocalReconstitutionFrame
  : HistoricalComparisonFrame

historicalRoleSystem :
  Dialectic.ContextualRoleSystem HistoricalComparisonFrame HistoricalGenderedPosition
historicalRoleSystem = record { roleIn = role }
  where
    role : HistoricalComparisonFrame → HistoricalGenderedPosition → Dialectic.DialecticRole
    role inheritedPatriarchalFrame masculineCoded = Dialectic.initialRole
    role inheritedPatriarchalFrame feminineCoded = Dialectic.counterRole
    role feministCounterFrame masculineCoded = Dialectic.counterRole
    role feministCounterFrame feminineCoded = Dialectic.initialRole
    role masculineCounterReactionFrame masculineCoded = Dialectic.initialRole
    role masculineCounterReactionFrame feminineCoded = Dialectic.counterRole
    role reciprocalReconstitutionFrame masculineCoded = Dialectic.mediatingRole
    role reciprocalReconstitutionFrame feminineCoded = Dialectic.mediatingRole

masculineRoleChanges : Dialectic.RoleChangeWitness historicalRoleSystem
masculineRoleChanges =
  Dialectic.role-change-witness
    masculineCoded inheritedPatriarchalFrame feministCounterFrame (λ ())

feminineRoleChanges : Dialectic.RoleChangeWitness historicalRoleSystem
feminineRoleChanges =
  Dialectic.role-change-witness
    feminineCoded inheritedPatriarchalFrame feministCounterFrame (λ ())

noIntrinsicMasculineDialecticRole :
  (intrinsic : HistoricalGenderedPosition → Dialectic.DialecticRole) →
  ((frame : HistoricalComparisonFrame) (position : HistoricalGenderedPosition) →
    Dialectic.roleIn historicalRoleSystem frame position ≡ intrinsic position) →
  ⊥
noIntrinsicMasculineDialecticRole intrinsic agrees =
  Dialectic.roleChangeBlocksIntrinsicRole masculineRoleChanges intrinsic agrees

noIntrinsicFeminineDialecticRole :
  (intrinsic : HistoricalGenderedPosition → Dialectic.DialecticRole) →
  ((frame : HistoricalComparisonFrame) (position : HistoricalGenderedPosition) →
    Dialectic.roleIn historicalRoleSystem frame position ≡ intrinsic position) →
  ⊥
noIntrinsicFeminineDialecticRole intrinsic agrees =
  Dialectic.roleChangeBlocksIntrinsicRole feminineRoleChanges intrinsic agrees

------------------------------------------------------------------------
-- Opposition is historical/relational and does not manufacture logical
-- negation or guarantee synthesis.  Reconstitution is an additional route.
------------------------------------------------------------------------

data HistoricalOppositionPromotesLogicalNegation : Set where

data CounterFormationGuaranteesSynthesis : Set where

historicalOppositionDoesNotPromoteLogicalNegation :
  HistoricalOppositionPromotesLogicalNegation → ⊥
historicalOppositionDoesNotPromoteLogicalNegation ()

counterFormationDoesNotGuaranteeSynthesis :
  CounterFormationGuaranteesSynthesis → ⊥
counterFormationDoesNotGuaranteeSynthesis ()

------------------------------------------------------------------------
-- Lacan/Irigaray remains a grammar difference, not male/female ontology.
------------------------------------------------------------------------

irigarayStillNotSignFlipOfLacan :
  (p : DASHI.Core.TernaryRoleCarrierExact.TernaryPermutation) →
  LacanIrigaray.GrammarPreserving p → ⊥
irigarayStillNotSignFlipOfLacan =
  LacanIrigaray.noTernaryRelabellingPreservesGrammar

sexuationRolesRemainNonBiological : Bool
sexuationRolesRemainNonBiological = false

------------------------------------------------------------------------
-- Representation boundary applies symmetrically: public gender legibility does
-- not transparently recover originating subject-position for either side.
------------------------------------------------------------------------

representationStillDoesNotRecoverSubject :
  INF.FactorsThrough Subject.categoryVisibility Subject.subjectPosition → ⊥
representationStillDoesNotRecoverSubject =
  Subject.categoryVisibilityCannotRecoverSubjectPosition

record SexedHistoricalSubjectDialecticBoundary : Set where
  constructor sexed-historical-subject-dialectic-boundary
  field
    masculineIsIntrinsicThesis : Bool
    feminineIsIntrinsicAntithesis : Bool
    biologicalSexFixesDialecticRole : Bool
    oppositionEqualsLogicalContradiction : Bool
    counterFormationGuaranteesSynthesis : Bool
    bothConstructedSidesCanChangeRoleAcrossFrames : Bool
    reciprocalReconstitutionAvailableAsDistinctFrame : Bool

canonicalSexedHistoricalSubjectDialecticBoundary :
  SexedHistoricalSubjectDialecticBoundary
canonicalSexedHistoricalSubjectDialecticBoundary =
  sexed-historical-subject-dialectic-boundary
    false false false false false true true

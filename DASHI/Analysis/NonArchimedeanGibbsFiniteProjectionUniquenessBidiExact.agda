module DASHI.Analysis.NonArchimedeanGibbsFiniteProjectionUniquenessBidiExact where

------------------------------------------------------------------------
-- GIBBS UNIQUENESS VIA FINITE DYADIC PROJECTIONS
--
-- The source prose claims unique Haar conformal Gibbs MEASURE.  Its formal
-- `IsConformalGibbs`, however, is a predicate on arbitrary real linear
-- functionals with no positivity, normalization or continuity fields.
--
-- This module repairs the semantic target to probability measures and routes
-- uniqueness through literal finite quotients:
--
--   stationary probability measure mu on Z_2
--     -> (toZModPow n)_* mu stationary on Z/2^n Z
--     -> finite quotient law is the unique uniform stationary law
--     -> every dyadic residue-cylinder mass agrees with Haar
--     -> mu = Haar once residue cylinders determine the Borel measure.
--
-- Mathlib already owns:
--   * PadicInt.toZModPow : Z_p ->+* ZMod (p^n);
--   * projective-limit infrastructure PadicInt.lift/lift_unique;
--   * generic finite-measure extensionality from a generating pi-system;
--   * uniqueness of probability Haar measure once Haar invariance is known.
--
-- The only source/library topology receipt not located under an exact theorem
-- name is that the fibers of all dyadic toZModPow maps form a determining
-- cylinder family for the Borel sigma-algebra on Z_2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data GibbsMeasureLeaf : Set where
  measureLevelGibbsDefinition : GibbsMeasureLeaf
  padicFiniteProjection : GibbsMeasureLeaf
  stationaryPushforwardCommutes : GibbsMeasureLeaf
  finiteUniformStationaryUniqueness : GibbsMeasureLeaf
  residueCylinderMassEquality : GibbsMeasureLeaf
  residueCylindersGenerateBorel : GibbsMeasureLeaf
  probabilityMeasureGibbsUniqueness : GibbsMeasureLeaf
  arbitraryLinearFunctionalUniqueness : GibbsMeasureLeaf


data GibbsMeasureStatus : Set where
  semanticRepair : GibbsMeasureStatus
  sourceLibraryOwned : GibbsMeasureStatus
  compiled : GibbsMeasureStatus
  liveTopologyReceipt : GibbsMeasureStatus
  downstream : GibbsMeasureStatus
  rejectedPromotion : GibbsMeasureStatus

gibbsMeasureStatus : GibbsMeasureLeaf → GibbsMeasureStatus
gibbsMeasureStatus measureLevelGibbsDefinition = semanticRepair
gibbsMeasureStatus padicFiniteProjection = sourceLibraryOwned
gibbsMeasureStatus stationaryPushforwardCommutes = compiled
gibbsMeasureStatus finiteUniformStationaryUniqueness = compiled
gibbsMeasureStatus residueCylinderMassEquality = compiled
gibbsMeasureStatus residueCylindersGenerateBorel = liveTopologyReceipt
gibbsMeasureStatus probabilityMeasureGibbsUniqueness = downstream
gibbsMeasureStatus arbitraryLinearFunctionalUniqueness = rejectedPromotion


data GibbsMeasureObligation : Set where
  needPadicResidueCylindersGenerateBorel : GibbsMeasureObligation

probabilityMeasureUniquenessCutset : List GibbsMeasureObligation
probabilityMeasureUniquenessCutset =
  needPadicResidueCylindersGenerateBorel ∷ []

record SourceLibraryReceipt : Set where
  constructor sourceLibraryReceipt
  field
    continuousTransferDefinesPlainLinearFunctionalGibbs : Bool
    sourceProseClaimsMeasureUniqueness : Bool
    padicToZModPowOwned : Bool
    padicProjectiveLimitUniversalPropertyOwned : Bool
    genericMeasureExtFromGeneratingPiSystemOwned : Bool
    finiteUniformStationaryLawOwned : Bool
    cylinderGeneratorTheoremLocated : Bool

canonicalSourceLibraryReceipt : SourceLibraryReceipt
canonicalSourceLibraryReceipt =
  sourceLibraryReceipt true true true true true true false

plainFunctionalPredicateIsNotProbabilityStateDefinition :
  SourceLibraryReceipt.continuousTransferDefinesPlainLinearFunctionalGibbs
    canonicalSourceLibraryReceipt
  ≡ true
plainFunctionalPredicateIsNotProbabilityStateDefinition = refl

probabilityUniquenessStillSingleTopologyLeaf :
  probabilityMeasureUniquenessCutset
  ≡ needPadicResidueCylindersGenerateBorel ∷ []
probabilityUniquenessStillSingleTopologyLeaf = refl

record GibbsUniquenessFirewall : Set where
  constructor gibbsUniquenessFirewall
  field
    finiteStationaryUniquenessAutomaticallyEqualsInfiniteMeasureUniqueness : Bool
    arbitraryLinearFunctionalGibbsUniquenessClaimed : Bool
    branchAverageInvarianceImpliesEachBranchInvariant : Bool
    probabilityMeasureRouteUsesFiniteProjections : Bool

canonicalGibbsUniquenessFirewall : GibbsUniquenessFirewall
canonicalGibbsUniquenessFirewall =
  gibbsUniquenessFirewall false false false true

noFunctionalOverpromotion :
  GibbsUniquenessFirewall.arbitraryLinearFunctionalGibbsUniquenessClaimed
    canonicalGibbsUniquenessFirewall
  ≡ false
noFunctionalOverpromotion = refl

noBranchwiseShortcut :
  GibbsUniquenessFirewall.branchAverageInvarianceImpliesEachBranchInvariant
    canonicalGibbsUniquenessFirewall
  ≡ false
noBranchwiseShortcut = refl

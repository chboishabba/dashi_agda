module DASHI.Moonshine.OggMonstrousExponentBraidedProvenanceExact where

------------------------------------------------------------------------
-- OGG / MONSTROUS EXPONENT BRAIDED PROVENANCE
--
-- SOURCE BOUNDARY
--
-- External arithmetic is consumed through
--   OggMonstrousExponentTrialecticDescentExact
--   -> MonsterOrderExponentCorrectionExact
--   -> Duncan--Swisher.
--
-- Braiding Sweetgrass / Two-Eyed Seeing are NOT mathematical authorities for
-- the arithmetic below.  DASHI imports only the already source-bounded
-- structural lesson used elsewhere in the repository:
--
--   coordinated/convergent output does not fuse knowledge/source provenance.
--
-- DASHI contribution:
--   the three arithmetic contribution roles are retained as distinct strands;
--   flattening to the total Monster exponent does not recover which strand a
--   multiplicity slot came from.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.KimmererBraidingAcknowledgement as Sweetgrass
import DASHI.Moonshine.OggMonstrousExponentTrialecticDescentExact as Trial
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source

------------------------------------------------------------------------
-- 1. Contribution-role provenance is explicit.
------------------------------------------------------------------------

roleOfSlot :
  {prime : Lane.MonsterPrimeLane} ->
  (trial : Trial.ArithmeticTrialectic prime) ->
  Trial.ArithmeticMultiplicitySlot trial ->
  Trial.ModularContributionRole
roleOfSlot trial (inj₁ slot) =
  Trial.frickeComparison
roleOfSlot trial (inj₂ (inj₁ slot)) =
  Trial.levelPComparison
roleOfSlot trial (inj₂ (inj₂ slot)) =
  Trial.levelP2Comparison

------------------------------------------------------------------------
-- 2. p=5 is the smallest useful exact collision because all three source
--    fibres are nonempty: (A,B,C)=(3,5,1).
------------------------------------------------------------------------

p5FrickeSlot :
  Trial.ArithmeticMultiplicitySlot Trial.p5Trialectic
p5FrickeSlot = inj₁ zero

p5LevelPSlot :
  Trial.ArithmeticMultiplicitySlot Trial.p5Trialectic
p5LevelPSlot = inj₂ (inj₁ zero)

p5LevelP2Slot :
  Trial.ArithmeticMultiplicitySlot Trial.p5Trialectic
p5LevelP2Slot = inj₂ (inj₂ zero)

data FlattenedP5ExponentObservation : Set where
  p5ExponentNine : FlattenedP5ExponentObservation

flattenP5Slot :
  Trial.ArithmeticMultiplicitySlot Trial.p5Trialectic ->
  FlattenedP5ExponentObservation
flattenP5Slot _ = p5ExponentNine

p5Role :
  Trial.ArithmeticMultiplicitySlot Trial.p5Trialectic ->
  Trial.ModularContributionRole
p5Role = roleOfSlot Trial.p5Trialectic

sameFlattenedObservationFrickeP :
  flattenP5Slot p5FrickeSlot
  ≡ flattenP5Slot p5LevelPSlot
sameFlattenedObservationFrickeP = refl

frickeRoleDiffersFromP :
  p5Role p5FrickeSlot
  ≡ p5Role p5LevelPSlot ->
  ⊥
frickeRoleDiffersFromP ()

p5ContributionRoleNonFactorability :
  NF.NonFactorabilityWitness
    flattenP5Slot
    p5Role
p5ContributionRoleNonFactorability =
  NF.nonFactorabilityWitness
    p5FrickeSlot
    p5LevelPSlot
    sameFlattenedObservationFrickeP
    frickeRoleDiffersFromP

p5TotalExponentDoesNotRecoverContributionRole :
  NF.FactorsThrough flattenP5Slot p5Role ->
  ⊥
p5TotalExponentDoesNotRecoverContributionRole =
  NF.witnessRulesOutEveryFlatFactorisation
    p5ContributionRoleNonFactorability

------------------------------------------------------------------------
-- 3. Any rechart of the already flattened total still cannot recover role.
------------------------------------------------------------------------

p5RechartCannotRecoverContributionRole :
  ∀ {Recharted : Set} ->
  (rechart : FlattenedP5ExponentObservation -> Recharted) ->
  NF.FactorsThrough
    (λ slot -> rechart (flattenP5Slot slot))
    p5Role
  ->
  ⊥
p5RechartCannotRecoverContributionRole rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart
    p5ContributionRoleNonFactorability

------------------------------------------------------------------------
-- 4. Braided arithmetic package: distinct source strands + exact total.
------------------------------------------------------------------------

record BraidedArithmeticTrialectic
    (prime : Lane.MonsterPrimeLane) : Set where
  constructor braided-arithmetic-trialectic
  field
    arithmetic : Trial.ArithmeticTrialectic prime

    frickeStrandValue : Nat
    levelPStrandValue : Nat
    levelP2StrandValue : Nat

    frickeExact :
      frickeStrandValue ≡ Trial.A arithmetic
    levelPExact :
      levelPStrandValue ≡ Trial.B arithmetic
    levelP2Exact :
      levelP2StrandValue ≡ Trial.C arithmetic

    strandsRemainDistinctInProvenance : Bool
    totalReconstructsExponent :
      frickeStrandValue + levelPStrandValue + levelP2StrandValue
      ≡
      Trial.A arithmetic + Trial.B arithmetic + Trial.C arithmetic

open BraidedArithmeticTrialectic public

canonicalBraidedArithmeticTrialectic :
  {prime : Lane.MonsterPrimeLane} ->
  (trial : Trial.ArithmeticTrialectic prime) ->
  BraidedArithmeticTrialectic prime
canonicalBraidedArithmeticTrialectic trial =
  braided-arithmetic-trialectic
    trial
    (Trial.A trial)
    (Trial.B trial)
    (Trial.C trial)
    refl refl refl
    true
    refl

------------------------------------------------------------------------
-- 5. Source-bounded epistemic analogies.
------------------------------------------------------------------------

twoEyedBoundary :
  TwoEyed.KimmererTwoEyedSeeingBoundary
twoEyedBoundary =
  TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

sweetgrassAcknowledgement :
  Sweetgrass.KimmererBraidingAcknowledgement
sweetgrassAcknowledgement =
  Sweetgrass.canonicalKimmererBraidingAcknowledgement

data ArithmeticBraidIsKimmererTheorem : Set where
data ArithmeticTripleIsTwoEyedSeeingClaim : Set where
data SharedExponentFusesArithmeticSourceRoles : Set where
data Downstream369CodeMaySilentlyEraseRole : Set where

arithmeticBraidIsNotKimmererTheorem :
  ArithmeticBraidIsKimmererTheorem -> ⊥
arithmeticBraidIsNotKimmererTheorem ()

arithmeticTripleIsNotTwoEyedSeeingClaim :
  ArithmeticTripleIsTwoEyedSeeingClaim -> ⊥
arithmeticTripleIsNotTwoEyedSeeingClaim ()

sharedExponentDoesNotFuseArithmeticSourceRoles :
  SharedExponentFusesArithmeticSourceRoles -> ⊥
sharedExponentDoesNotFuseArithmeticSourceRoles ()

downstream369CodeMayNotSilentlyEraseRole :
  Downstream369CodeMaySilentlyEraseRole -> ⊥
downstream369CodeMayNotSilentlyEraseRole ()

------------------------------------------------------------------------
-- 6. Attribution classification.
------------------------------------------------------------------------

braidedArithmeticClaimOrigin : Source.ClaimOrigin
braidedArithmeticClaimOrigin =
  Source.repositoryCrossModuleInference

record OggMonstrousExponentBraidedProvenanceBoundary : Set where
  constructor ogg-monstrous-exponent-braided-provenance-boundary
  field
    threeArithmeticSourceRolesRetained : Bool
    p5AllThreeContributionStrandsNonempty : Bool
    flattenedExponentRecoversContributionRole : Bool
    postRechartRecoversErasedContributionRole : Bool
    sourceBraidingUsedAsMathematicalAuthority : Bool
    twoEyedSeeingUsedAsArithmeticTheorem : Bool
    downstreamEncodingMustDeclareRoleLoss : Bool

canonicalOggMonstrousExponentBraidedProvenanceBoundary :
  OggMonstrousExponentBraidedProvenanceBoundary
canonicalOggMonstrousExponentBraidedProvenanceBoundary =
  ogg-monstrous-exponent-braided-provenance-boundary
    true true false false false false true

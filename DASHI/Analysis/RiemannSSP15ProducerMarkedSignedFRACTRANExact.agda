module DASHI.Analysis.RiemannSSP15ProducerMarkedSignedFRACTRANExact where

------------------------------------------------------------------------
-- PRODUCER-MARKED RH ROLES -> SIGNED SSP FRACTRAN
--
-- Conditional on an actual producer-side role certificate, compile the
-- source-marked depth-five roles through the already-owned SSP15 pointed
-- signed carrier and into the existing SignedSSPFRACTRANWeaveExact
-- instruction language.
--
-- Chosen indexing semantics:
--
--   originRole -> negative unit multiplicity
--              -> introduceInversePrime selectedPrime
--
--   jRole      -> zero multiplicity
--              -> empty arithmetic instruction program
--              -> BUT selectedPrime remains in the pointed seed
--
--   sRole      -> positive unit multiplicity
--              -> introducePrime selectedPrime
--
-- Thus the signed FRACTRAN programme intentionally loses the neutral selected
-- lane unless the pointed seed is retained.  This is the executable version
-- of the provenance-loss theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Analysis.RiemannSSP15DepthFiveRoleCodecExact as Codec
import DASHI.Analysis.RiemannSSP15FilteredProvenanceCapstoneExact as Capstone
import DASHI.Analysis.RiemannSSP15SignedProvenanceBridgeExact as Provenance
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Branch
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Role-indexed signed FRACTRAN programme.
------------------------------------------------------------------------

roleProgram :
  Codec.RHSSP15RoleCode ->
  List Signed.WeaveInstruction
roleProgram code with proj₂ code
... | Codec.originRole =
  Signed.introduceInversePrime
    (Branch.lanePrimeToSignedPrime
      (Provenance.roleCodeToPrime code))
  ∷ []
... | Codec.jRole =
  []
... | Codec.sRole =
  Signed.introducePrime
    (Branch.lanePrimeToSignedPrime
      (Provenance.roleCodeToPrime code))
  ∷ []

producerMarkedRoleProgram :
  {certificate : Capstone.PrimitiveRowProducerRoleCertificate} ->
  Capstone.ProducerMarkedSSP15Code certificate ->
  List Signed.WeaveInstruction
producerMarkedRoleProgram code =
  roleProgram (Capstone.eraseProducerMark code)

------------------------------------------------------------------------
-- 2. Producer-marked pointed FRACTRAN seed.
------------------------------------------------------------------------

producerMarkedSeed :
  {certificate : Capstone.PrimitiveRowProducerRoleCertificate} ->
  Capstone.ProducerMarkedSSP15Code certificate ->
  Branch.PointedSignedFRACTRANSeed
producerMarkedSeed code =
  Branch.seedFromInternalLane
    (Codec.encodeRoleCode (Capstone.eraseProducerMark code))
    (producerMarkedRoleProgram code)

producerMarkedPointedLaneExact :
  {certificate : Capstone.PrimitiveRowProducerRoleCertificate} ->
  (code : Capstone.ProducerMarkedSSP15Code certificate) ->
  Branch.pointedLane (producerMarkedSeed code)
  ≡
  Capstone.compileProducerMarkedToPointedSigned code
producerMarkedPointedLaneExact code = refl

producerMarkedValuationOwnLane :
  {certificate : Capstone.PrimitiveRowProducerRoleCertificate} ->
  (code : Capstone.ProducerMarkedSSP15Code certificate) ->
  Branch.valuation (producerMarkedSeed code)
    (Branch.lanePrimeToSignedPrime
      (Branch.selectedPrime
        (Branch.pointedLane (producerMarkedSeed code))))
  ≡
  Branch.signedMultiplicity
    (Branch.pointedLane (producerMarkedSeed code))
producerMarkedValuationOwnLane code =
  Branch.pointedValuationOwnLane
    (Branch.pointedLane (producerMarkedSeed code))

------------------------------------------------------------------------
-- 3. Exact signed execution effect.
------------------------------------------------------------------------

executeProducerMarked :
  {certificate : Capstone.PrimitiveRowProducerRoleCertificate} ->
  Capstone.ProducerMarkedSSP15Code certificate ->
  Signed.WeaveEffect
executeProducerMarked code =
  Branch.executeSeedProgram (producerMarkedSeed code)

originRoleProgramHasOneInverseToken :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (mode : Quotient.ComplementMode5) ->
  Signed.inversePrimeTokens
    (executeProducerMarked
      (Capstone.canonicalProducerMarkedCode
        certificate mode Codec.originRole))
  ≡ 1
originRoleProgramHasOneInverseToken certificate mode = refl

originRoleProgramHasNoPositiveToken :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (mode : Quotient.ComplementMode5) ->
  Signed.positivePrimeTokens
    (executeProducerMarked
      (Capstone.canonicalProducerMarkedCode
        certificate mode Codec.originRole))
  ≡ 0
originRoleProgramHasNoPositiveToken certificate mode = refl

jRoleProgramIsEmpty :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (mode : Quotient.ComplementMode5) ->
  producerMarkedRoleProgram
    (Capstone.canonicalProducerMarkedCode
      certificate mode Codec.jRole)
  ≡ []
jRoleProgramIsEmpty certificate mode = refl

jRoleProgramEffectIsEmpty :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (mode : Quotient.ComplementMode5) ->
  executeProducerMarked
    (Capstone.canonicalProducerMarkedCode
      certificate mode Codec.jRole)
  ≡ Signed.emptyWeaveEffect
jRoleProgramEffectIsEmpty certificate mode = refl

sRoleProgramHasOnePositiveToken :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (mode : Quotient.ComplementMode5) ->
  Signed.positivePrimeTokens
    (executeProducerMarked
      (Capstone.canonicalProducerMarkedCode
        certificate mode Codec.sRole))
  ≡ 1
sRoleProgramHasOnePositiveToken certificate mode = refl

sRoleProgramHasNoInverseToken :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (mode : Quotient.ComplementMode5) ->
  Signed.inversePrimeTokens
    (executeProducerMarked
      (Capstone.canonicalProducerMarkedCode
        certificate mode Codec.sRole))
  ≡ 0
sRoleProgramHasNoInverseToken certificate mode = refl

------------------------------------------------------------------------
-- 4. Neutral j role: executable arithmetic effect collapses, provenance does
-- not.
------------------------------------------------------------------------

jSelectedPrime :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  Quotient.ComplementMode5 ->
  Lane.MonsterPrimeLane
jSelectedPrime certificate mode =
  Branch.selectedPrime
    (Branch.pointedLane
      (producerMarkedSeed
        (Capstone.canonicalProducerMarkedCode
          certificate mode Codec.jRole)))

jMode09PrimeIsThree :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  jSelectedPrime certificate Quotient.mode09 ≡ Lane.p3
jMode09PrimeIsThree certificate = refl

jMode18PrimeIsEleven :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  jSelectedPrime certificate Quotient.mode18 ≡ Lane.p11
jMode18PrimeIsEleven certificate = refl

jMode27PrimeIsNineteen :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  jSelectedPrime certificate Quotient.mode27 ≡ Lane.p19
jMode27PrimeIsNineteen certificate = refl

jMode36PrimeIsThirtyOne :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  jSelectedPrime certificate Quotient.mode36 ≡ Lane.p31
jMode36PrimeIsThirtyOne certificate = refl

jMode45PrimeIsFiftyNine :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  jSelectedPrime certificate Quotient.mode45 ≡ Lane.p59
jMode45PrimeIsFiftyNine certificate = refl

jAllExecutionEffectsCoincide :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (left right : Quotient.ComplementMode5) ->
  executeProducerMarked
    (Capstone.canonicalProducerMarkedCode
      certificate left Codec.jRole)
  ≡
  executeProducerMarked
    (Capstone.canonicalProducerMarkedCode
      certificate right Codec.jRole)
jAllExecutionEffectsCoincide certificate left right =
  trans
    (jRoleProgramEffectIsEmpty certificate left)
    (sym (jRoleProgramEffectIsEmpty certificate right))

data EmptyJProgramRecoversSelectedPrime : Set where

emptyJProgramDoesNotRecoverSelectedPrime :
  EmptyJProgramRecoversSelectedPrime -> ⊥
emptyJProgramDoesNotRecoverSelectedPrime ()

------------------------------------------------------------------------
-- 5. Producer-marked role-code reopening remains exact above execution.
------------------------------------------------------------------------

producerMarkedSeedReopensRoleCode :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (mode : Quotient.ComplementMode5) ->
  (role : Codec.RHDepthFiveRole) ->
  Provenance.pointedSignedToRoleCode
    (Branch.pointedLane
      (producerMarkedSeed
        (Capstone.canonicalProducerMarkedCode
          certificate mode role)))
  ≡
  (mode , role)
producerMarkedSeedReopensRoleCode certificate mode role =
  Provenance.roleCodePointedRoundTrip (mode , role)

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

data SignedFRACTRANExecutionCreatesAnalyticIdentity : Set where

signedFRACTRANExecutionDoesNotCreateAnalyticIdentity :
  SignedFRACTRANExecutionCreatesAnalyticIdentity -> ⊥
signedFRACTRANExecutionDoesNotCreateAnalyticIdentity ()

record RiemannSSP15ProducerMarkedSignedFRACTRANBoundary : Set where
  constructor riemann-ssp15-producer-marked-signed-fractran-boundary
  field
    producerMarkedPointedSeedOwned : Bool
    originCompilesToInversePrimeInstruction : Bool
    jCompilesToEmptyArithmeticProgram : Bool
    sCompilesToPositivePrimeInstruction : Bool
    jSelectedPrimeRetainedAboveExecution : Bool
    jExecutionEffectCollapsesAcrossFiveModes : Bool
    pointedSeedReopensProducerRoleCode : Bool
    signedExecutionPromotedToAnalyticIdentity : Bool

canonicalRiemannSSP15ProducerMarkedSignedFRACTRANBoundary :
  RiemannSSP15ProducerMarkedSignedFRACTRANBoundary
canonicalRiemannSSP15ProducerMarkedSignedFRACTRANBoundary =
  riemann-ssp15-producer-marked-signed-fractran-boundary
    true true true true true true true false

module DASHI.Moonshine.Monster369SignedSSPTauInversionSeamExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit
import DASHI.Moonshine.JInvariantFormulaic369ModularReplicationExact as Replication
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Fricke
import DASHI.Wikimedia.IbrahimMonster6BCompleteReplicabilityPowerSnowballExact as Replicability

------------------------------------------------------------------------
-- MONSTER / 369 / SIGNED-SSP MODULAR-TAU INVERSION SEAM
--
-- The shared useful structure is an inversion grammar, not a numeral match.
--
-- * the modular side has a genuine Fricke involution on one fine modular point;
-- * the signed-SSP/FRACTRAN side has a genuine multiplicity negation, where
--   negative/zero/positive multiplicity projects to the balanced ternary fibre;
-- * the j-orbit owner already consumes that same signed multiplicity through
--   the balanced-trit seam/gluing observer;
-- * the existing formulaic-j replication owner already records that the same
--   signed-FRACTRAN seam word is reused by its analytic modular action.
--
-- We therefore construct the product involution
--
--      (tau , m) |-> (Fricke tau , -m)
--
-- abstractly over any existing ModularJFrickeSystem.
--
-- This does NOT identify signed FRACTRAN execution with a modular action, and
-- it does NOT yet prove that the 6B McKay-Thompson replicability owner uses the
-- same literal FinePoint/tau carrier.  That same-object weld remains the next
-- Monster-facing residual.  Modular tau is also kept distinct from Ramanujan's
-- arithmetic tau(n); shared notation creates no identity.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Signed multiplicity negation is already a true involution.
------------------------------------------------------------------------

signedNegationInvolutive :
  (m : SSP.SignedMultiplicity) ->
  SSP.negateMultiplicity (SSP.negateMultiplicity m) ≡ m
signedNegationInvolutive (SSP.negativeMultiplicity n) = refl
signedNegationInvolutive SSP.zeroMultiplicity = refl
signedNegationInvolutive (SSP.positiveMultiplicity n) = refl

------------------------------------------------------------------------
-- 2. Coarse balanced-trit projection commutes with sign reversal.
------------------------------------------------------------------------

negateTrit : Triadic.KernelTrit -> Triadic.KernelTrit
negateTrit Triadic.negativeTrit = Triadic.positiveTrit
negateTrit Triadic.zeroTrit = Triadic.zeroTrit
negateTrit Triadic.positiveTrit = Triadic.negativeTrit

negateTritInvolutive :
  (t : Triadic.KernelTrit) ->
  negateTrit (negateTrit t) ≡ t
negateTritInvolutive Triadic.negativeTrit = refl
negateTritInvolutive Triadic.zeroTrit = refl
negateTritInvolutive Triadic.positiveTrit = refl

coarseNegationCompatible :
  (m : SSP.SignedMultiplicity) ->
  SSP.coarseMultiplicity (SSP.negateMultiplicity m)
  ≡ negateTrit (SSP.coarseMultiplicity m)
coarseNegationCompatible (SSP.negativeMultiplicity n) = refl
coarseNegationCompatible SSP.zeroMultiplicity = refl
coarseNegationCompatible (SSP.positiveMultiplicity n) = refl

------------------------------------------------------------------------
-- 3. Product modular-point / signed-fibre state and exact involution.
------------------------------------------------------------------------

record TauSignedState (system : Fricke.ModularJFrickeSystem) : Set where
  constructor tau-signed-state
  field
    modularPoint : Fricke.FinePoint system
    signedMultiplicity : SSP.SignedMultiplicity
open TauSignedState public

tauSignedInversion :
  (system : Fricke.ModularJFrickeSystem) ->
  TauSignedState system ->
  TauSignedState system
tauSignedInversion system (tau-signed-state point multiplicity) =
  tau-signed-state
    (Fricke.fricke system point)
    (SSP.negateMultiplicity multiplicity)

tauSignedInversionInvolutive :
  (system : Fricke.ModularJFrickeSystem) ->
  (state : TauSignedState system) ->
  tauSignedInversion system (tauSignedInversion system state) ≡ state
tauSignedInversionInvolutive system (tau-signed-state point multiplicity)
  rewrite Fricke.frickeInvolutive system point
        | signedNegationInvolutive multiplicity = refl

------------------------------------------------------------------------
-- 4. Existing j-orbit seam interpretation flips exactly under signed inversion.
------------------------------------------------------------------------

negativeSignedInversionBecomesDiverging :
  (n : Nat) ->
  Orbit.seamDynamicsOfMultiplicity
    (SSP.negateMultiplicity (SSP.negativeMultiplicity n))
  ≡ Orbit.divergingSeam
negativeSignedInversionBecomesDiverging n = refl

positiveSignedInversionBecomesConverging :
  (n : Nat) ->
  Orbit.seamDynamicsOfMultiplicity
    (SSP.negateMultiplicity (SSP.positiveMultiplicity n))
  ≡ Orbit.convergingSeam
positiveSignedInversionBecomesConverging n = refl

zeroSignedInversionRemainsIdentity :
  Orbit.seamDynamicsOfMultiplicity
    (SSP.negateMultiplicity SSP.zeroMultiplicity)
  ≡ Orbit.seamIdentity
zeroSignedInversionRemainsIdentity = refl

------------------------------------------------------------------------
-- 5. Existing formulaic 369 modular replication already reuses the signed
-- FRACTRAN seam word.  Retain that exact receipt instead of restating it.
------------------------------------------------------------------------

existingSignedFRACTRANSeamWordReuse :
  Replication.FormulaicReplicationFrontier.signedFRACTRANSeamWordReused
    Replication.canonicalFormulaicReplicationFrontier
  ≡ true
existingSignedFRACTRANSeamWordReuse = refl

------------------------------------------------------------------------
-- 6. Keep the current 6B whole-series donor visible without inventing a tau weld.
------------------------------------------------------------------------

replicabilityFrontier : Replicability.Monster6BReplicabilityFrontier
replicabilityFrontier = Replicability.currentMonster6BReplicabilityFrontier

sameTauResidual : String
sameTauResidual =
  "attach the selected 6B McKay-Thompson modular function to the same literal modular FinePoint/tau carrier used by the Fricke/Hecke/formulaic-j side; only then compare complete replicability and signed-SSP inversion on one same-object tau fibre"

------------------------------------------------------------------------
-- 7. WrongType / same-object firewalls.
------------------------------------------------------------------------

data SignedSSPIsLiteralFrickeAction : Set where
data SharedInvolutionCreatesSameObject : Set where
data SameTauSpellingCreatesSameCarrier : Set where
data ModularTauIsRamanujanTau : Set where
data ReplicabilityCreatesSignedFRACTRANAction : Set where
data ProductInvolutionCreatesMonsterRepresentation : Set where

signedSSPDoesNotBecomeFrickeAction : SignedSSPIsLiteralFrickeAction -> ⊥
signedSSPDoesNotBecomeFrickeAction ()

sharedInvolutionDoesNotCreateSameObject : SharedInvolutionCreatesSameObject -> ⊥
sharedInvolutionDoesNotCreateSameObject ()

sameTauSpellingDoesNotCreateSameCarrier : SameTauSpellingCreatesSameCarrier -> ⊥
sameTauSpellingDoesNotCreateSameCarrier ()

modularTauDoesNotBecomeRamanujanTau : ModularTauIsRamanujanTau -> ⊥
modularTauDoesNotBecomeRamanujanTau ()

replicabilityDoesNotCreateSignedFRACTRANAction :
  ReplicabilityCreatesSignedFRACTRANAction -> ⊥
replicabilityDoesNotCreateSignedFRACTRANAction ()

productInvolutionDoesNotCreateMonsterRepresentation :
  ProductInvolutionCreatesMonsterRepresentation -> ⊥
productInvolutionDoesNotCreateMonsterRepresentation ()

------------------------------------------------------------------------
-- 8. Frontier.
------------------------------------------------------------------------

record Monster369SignedSSPTauInversionBoundary : Set where
  constructor monster-369-signed-ssp-tau-inversion-boundary
  field
    signedNegationInvolutive : Bool
    frickeInvolutionRetained : Bool
    productInversionConstructed : Bool
    coarseTritNegationCompatible : Bool
    jOrbitSignedSeamFlipConstructed : Bool
    signedFRACTRANSeamWordReusedInModularReplication : Bool
    signedSSPIsLiteralFrickeAction : Bool
    modularTauIsRamanujanTau : Bool
    sameTauCarrierFor6BReplicabilityPaid : Bool
    literalMonsterActionWeldPaid : Bool
    nextResidual : String
open Monster369SignedSSPTauInversionBoundary public

canonicalMonster369SignedSSPTauInversionBoundary :
  Monster369SignedSSPTauInversionBoundary
canonicalMonster369SignedSSPTauInversionBoundary =
  monster-369-signed-ssp-tau-inversion-boundary
    true true true true true true
    false false false false
    sameTauResidual

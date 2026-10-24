module DASHI.Biology.IITJFineD4SymplecticMultiplicityObstructionExact where

------------------------------------------------------------------------
-- SOURCE-REUSE / PROOF STATUS
--
-- Earlier D4 irrep owner:
--   DASHI.Biology.TernaryMonsterSymmetryCandidateExact
-- Earlier actual site D4:
--   DASHI.Biology.D4NineCellOrbitCompressionExact
-- Earlier jFine relative carrier:
--   DASHI.Biology.IITJFineFourOneFourS3ZetaGaugeExact
--
-- Finite exact matrix completion/obstruction:
--   scripts/iit_jfine_d4_symplectic_obstruction_audit.py
--
-- This Agda module proves the CONTRADICTION in each necessary
-- multiplicity/parity case. It does NOT prove the external prerequisite:
--   a nondegenerate chi-valued alternating form on the full source
--   F3[D4]-module implies the corresponding multiplicity condition.
-- That Maschke/self-duality lemma and the literal matrix interpretation
-- remain an explicit future Agda kernel obligation.
--
-- No actual Monster 3B, 6.Suz, or physical mechanism is identified.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as D4

-- Remove the fixed centre A1 from the original 9-cell representation.
-- Original 3 A1 + B1 + B2 + 2 E becomes 2 A1 + B1 + B2 + 2 E.
sourceShellMultiplicity : D4.D4IrrepKind → Nat
sourceShellMultiplicity D4.A1 = 2
sourceShellMultiplicity D4.A2 = 0
sourceShellMultiplicity D4.B1 = 1
sourceShellMultiplicity D4.B2 = 1
sourceShellMultiplicity D4.E2 = 2

sourceShellDimension :
  sourceShellMultiplicity D4.A1 +
  sourceShellMultiplicity D4.A2 +
  sourceShellMultiplicity D4.B1 +
  sourceShellMultiplicity D4.B2 +
  2 * sourceShellMultiplicity D4.E2 ≡ 8
sourceShellDimension = refl

sourceNineRecoversCentre :
  sourceShellMultiplicity D4.A1 + 1
  ≡ D4.rawNineMultiplicity D4.A1
sourceNineRecoversCentre = refl

-- These are the four D4 -> F3^× = {+1,-1} central multipliers.
-- Their character signs on quarter-turn r and vertical mirror m are:
-- trivial (+,+), reflectionSign (+,-), rotationSign (-,+),
-- combinedSign (-,-).
data CentreMultiplier : Set where
  trivial reflectionSign rotationSign combinedSign : CentreMultiplier

-- Distinct proof objects: odd 1D multiplicity versus mismatched
-- chi-dual character multiplicity. Not an assumed equality of chars.
data EvenMultiplicity : Nat → Set where
  evenZero : EvenMultiplicity zero
  evenStep : ∀ {n} → EvenMultiplicity n →
    EvenMultiplicity (suc (suc n))

data MatchedMultiplicity : Nat → Nat → Set where
  matched : ∀ {n} → MatchedMultiplicity n n

-- The standard semisimple symplectic-form criterion implies one of:
--   trivial: B1 occurs with even multiplicity;
--   chi != trivial: number of A1 copies equals number of chi copies.
-- Here these are NECESSARY-CERTIFICATE TYPES. Their implication from
-- a concrete invariant full-rank 8x8 form is NOT proved in this module.
NecessaryPairingMultiplicity : CentreMultiplier → Set
NecessaryPairingMultiplicity trivial =
  EvenMultiplicity (sourceShellMultiplicity D4.B1)
NecessaryPairingMultiplicity reflectionSign =
  MatchedMultiplicity
    (sourceShellMultiplicity D4.A1)
    (sourceShellMultiplicity D4.A2)
NecessaryPairingMultiplicity rotationSign =
  MatchedMultiplicity
    (sourceShellMultiplicity D4.A1)
    (sourceShellMultiplicity D4.B1)
NecessaryPairingMultiplicity combinedSign =
  MatchedMultiplicity
    (sourceShellMultiplicity D4.A1)
    (sourceShellMultiplicity D4.B2)

-- Concrete elimination: the four required types have no constructors
-- at their instantiated indices (Even 1, Match 2 0, Match 2 1).
noCompatibleNecessaryMultiplicity :
  (chi : CentreMultiplier) → NecessaryPairingMultiplicity chi → ⊥
noCompatibleNecessaryMultiplicity trivial ()
noCompatibleNecessaryMultiplicity reflectionSign ()
noCompatibleNecessaryMultiplicity rotationSign ()
noCompatibleNecessaryMultiplicity combinedSign ()

-- Minimum two-dimensional symplectic repair is a separately verified
-- FINITE MODEL: add B1+B2 to pair singleton B1 and B2 modes.
sourceWithB1B2Dimension : 8 + 1 + 1 ≡ 10
sourceWithB1B2Dimension = refl

sourceWithH6HyperbolicPairDimension : 10 + 2 ≡ 12
sourceWithH6HyperbolicPairDimension = refl

-- The D4-stable source plane has commutator rank six in the new model;
-- the dimension/character numbers below are numerical consequences,
-- NOT proof of the actual source matrix ranks inside this Agda module.
D4SourceRestrictedHeisenbergOrder : 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3 ≡ 19683
D4SourceRestrictedHeisenbergOrder = refl

D4StableModelCentreOrder : 3 * 3 * 3 ≡ 27
D4StableModelCentreOrder = refl

nonlinearDegreeSquareSpectrumDistinguishesModels :
  6561 + 18 * (27 * 27) ≡ 6561 + 2 * (81 * 81)
nonlinearDegreeSquareSpectrumDistinguishesModels = refl

record KernelAdmissionBoundary : Set where
  constructor kernelAdmissionBoundary
  field
    existingD4IrrepSourceReused : Bool
    allNecessaryMultiplicityCasesEliminated : Bool
    fullSourceMatrixD4FormRankBoundKernelProved : Bool
    repairedFormAndH6GroupLawKernelProved : Bool
    actualMonsterNormalizerIntertwinerConstructed : Bool

currentBoundary : KernelAdmissionBoundary
currentBoundary = kernelAdmissionBoundary true true false false false

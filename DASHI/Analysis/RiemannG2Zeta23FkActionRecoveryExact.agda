module DASHI.Analysis.RiemannG2Zeta23FkActionRecoveryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LITERAL ZETA23 SOURCE ACTION RETURN
--
-- Inspected checked source:
--   Zeta23/Zeta23/Defs.lean
--
-- It literally defines
--
--   phiHat z = paperFT (fun u => (phi u : C)) z
--   fk k u   = (phi u : C) * exp (-(i * tau k * u)).
--
-- Therefore the target/frequency action itself is already source-owned on the
-- concrete function carrier R -> C.  We must not continue searching for an
-- abstract modulation operation.
--
-- IMPORTANT trust boundary: the Defs.lean docstring also states
--
--   h_{f_k}(z) = phiHat(z - tau_k),
--
-- but the inspected package does not expose a theorem declaration with that
-- identity.  A source comment is not promoted to a checked theorem here.
-- Consequently the transform-shift equality remains a proof-relevant recovery
-- leaf, as does exact identification of this source function carrier with the
-- canonical Gamma/Mellin Test selected by the Agda analytic substrate.
------------------------------------------------------------------------

record Zeta23FkSourceReturn : Set where
  constructor zeta23-fk-source-return
  field
    sourcePackage : String
    defsOwner : String
    fourierOwner : String

    sourceFunctionCarrier : String
    sourceTargetActionDefinition : String
    sourcePhiHatDefinition : String

    fkDefinitionOwned : Bool
    fkDefinitionOwnedIsTrue : fkDefinitionOwned ≡ true

    phiHatDefinitionOwned : Bool
    phiHatDefinitionOwnedIsTrue : phiHatDefinitionOwned ≡ true

    realEvenConjugationTheoremOwned : Bool
    realEvenConjugationTheoremOwnedIsTrue :
      realEvenConjugationTheoremOwned ≡ true

    fkTransformShiftAppearsAsCheckedTheoremInInspectedPackage : Bool
    fkTransformShiftAppearsAsCheckedTheoremInInspectedPackageIsFalse :
      fkTransformShiftAppearsAsCheckedTheoremInInspectedPackage ≡ false

    sourceCarrierIdentifiedWithCanonicalMellinTestInAgda : Bool
    sourceCarrierIdentifiedWithCanonicalMellinTestInAgdaIsFalse :
      sourceCarrierIdentifiedWithCanonicalMellinTestInAgda ≡ false

    leanProofTransportedIntoAgda : Bool
    leanProofTransportedIntoAgdaIsFalse : leanProofTransportedIntoAgda ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalZeta23FkSourceReturn : Zeta23FkSourceReturn
canonicalZeta23FkSourceReturn =
  zeta23-fk-source-return
    "attached Aristotle/Zeta23Bridge checked-source package"
    "Zeta23/Zeta23/Defs.lean"
    "Zeta23/Zeta23/Taper/Fourier.lean"
    "Real -> Complex"
    "fk k u = phi(u) * exp(-(i * tau_k * u))"
    "phiHat z = paperFT (fun u => (phi u : Complex)) z"
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "The literal source target-character multiplication action is already recovered: stop searching for another H_A modulation operation. What remains is exact same-object attachment of the source function/test carrier to the canonical Gamma/Mellin Test plus proof-relevant admissibility and transform/spectral shift equalities. The documented h_fk(z)=phiHat(z-tau_k) sentence is not counted as a checked theorem until a theorem declaration or proof is recovered."

------------------------------------------------------------------------
-- Search pruning.
------------------------------------------------------------------------

data HARecoveryAction : Set where
  searchForAnyModulationOperation
  rebuildCharacterMultiplication
  recoverSourceCarrierToMellinIdentity
  recoverFkAdmissibilityClosure
  recoverFkTransformShiftProof
  identifyShiftWithSameExplicitFormula
  compileThroughProofRelevantHA
  : HARecoveryAction

HARelevant : HARecoveryAction -> Set
HARelevant searchForAnyModulationOperation = ⊥
HARelevant rebuildCharacterMultiplication = ⊥
HARelevant recoverSourceCarrierToMellinIdentity = ⊤
HARelevant recoverFkAdmissibilityClosure = ⊤
HARelevant recoverFkTransformShiftProof = ⊤
HARelevant identifyShiftWithSameExplicitFormula = ⊤
HARelevant compileThroughProofRelevantHA = ⊤

modulationSearchPruned : HARelevant searchForAnyModulationOperation -> ⊥
modulationSearchPruned x = x

characterMultiplicationRebuildPruned :
  HARelevant rebuildCharacterMultiplication -> ⊥
characterMultiplicationRebuildPruned x = x

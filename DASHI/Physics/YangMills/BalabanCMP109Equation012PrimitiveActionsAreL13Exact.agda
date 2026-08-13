module DASHI.Physics.YangMills.BalabanCMP109Equation012PrimitiveActionsAreL13Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- The printed equation-(0.12) derivative is identified leaf-by-leaf rather
-- than by one terminal matrix assertion.  Each equality is pointwise on the
-- same direction vector.  Transitivity then forces the printed DAG action to
-- equal the already-owned L13 action, preventing sign/orientation drift at a
-- primitive boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record Equation012PrimitiveActionChain
    (Direction Output : Set) : Set₁ where
  field
    sourceContourAction : Direction → Output
    crossingRelativeProductAction : Direction → Output
    targetReverseAverageAction : Direction → Output
    coarseInverseAction : Direction → Output
    principalLogAction : Direction → Output
    finiteBlockAverageAction : Direction → Output
    exponentialAction : Direction → Output
    endpointProductAction : Direction → Output
    printedDAGAction : Direction → Output
    l13Action : Direction → Output

    sourceToCrossing : ∀ h →
      sourceContourAction h ≡ crossingRelativeProductAction h
    crossingToTarget : ∀ h →
      crossingRelativeProductAction h ≡ targetReverseAverageAction h
    targetToInverse : ∀ h →
      targetReverseAverageAction h ≡ coarseInverseAction h
    inverseToLog : ∀ h →
      coarseInverseAction h ≡ principalLogAction h
    logToBlock : ∀ h →
      principalLogAction h ≡ finiteBlockAverageAction h
    blockToExp : ∀ h →
      finiteBlockAverageAction h ≡ exponentialAction h
    expToEndpoint : ∀ h →
      exponentialAction h ≡ endpointProductAction h
    endpointIsPrintedDAG : ∀ h →
      endpointProductAction h ≡ printedDAGAction h
    printedDAGIsL13 : ∀ h →
      printedDAGAction h ≡ l13Action h

open Equation012PrimitiveActionChain public

equation012PrimitiveActionsForceL13 :
  ∀ {Direction Output}
    (chain : Equation012PrimitiveActionChain Direction Output)
    h →
  sourceContourAction chain h ≡ l13Action chain h
equation012PrimitiveActionsForceL13 chain h =
  trans (sourceToCrossing chain h)
  (trans (crossingToTarget chain h)
  (trans (targetToInverse chain h)
  (trans (inverseToLog chain h)
  (trans (logToBlock chain h)
  (trans (blockToExp chain h)
  (trans (expToEndpoint chain h)
  (trans (endpointIsPrintedDAG chain h)
         (printedDAGIsL13 chain h))))))))

record PrintedEquation012PrimitiveAuthority
    (Direction Output : Set) : Set₁ where
  field
    chain : Equation012PrimitiveActionChain Direction Output
    printedDerivativeAction : Direction → Output
    printedDerivativeIsSourceLeaf : ∀ h →
      printedDerivativeAction h ≡ sourceContourAction chain h

open PrintedEquation012PrimitiveAuthority public

printedEquation012DerivativeIsL13Pointwise :
  ∀ {Direction Output}
    (authority : PrintedEquation012PrimitiveAuthority Direction Output)
    h →
  printedDerivativeAction authority h
    ≡ l13Action (chain authority) h
printedEquation012DerivativeIsL13Pointwise authority h =
  trans
    (printedDerivativeIsSourceLeaf authority h)
    (equation012PrimitiveActionsForceL13 (chain authority) h)

cmp109Equation012PrimitiveActionChainLevel : ProofLevel
cmp109Equation012PrimitiveActionChainLevel = machineChecked

cmp109Equation012PrintedToL13PointwiseLevel : ProofLevel
cmp109Equation012PrintedToL13PointwiseLevel = machineChecked

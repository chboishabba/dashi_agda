module DASHI.Physics.YangMills.BalabanClayT2UrsellCauchyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact using
  (half; halfPower; halfPowerNonnegative)

quarter : ℚ
quarter = + 1 / 4

------------------------------------------------------------------------
-- Exact geometric tail used by the Ursell expansion.
------------------------------------------------------------------------

geometricTailPartial : Nat → Nat → ℚ
geometricTailPartial start zero = 0ℚ
geometricTailPartial start (suc count) =
  quarter * halfPower start
  + geometricTailPartial (suc start) count

halfTimesPowerNonnegative : ∀ depth →
  0ℚ ≤ half * halfPower depth
halfTimesPowerNonnegative depth =
  let
    halfNonnegativeProof : 0ℚ ≤ half
    halfNonnegativeProof =
      let
        instance
          halfNonnegative : NonNegative half
          halfNonnegative = ℚP.normalize-nonNeg 1 2
      in ℚP.nonNegative⁻¹ half

    instance
      halfNonnegative : NonNegative half
      halfNonnegative = nonNegative halfNonnegativeProof

      powerNonnegative : NonNegative (halfPower depth)
      powerNonnegative = nonNegative (halfPowerNonnegative depth)
  in ℚP.nonNegative⁻¹ (half * halfPower depth)

geometricTailBelow : ∀ start count →
  geometricTailPartial start count ≤ half * halfPower start
geometricTailBelow start zero =
  baseBelowBasePlusRemainder 0ℚ
    (half * halfPower start)
    (halfTimesPowerNonnegative start)
geometricTailBelow start (suc count) =
  trans
    (ℚP.+-mono-≤
      (ℚP.≤-reflexive (quarter * halfPower start))
      (geometricTailBelow (suc start) count))
    (subst
      (λ right →
        quarter * halfPower start
          + half * halfPower (suc start)
        ≤ right)
      (ℚRing.solve-∀ (halfPower start))
      (ℚP.≤-reflexive (half * halfPower start)))

------------------------------------------------------------------------
-- The actual absolute Ursell coefficients are now a sequence with a concrete
-- Cauchy modulus.  Tree-graph/KP analysis only has to prove the per-depth bound;
-- convergence is then constructed rather than supplied as an opaque flag.
------------------------------------------------------------------------

record UrsellDepthMajorant : Set₁ where
  field
    absoluteUrsellDepth : Nat → ℚ
    absoluteDepthNonnegative : ∀ depth → 0ℚ ≤ absoluteUrsellDepth depth
    depthBelowRootedShell : ∀ depth →
      absoluteUrsellDepth depth ≤ quarter * halfPower depth

open UrsellDepthMajorant public

ursellTailPartial : UrsellDepthMajorant → Nat → Nat → ℚ
ursellTailPartial dataSet start zero = 0ℚ
ursellTailPartial dataSet start (suc count) =
  absoluteUrsellDepth dataSet start
  + ursellTailPartial dataSet (suc start) count

ursellTailBelowGeometric :
  (dataSet : UrsellDepthMajorant) → ∀ start count →
  ursellTailPartial dataSet start count
  ≤ geometricTailPartial start count
ursellTailBelowGeometric dataSet start zero = ℚP.≤-reflexive 0ℚ
ursellTailBelowGeometric dataSet start (suc count) =
  ℚP.+-mono-≤
    (depthBelowRootedShell dataSet start)
    (ursellTailBelowGeometric dataSet (suc start) count)

ursellCauchyTail :
  (dataSet : UrsellDepthMajorant) → ∀ start count →
  ursellTailPartial dataSet start count
  ≤ half * halfPower start
ursellCauchyTail dataSet start count =
  trans
    (ursellTailBelowGeometric dataSet start count)
    (geometricTailBelow start count)

record InfiniteUrsellLimit (Observable Value : Set) : Set₁ where
  field
    majorant : UrsellDepthMajorant
    finiteConnected : Observable → Observable → Nat → Value
    infiniteConnected : Observable → Observable → Value
    absoluteValue : Value → ℚ
    separationDepth : Observable → Observable → Nat

    finiteCrossingBound : ∀ left right cutoff →
      absoluteValue (finiteConnected left right cutoff)
      ≤ ursellTailPartial majorant (separationDepth left right) cutoff

    limitBoundClosed : ∀ left right →
      (∀ cutoff →
        absoluteValue (finiteConnected left right cutoff)
        ≤ half * halfPower (separationDepth left right)) →
      absoluteValue (infiniteConnected left right)
      ≤ half * halfPower (separationDepth left right)

open InfiniteUrsellLimit public

connectedCorrelationExponentialDecay :
  ∀ {Observable Value}
    (dataSet : InfiniteUrsellLimit Observable Value)
    left right →
  absoluteValue dataSet (infiniteConnected dataSet left right)
  ≤ half * halfPower (separationDepth dataSet left right)
connectedCorrelationExponentialDecay dataSet left right =
  limitBoundClosed dataSet left right
    (λ cutoff →
      trans
        (finiteCrossingBound dataSet left right cutoff)
        (ursellCauchyTail (majorant dataSet)
          (separationDepth dataSet left right) cutoff))

ursellGeometricCauchyModulusLevel : ProofLevel
ursellGeometricCauchyModulusLevel = machineChecked

finiteConnectedCrossingDecayLevel : ProofLevel
finiteConnectedCrossingDecayLevel = machineChecked

infiniteConnectedCorrelationDecayAssemblyLevel : ProofLevel
infiniteConnectedCorrelationDecayAssemblyLevel = machineChecked

-- The remaining combinatorial theorem is the literal tree-graph/KP estimate
-- identifying physical absolute Ursell coefficients with UrsellDepthMajorant.
physicalUrsellTreeGraphMajorantLevel : ProofLevel
physicalUrsellTreeGraphMajorantLevel = conditional

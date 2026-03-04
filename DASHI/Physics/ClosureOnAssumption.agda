module DASHI.Physics.ClosureOnAssumption where

open import Data.Unit using (⊤)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.QuadraticPolarization public hiding (b2-trit)
open import DASHI.Physics.IndefiniteMaskQuadratic public using
  (Sign; plus; minus; signℤ; toℤTrit; sqℤ; Qσ; dotσ; B2σ; B2σ≡2dotσ)
open import DASHI.Physics.SignatureFromMask public
open import DASHI.Physics.MaskedQuadraticRenormalization public
open import DASHI.Physics.MaskedConeStructure public
open import DASHI.Physics.RealConeStructureInstance public
open import DASHI.Physics.RealCausalStructureInstance public
open import DASHI.Physics.OrbitFingerprintAssumptions public
open import DASHI.Physics.OrbitFingerprintInstance public
open import DASHI.Physics.OrbitShellPredicate public
open import DASHI.Physics.MaskedClosureKit public
open import DASHI.Physics.TernaryRealInstanceShift
open import DASHI.Physics.DimensionBoundAssumptions public

open import DASHI.Physics.BianchiEinsteinAssumptions public
open import DASHI.Physics.CliffordAssumptions public
open import DASHI.Physics.SpinAssumptions public
open import DASHI.Physics.CCRAssumptions public
open import DASHI.Physics.UnitaryLiftAssumptions public
open import DASHI.Physics.StandardModelAssumptions public using (StandardModelGate)

record PhysicsClosureOnAssumption : Set₁ where
  field
    dimBound : DimensionBoundGate
    einstein : ∀ {V : Set} (M : DiscreteManifoldLike V) → EinsteinGate M
    clifford : ∀ {VS : VectorSpace} {BF : BilinearForm VS} (C : CliffordData VS BF) → CliffordGate C
    spin     : ∀ (A : SpinAxioms) (p q : Nat) → DoubleCover (spinGroup A p q) (soGroup A p q)
    ccr      : ∀ (A : OperatorAlgebra) → CCRGate A
    unitary  : UnitaryLift
    sm       : StandardModelGate

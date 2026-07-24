module DASHI.Physics.YangMills.BalabanSU2TransportPathNormBound where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2TransportTelescopingExact

------------------------------------------------------------------------
-- Ordered path estimate from the exact SU(2) telescoping identity.
--
-- The group-algebra part is already computed in
-- BalabanSU2TransportTelescopingExact.  Here triangle inequality and adjoint
-- isometry are used once, by list induction, to expose the literal path-length
-- factor.  Only the one-link small-radius bound remains model-analytic.
------------------------------------------------------------------------

record SU2TransportNormAuthority (Bound : Set) : Set₁ where
  field
    zeroBound : Bound
    addBound : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    reflexive : ∀ {value} → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (addBound left right) (addBound leftUpper rightUpper)

    norm : Vec3R → Bound
    normZero : norm zeroV ≡ zeroBound
    normTriangle : ∀ left right →
      LessEqual (norm (addV left right))
        (addBound (norm left) (norm right))
    rotationIsometry : ∀ q vector → norm (rotate q vector) ≡ norm vector

    oneLinkBudget : Vec3R → Bound
    oneLinkSmallRadiusBound : ∀ q vector →
      LessEqual
        (norm (subV (rotate q vector) vector))
        (oneLinkBudget vector)

    natScale : Nat → Bound → Bound
    natScaleZero : ∀ value → natScale zero value ≡ zeroBound
    natScaleSuc : ∀ n value →
      natScale (suc n) value ≡ addBound (natScale n value) value

open SU2TransportNormAuthority public

pathLength : ∀ {A : Set} → List A → Nat
pathLength [] = zero
pathLength (x ∷ xs) = suc (pathLength xs)

pathBudget :
  ∀ {Bound} → SU2TransportNormAuthority Bound →
  List AdjointCoordinates → Vec3R → Bound
pathBudget authority [] vector = zeroBound authority
pathBudget authority (q ∷ path) vector =
  addBound authority
    (pathBudget authority path vector)
    (oneLinkBudget authority vector)

transportRemainderNormBound :
  ∀ {Bound} (authority : SU2TransportNormAuthority Bound) path vector →
  LessEqual authority
    (norm authority (transportRemainder path vector))
    (pathBudget authority path vector)
transportRemainderNormBound authority [] vector
  rewrite normZero authority =
  reflexive authority
transportRemainderNormBound authority (q ∷ path) vector
  rewrite rotationIsometry authority q (transportRemainder path vector) =
  transitive authority
    (normTriangle authority
      (rotate q (transportRemainder path vector))
      (subV (rotate q vector) vector))
    (addMonotone authority
      (transportRemainderNormBound authority path vector)
      (oneLinkSmallRadiusBound authority q vector))

transportDisplacementNormBound :
  ∀ {Bound} (authority : SU2TransportNormAuthority Bound) path vector →
  LessEqual authority
    (norm authority (subV (transport path vector) vector))
    (pathBudget authority path vector)
transportDisplacementNormBound authority path vector
  rewrite sym (transportRemainderExact path vector) =
  transportRemainderNormBound authority path vector

pathBudgetEqualsLengthScale :
  ∀ {Bound} (authority : SU2TransportNormAuthority Bound) path vector →
  pathBudget authority path vector
  ≡ natScale authority (pathLength path) (oneLinkBudget authority vector)
pathBudgetEqualsLengthScale authority [] vector =
  sym (natScaleZero authority (oneLinkBudget authority vector))
pathBudgetEqualsLengthScale authority (q ∷ path) vector =
  trans
    (cong
      (λ previous →
        addBound authority previous (oneLinkBudget authority vector))
      (pathBudgetEqualsLengthScale authority path vector))
    (sym
      (natScaleSuc authority (pathLength path)
        (oneLinkBudget authority vector)))

transportPathLengthNormBound :
  ∀ {Bound} (authority : SU2TransportNormAuthority Bound) path vector →
  LessEqual authority
    (norm authority (subV (transport path vector) vector))
    (natScale authority (pathLength path) (oneLinkBudget authority vector))
transportPathLengthNormBound authority path vector =
  let
    raw = transportDisplacementNormBound authority path vector
  in
  substRight raw
  where
    substRight :
      LessEqual authority
        (norm authority (subV (transport path vector) vector))
        (pathBudget authority path vector) →
      LessEqual authority
        (norm authority (subV (transport path vector) vector))
        (natScale authority (pathLength path) (oneLinkBudget authority vector))
    substRight proof
      rewrite pathBudgetEqualsLengthScale authority path vector = proof

su2TransportPathNormAssemblyLevel : ProofLevel
su2TransportPathNormAssemblyLevel = machineChecked

su2OneLinkSmallRadiusBoundLevel : ProofLevel
su2OneLinkSmallRadiusBoundLevel = conditional

su2PathLengthFactorLevel : ProofLevel
su2PathLengthFactorLevel = machineChecked

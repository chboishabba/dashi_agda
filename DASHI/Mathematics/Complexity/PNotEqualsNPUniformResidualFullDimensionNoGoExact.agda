module DASHI.Mathematics.Complexity.PNotEqualsNPUniformResidualFullDimensionNoGoExact where

------------------------------------------------------------------------
-- UNIFORMITY DOES NOT FORCE LOW-DIMENSIONAL LOCAL RESIDUALS
--
-- Candidate P11 hypothesis under audit:
--
--   perhaps one fixed uniform program generating C_n forces the family of
--   self-evaluation residuals into a low-dimensional algebraic subspace.
--
-- This owner gives a concrete no-go for UNIFORMITY ALONE.
--
-- We construct a uniform NOT-chain:
--
--   x -> not -> not -> ... -> not
--
-- Every gate lies on the unique path to the output; there are no dead gates.
-- For an arbitrary claimed gate-value witness y_1,...,y_n define local residual
--
--   e_i = y_i XOR (NOT y_(i-1)),
--
-- with y_0 = input.
--
-- Main theorem:
--
--   for every desired residual vector e : Bool^n there exists a gate-value
--   witness y : Bool^n whose local residual vector is exactly e.
--
-- Hence the residual family is all of Bool^n.  In particular it contains every
-- unit vector and cannot be forced into any proper coordinate subspace merely
-- from the fact that the circuit family is uniformly generated.
--
-- The generator itself is trivial recursive syntax.  Therefore any useful
-- low-dimensional theorem for SAT self-evaluation must exploit structure
-- stronger than uniformity and polynomial description length alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPBooleanResidualFingerprintExact as Fingerprint

------------------------------------------------------------------------
-- Uniform concrete NOT-chain.
------------------------------------------------------------------------

notChainProgram :
  (depth : Nat) →
  Circuit.GateProgram (suc zero) depth
notChainProgram zero =
  Circuit.noGates
notChainProgram (suc zero) =
  Circuit.appendGate
    Circuit.noGates
    (Circuit.notGate
      (Circuit.inputWire fzero))
notChainProgram (suc (suc depth)) =
  Circuit.appendGate
    (notChainProgram (suc depth))
    (Circuit.notGate
      (Circuit.gateWire fzero))

notChainCircuit :
  (depth : Nat) →
  Circuit.ConcreteBooleanCircuit (suc zero)
notChainCircuit zero =
  Circuit.concrete-boolean-circuit
    zero
    Circuit.noGates
    (Circuit.inputWire fzero)
notChainCircuit (suc depth) =
  Circuit.concrete-boolean-circuit
    (suc depth)
    (notChainProgram (suc depth))
    (Circuit.gateWire fzero)

notChainGateCount :
  (depth : Nat) →
  Circuit.circuitSize (notChainCircuit depth)
  ≡ depth
notChainGateCount depth =
  refl

------------------------------------------------------------------------
-- Boolean residual algebra.
------------------------------------------------------------------------

xorBool : Bool → Bool → Bool
xorBool =
  Fingerprint.xorBool

notBool : Bool → Bool
notBool =
  Cook.notBool

xorSelfFalse :
  (value : Bool) →
  xorBool value value ≡ false
xorSelfFalse false =
  refl
xorSelfFalse true =
  refl

xorWithFalseRight :
  (value : Bool) →
  xorBool value false ≡ value
xorWithFalseRight false =
  refl
xorWithFalseRight true =
  refl

chooseClaimedValue :
  Bool →
  Bool →
  Bool
chooseClaimedValue expected residual =
  xorBool expected residual

chooseClaimedValueResidual :
  (expected residual : Bool) →
  xorBool
    (chooseClaimedValue expected residual)
    expected
  ≡ residual
chooseClaimedValueResidual false false =
  refl
chooseClaimedValueResidual false true =
  refl
chooseClaimedValueResidual true false =
  refl
chooseClaimedValueResidual true true =
  refl

------------------------------------------------------------------------
-- Residuals of a claimed gate-value witness.
--
-- Gate values are stored in chronological order:
--   y_1 :: y_2 :: ... :: y_n.
------------------------------------------------------------------------

notChainResiduals :
  ∀ {depth : Nat} →
  Bool →
  Vec Bool depth →
  Vec Bool depth
notChainResiduals {zero} input [] =
  []
notChainResiduals {suc depth} input (claimed ∷ rest) =
  xorBool claimed (notBool input)
  ∷
  notChainResiduals claimed rest

------------------------------------------------------------------------
-- Given ANY desired residual vector, synthesize claimed gate values realizing
-- it exactly.
------------------------------------------------------------------------

realizeResiduals :
  ∀ {depth : Nat} →
  Bool →
  Vec Bool depth →
  Vec Bool depth
realizeResiduals {zero} input [] =
  []
realizeResiduals {suc depth} input (residual ∷ residuals) =
  claimed
  ∷
  realizeResiduals claimed residuals
  where
    claimed : Bool
    claimed =
      chooseClaimedValue
        (notBool input)
        residual

realizeResidualsExact :
  ∀ {depth : Nat}
    (input : Bool)
    (desired : Vec Bool depth) →
  notChainResiduals
    input
    (realizeResiduals input desired)
  ≡ desired
realizeResidualsExact {zero} input [] =
  refl
realizeResidualsExact {suc depth}
    input (residual ∷ residuals)
    rewrite
      chooseClaimedValueResidual
        (notBool input)
        residual
      |
      realizeResidualsExact
        (chooseClaimedValue
          (notBool input)
          residual)
        residuals =
  refl

------------------------------------------------------------------------
-- Surjectivity: the local residual map is onto Bool^n.
------------------------------------------------------------------------

ResidualWitness :
  ∀ {depth : Nat} →
  Bool →
  Vec Bool depth →
  Set
ResidualWitness {depth} input desired =
  Σ (Vec Bool depth) λ claimedValues →
    notChainResiduals input claimedValues
    ≡ desired

everyResidualVectorIsRealizable :
  ∀ {depth : Nat}
    (input : Bool)
    (desired : Vec Bool depth) →
  ResidualWitness input desired
everyResidualVectorIsRealizable input desired =
  realizeResiduals input desired
  ,
  realizeResidualsExact input desired

------------------------------------------------------------------------
-- Unit residual vectors are therefore all present.
------------------------------------------------------------------------

unitResidual :
  ∀ {depth : Nat} →
  Fin depth →
  Vec Bool depth
unitResidual {suc depth} fzero =
  true ∷ Fingerprint.zeroWeights depth
unitResidual {suc depth} (fsuc index) =
  false ∷ unitResidual index

everyUnitResidualIsRealizable :
  ∀ {depth : Nat}
    (input : Bool)
    (index : Fin depth) →
  ResidualWitness input (unitResidual index)
everyUnitResidualIsRealizable input index =
  everyResidualVectorIsRealizable
    input
    (unitResidual index)

------------------------------------------------------------------------
-- Coordinate-subspace no-go.
--
-- Any theorem claiming one fixed coordinate is ALWAYS zero across all residual
-- witnesses is false, because the unit residual at that coordinate is
-- realizable.
------------------------------------------------------------------------

coordinate :
  ∀ {depth : Nat} →
  Fin depth →
  Vec Bool depth →
  Bool
coordinate =
  Circuit.lookupVec

unitResidualAtOwnCoordinate :
  ∀ {depth : Nat}
    (index : Fin depth) →
  coordinate index (unitResidual index)
  ≡ true
unitResidualAtOwnCoordinate fzero =
  refl
unitResidualAtOwnCoordinate (fsuc index) =
  unitResidualAtOwnCoordinate index

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

noCoordinateIsUniformlyZero :
  ∀ {depth : Nat}
    (input : Bool)
    (index : Fin depth) →
  ((claimedValues : Vec Bool depth) →
    coordinate index
      (notChainResiduals input claimedValues)
    ≡ false) →
  ⊥
noCoordinateIsUniformlyZero
    input index alwaysZero
    with everyUnitResidualIsRealizable input index
... | claimedValues , exact =
  falseNotTrue
    (transitive
      (symmetry
        (alwaysZero claimedValues))
      (transitive
        (cong (coordinate index) exact)
        (unitResidualAtOwnCoordinate index)))
  where
    symmetry :
      ∀ {A : Set} {left right : A} →
      left ≡ right →
      right ≡ left
    symmetry refl =
      refl

    transitive :
      ∀ {A : Set} {left middle right : A} →
      left ≡ middle →
      middle ≡ right →
      left ≡ right
    transitive refl refl =
      refl

------------------------------------------------------------------------
-- Research consequence.
--
-- Uniform generation by a tiny fixed schema does not imply a low-dimensional
-- local-residual family.  This NOT-chain is uniformly generated, every gate is
-- output-relevant, yet the witness-residual map is surjective onto Bool^n.
--
-- Therefore P11 must exploit a stronger feature of the SPECIAL diagonal
-- self-evaluation instance: e.g. a semantic restriction on admissible
-- witnesses, an algebraic relation induced by self-instantiation, or a
-- uniform-family theorem not shared by arbitrary uniformly generated circuits.
------------------------------------------------------------------------

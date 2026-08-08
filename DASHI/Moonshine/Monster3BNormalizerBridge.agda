module DASHI.Moonshine.Monster3BNormalizerBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact arithmetic owned by the 3B restriction discussion.
------------------------------------------------------------------------

heisenbergDegree : Nat
heisenbergDegree = 729

naturalSuzukiDegree : Nat
naturalSuzukiDegree = 12

symmetricSquareDualDegree : Nat
symmetricSquareDualDegree = 78

multiplicityDegree : Nat
multiplicityDegree = naturalSuzukiDegree + symmetricSquareDualDegree

nontrivialPhaseDegree : Nat
nontrivialPhaseDegree = heisenbergDegree * multiplicityDegree

invariantPhaseDegree : Nat
invariantPhaseDegree = 65663

characterResidual : Nat
characterResidual = 53

multiplicity-degree-is-90 : multiplicityDegree ≡ 90
multiplicity-degree-is-90 = refl

heisenberg-times-twelve : heisenbergDegree * naturalSuzukiDegree ≡ 8748
heisenberg-times-twelve = refl

heisenberg-times-seventy-eight :
  heisenbergDegree * symmetricSquareDualDegree ≡ 56862
heisenberg-times-seventy-eight = refl

nontrivial-phase-degree-is-65610 : nontrivialPhaseDegree ≡ 65610
nontrivial-phase-degree-is-65610 = refl

phase-sum-dimension :
  invariantPhaseDegree + nontrivialPhaseDegree + nontrivialPhaseDegree ≡ 196883
phase-sum-dimension = refl

invariant-excess :
  nontrivialPhaseDegree + characterResidual ≡ invariantPhaseDegree
invariant-excess = refl

------------------------------------------------------------------------
-- Typed epistemic boundary.
--
-- The arithmetic above is checked.  The actual CTblLib restriction and any
-- identification of concrete MN3B irreducibles are external computational
-- evidence until imported through a checked certificate.
------------------------------------------------------------------------

record NormalizerRestrictionBoundary : Set where
  constructor mkBoundary
  field
    sourceTable : String
    targetTable : String
    externalComputationRequired : Bool
    externalComputationRequiredIsTrue :
      externalComputationRequired ≡ true
    actualConstituentIdentificationPromoted : Bool
    explicitMonsterBasisAvailable : Bool
    actualConstituentIdentificationPromotedIsFalse :
      actualConstituentIdentificationPromoted ≡ false
    explicitMonsterBasisAvailableIsFalse :
      explicitMonsterBasisAvailable ≡ false

normalizerRestrictionBoundary : NormalizerRestrictionBoundary
normalizerRestrictionBoundary =
  mkBoundary
    "M"
    "MN3B"
    true
    refl
    false
    false
    refl
    refl

------------------------------------------------------------------------
-- Model-level carrier roles.  These are deliberately not equalities of
-- actual Monster modules.
------------------------------------------------------------------------

record CandidateTensorReading : Set where
  constructor candidateTensorReading
  field
    heisenbergCarrierDimension : Nat
    multiplicityCarrierDimension : Nat
    totalDimension : Nat
    interpretation : String
    actualNormalizerEquivalenceProved : Bool
    actualNormalizerEquivalenceProvedIsFalse :
      actualNormalizerEquivalenceProved ≡ false

candidate65610TensorReading : CandidateTensorReading
candidate65610TensorReading =
  candidateTensorReading
    heisenbergDegree
    multiplicityDegree
    nontrivialPhaseDegree
    "candidate 3^6 Heisenberg carrier tensored with the documented 12 plus 78 multiplicity carrier"
    false
    refl

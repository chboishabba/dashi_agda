module DASHI.Physics.YangMills.BalabanClayGate4LocalizedExponentiationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- Project Euclid stable identifier: euclid:cmp/1104161193.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
------------------------------------------------------------------------

record LocalizedExponentiationData (Term Bound : Set) : Set₁ where
  field
    zero one : Bound
    add multiply : Bound → Bound → Bound
    exp : Bound → Bound
    LessEqual : Bound → Bound → Set

    termNorm localizedFactor : Term → Bound

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    multiplyMonotoneNonnegative : ∀ {left leftUpper right rightUpper} →
      LessEqual zero left → LessEqual zero leftUpper →
      LessEqual zero right → LessEqual zero rightUpper →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (multiply left right) (multiply leftUpper rightUpper)

    oneNonnegative : LessEqual zero one
    factorNonnegative : ∀ term → LessEqual zero (localizedFactor term)
    exponentialNonnegative : ∀ value → LessEqual zero (exp value)

    factorBelowExponential : ∀ term →
      LessEqual (localizedFactor term) (exp (termNorm term))
    expAdd : ∀ left right →
      exp (add left right) ≡ multiply (exp left) (exp right)
    expZero : exp zero ≡ one

open LocalizedExponentiationData public

sumNorms : ∀ {Term Bound} → LocalizedExponentiationData Term Bound → List Term → Bound
sumNorms dataSet [] = zero dataSet
sumNorms dataSet (term ∷ terms) =
  add dataSet (termNorm dataSet term) (sumNorms dataSet terms)

localizedProduct :
  ∀ {Term Bound} → LocalizedExponentiationData Term Bound → List Term → Bound
localizedProduct dataSet [] = one dataSet
localizedProduct dataSet (term ∷ terms) =
  multiply dataSet (localizedFactor dataSet term) (localizedProduct dataSet terms)

localizedProductNonnegative :
  ∀ {Term Bound} (dataSet : LocalizedExponentiationData Term Bound) terms →
  LessEqual dataSet (zero dataSet) (localizedProduct dataSet terms)
localizedProductNonnegative dataSet [] = oneNonnegative dataSet
localizedProductNonnegative dataSet (term ∷ terms) =
  multiplyMonotoneNonnegative dataSet
    (factorNonnegative dataSet term)
    (factorNonnegative dataSet term)
    (localizedProductNonnegative dataSet terms)
    (localizedProductNonnegative dataSet terms)
    (reflexive dataSet (localizedFactor dataSet term))
    (reflexive dataSet (localizedProduct dataSet terms))

localizedExponentiationBound :
  ∀ {Term Bound} (dataSet : LocalizedExponentiationData Term Bound) terms →
  LessEqual dataSet
    (localizedProduct dataSet terms)
    (exp dataSet (sumNorms dataSet terms))
localizedExponentiationBound dataSet [] =
  subst
    (λ upper → LessEqual dataSet (one dataSet) upper)
    (sym (expZero dataSet))
    (reflexive dataSet (one dataSet))
localizedExponentiationBound dataSet (term ∷ terms) =
  subst
    (λ upper → LessEqual dataSet
      (multiply dataSet
        (localizedFactor dataSet term)
        (localizedProduct dataSet terms)) upper)
    (sym (expAdd dataSet
      (termNorm dataSet term) (sumNorms dataSet terms)))
    (multiplyMonotoneNonnegative dataSet
      (factorNonnegative dataSet term)
      (exponentialNonnegative dataSet (termNorm dataSet term))
      (localizedProductNonnegative dataSet terms)
      (exponentialNonnegative dataSet (sumNorms dataSet terms))
      (factorBelowExponential dataSet term)
      (localizedExponentiationBound dataSet terms))

record LocalizedRExponentiationBridge
    (RExpression LocalizedTerm Bound : Set) : Set₁ where
  field
    exponentiationData : LocalizedExponentiationData LocalizedTerm Bound
    localizedTerms : RExpression → List LocalizedTerm
    rNorm : RExpression → Bound
    rNormBelowLocalizedProduct : ∀ expression →
      LessEqual exponentiationData (rNorm expression)
        (localizedProduct exponentiationData (localizedTerms expression))

open LocalizedRExponentiationBridge public

rNormBelowExponentialOfLocalizedSum :
  ∀ {RExpression LocalizedTerm Bound}
    (bridge : LocalizedRExponentiationBridge RExpression LocalizedTerm Bound)
    expression →
  LessEqual (exponentiationData bridge)
    (rNorm bridge expression)
    (exp (exponentiationData bridge)
      (sumNorms (exponentiationData bridge)
        (localizedTerms bridge expression)))
rNormBelowExponentialOfLocalizedSum bridge expression =
  transitive (exponentiationData bridge)
    (rNormBelowLocalizedProduct bridge expression)
    (localizedExponentiationBound (exponentiationData bridge)
      (localizedTerms bridge expression))

finiteLocalizedProductDefinitionLevel : ProofLevel
finiteLocalizedProductDefinitionLevel = machineChecked

localizedExponentiationInductionLevel : ProofLevel
localizedExponentiationInductionLevel = machineChecked

rLocalizedExponentiationAssemblyLevel : ProofLevel
rLocalizedExponentiationAssemblyLevel = machineChecked

-- Remaining analytic input: instantiate factorBelowExponential and identify the
-- actual R expression with the localized product in the common polymer norm.
localizedFactorAnalyticEstimateInputsLevel : ProofLevel
localizedFactorAnalyticEstimateInputsLevel = conditional

rExpressionLocalizedProductMeaningInputsLevel : ProofLevel
rExpressionLocalizedProductMeaningInputsLevel = conditional

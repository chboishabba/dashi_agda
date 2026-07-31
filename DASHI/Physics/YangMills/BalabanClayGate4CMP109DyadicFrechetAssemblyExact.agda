module DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicFrechetAssemblyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact chain-rule assembly for the dyadic CMP109 Fréchet kernel.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- For M_c(U)=exp(Xi_c(U)) U_c, the left-trivialized derivative has the form
--
--   D M_c[A]
--     = dexp_{Xi_c}(D Xi_c[A])
--       + Ad_{exp Xi_c}(D U_c[A]),
--
-- while D Xi_c is the weighted finite sum of
-- dexp^{-1}_{log W_{c,x}} D W_{c,x}.  The module below builds that formula
-- literally and proves its endpoint support from the component support laws.
-- The remaining physical theorem is therefore only that the repository's
-- perturbation calculus supplies the component derivative equalities.
------------------------------------------------------------------------

record CMP109DifferentialAlgebra
    (Base Entry Scalar : Set) : Set₁ where
  field
    zeroEntry : Entry
    addEntry : Entry → Entry → Entry
    scaleEntry : Scalar → Entry → Entry

    logDifferential : Base → Entry → Entry
    expDifferential : Base → Entry → Entry
    endpointTransport : Base → Entry → Entry

    addZeroLeft : ∀ entry → addEntry zeroEntry entry ≡ entry
    addZeroRight : ∀ entry → addEntry entry zeroEntry ≡ entry
    scaleZero : ∀ scalar → scaleEntry scalar zeroEntry ≡ zeroEntry
    logDifferentialZero : ∀ base →
      logDifferential base zeroEntry ≡ zeroEntry
    expDifferentialZero : ∀ base →
      expDifferential base zeroEntry ≡ zeroEntry
    endpointTransportZero : ∀ base →
      endpointTransport base zeroEntry ≡ zeroEntry

open CMP109DifferentialAlgebra public

finiteSumEntries :
  ∀ {Base Entry Scalar} →
  CMP109DifferentialAlgebra Base Entry Scalar → List Entry → Entry
finiteSumEntries algebra [] = zeroEntry algebra
finiteSumEntries algebra (entry ∷ entries) =
  addEntry algebra entry (finiteSumEntries algebra entries)

record DyadicCMP109DifferentialComponents
    (Coarse Fine Term Base Entry Scalar : Set) : Set₁ where
  field
    algebra : CMP109DifferentialAlgebra Base Entry Scalar

    localTerms : Coarse → List Term
    termWeight : Coarse → Term → Scalar

    relativeLogBase : Coarse → Term → Base
    relativeHolonomyDerivative : Coarse → Term → Fine → Entry

    averageBase exponentialBase : Coarse → Base
    endpointDerivative : Coarse → Fine → Entry

    Support : Coarse → Fine → Set

    relativeDerivativeOutsideSupport : ∀ coarse term fine →
      (Support coarse fine → Empty) →
      relativeHolonomyDerivative coarse term fine ≡ zeroEntry algebra

    endpointDerivativeOutsideSupport : ∀ coarse fine →
      (Support coarse fine → Empty) →
      endpointDerivative coarse fine ≡ zeroEntry algebra

open DyadicCMP109DifferentialComponents public

data Empty : Set where

localLogDerivative :
  ∀ {Coarse Fine Term Base Entry Scalar} →
  DyadicCMP109DifferentialComponents
    Coarse Fine Term Base Entry Scalar →
  Coarse → Term → Fine → Entry
localLogDerivative components coarse term fine =
  logDifferential (algebra components)
    (relativeLogBase components coarse term)
    (relativeHolonomyDerivative components coarse term fine)

weightedLocalDerivative :
  ∀ {Coarse Fine Term Base Entry Scalar} →
  DyadicCMP109DifferentialComponents
    Coarse Fine Term Base Entry Scalar →
  Coarse → Fine → Term → Entry
weightedLocalDerivative components coarse fine term =
  scaleEntry (algebra components)
    (termWeight components coarse term)
    (localLogDerivative components coarse term fine)

averageDerivative :
  ∀ {Coarse Fine Term Base Entry Scalar} →
  DyadicCMP109DifferentialComponents
    Coarse Fine Term Base Entry Scalar →
  Coarse → Fine → Entry
averageDerivative components coarse fine =
  finiteSumEntries (algebra components)
    (mapList
      (weightedLocalDerivative components coarse fine)
      (localTerms components coarse))
  where
  mapList : ∀ {A B : Set} → (A → B) → List A → List B
  mapList function [] = []
  mapList function (value ∷ values) =
    function value ∷ mapList function values

assembledCMP109DerivativeEntry :
  ∀ {Coarse Fine Term Base Entry Scalar} →
  DyadicCMP109DifferentialComponents
    Coarse Fine Term Base Entry Scalar →
  Coarse → Fine → Entry
assembledCMP109DerivativeEntry components coarse fine =
  addEntry (algebra components)
    (expDifferential (algebra components)
      (averageBase components coarse)
      (averageDerivative components coarse fine))
    (endpointTransport (algebra components)
      (exponentialBase components coarse)
      (endpointDerivative components coarse fine))

allWeightedTermsZeroOutsideSupport :
  ∀ {Coarse Fine Term Base Entry Scalar}
    (components : DyadicCMP109DifferentialComponents
      Coarse Fine Term Base Entry Scalar)
    coarse fine →
  (Support components coarse fine → Empty) →
  ∀ terms →
  finiteSumEntries (algebra components)
    (mapWeighted terms)
  ≡ zeroEntry (algebra components)
  where
  mapWeighted : List Term → List Entry
  mapWeighted [] = []
  mapWeighted (term ∷ terms) =
    weightedLocalDerivative components coarse fine term ∷
    mapWeighted terms
allWeightedTermsZeroOutsideSupport components coarse fine outside [] = refl
allWeightedTermsZeroOutsideSupport components coarse fine outside
    (term ∷ terms) =
  trans
    (cong
      (λ head → addEntry (algebra components) head
        (finiteSumEntries (algebra components)
          (mapWeighted terms)))
      (trans
        (cong
          (scaleEntry (algebra components)
            (termWeight components coarse term))
          (trans
            (cong
              (logDifferential (algebra components)
                (relativeLogBase components coarse term))
              (relativeDerivativeOutsideSupport components
                coarse term fine outside))
            (logDifferentialZero (algebra components)
              (relativeLogBase components coarse term))))
        (scaleZero (algebra components)
          (termWeight components coarse term))))
    (trans
      (addZeroLeft (algebra components)
        (finiteSumEntries (algebra components) (mapWeighted terms)))
      (allWeightedTermsZeroOutsideSupport
        components coarse fine outside terms))
  where
  mapWeighted : List Term → List Entry
  mapWeighted [] = []
  mapWeighted (selected ∷ selectedTerms) =
    weightedLocalDerivative components coarse fine selected ∷
    mapWeighted selectedTerms

averageDerivativeOutsideSupport :
  ∀ {Coarse Fine Term Base Entry Scalar}
    (components : DyadicCMP109DifferentialComponents
      Coarse Fine Term Base Entry Scalar)
    coarse fine →
  (Support components coarse fine → Empty) →
  averageDerivative components coarse fine ≡ zeroEntry (algebra components)
averageDerivativeOutsideSupport components coarse fine outside =
  allWeightedTermsZeroOutsideSupport components coarse fine outside
    (localTerms components coarse)

assembledDerivativeOutsideSupport :
  ∀ {Coarse Fine Term Base Entry Scalar}
    (components : DyadicCMP109DifferentialComponents
      Coarse Fine Term Base Entry Scalar)
    coarse fine →
  (Support components coarse fine → Empty) →
  assembledCMP109DerivativeEntry components coarse fine
  ≡ zeroEntry (algebra components)
assembledDerivativeOutsideSupport components coarse fine outside =
  trans
    (cong
      (λ averagePart →
        addEntry (algebra components) averagePart
          (endpointTransport (algebra components)
            (exponentialBase components coarse)
            (endpointDerivative components coarse fine)))
      (trans
        (cong
          (expDifferential (algebra components)
            (averageBase components coarse))
          (averageDerivativeOutsideSupport
            components coarse fine outside))
        (expDifferentialZero (algebra components)
          (averageBase components coarse))))
    (trans
      (addZeroLeft (algebra components)
        (endpointTransport (algebra components)
          (exponentialBase components coarse)
          (endpointDerivative components coarse fine)))
      (trans
        (cong
          (endpointTransport (algebra components)
            (exponentialBase components coarse))
          (endpointDerivativeOutsideSupport components
            coarse fine outside))
        (endpointTransportZero (algebra components)
          (exponentialBase components coarse))))

record PhysicalCMP109FrechetChainMeaning
    (Coarse Fine Term Base Entry Scalar : Set) : Set₁ where
  field
    components : DyadicCMP109DifferentialComponents
      Coarse Fine Term Base Entry Scalar

    physicalDerivativeEntry : Coarse → Fine → Entry
    productRuleDerivativeEntry : Coarse → Fine → Entry

    physicalDerivativeByProductRule : ∀ coarse fine →
      physicalDerivativeEntry coarse fine
      ≡ productRuleDerivativeEntry coarse fine

    productRuleUsesAssembledComponents : ∀ coarse fine →
      productRuleDerivativeEntry coarse fine
      ≡ assembledCMP109DerivativeEntry components coarse fine

open PhysicalCMP109FrechetChainMeaning public

physicalDerivativeEqualsAssembledKernel :
  ∀ {Coarse Fine Term Base Entry Scalar}
    (meaning : PhysicalCMP109FrechetChainMeaning
      Coarse Fine Term Base Entry Scalar)
    coarse fine →
  physicalDerivativeEntry meaning coarse fine
  ≡ assembledCMP109DerivativeEntry (components meaning) coarse fine
physicalDerivativeEqualsAssembledKernel meaning coarse fine =
  trans
    (physicalDerivativeByProductRule meaning coarse fine)
    (productRuleUsesAssembledComponents meaning coarse fine)

physicalDerivativeOutsideSupport :
  ∀ {Coarse Fine Term Base Entry Scalar}
    (meaning : PhysicalCMP109FrechetChainMeaning
      Coarse Fine Term Base Entry Scalar)
    coarse fine →
  (Support (components meaning) coarse fine → Empty) →
  physicalDerivativeEntry meaning coarse fine
  ≡ zeroEntry (algebra (components meaning))
physicalDerivativeOutsideSupport meaning coarse fine outside =
  trans
    (physicalDerivativeEqualsAssembledKernel meaning coarse fine)
    (assembledDerivativeOutsideSupport
      (components meaning) coarse fine outside)

cmp109FrechetKernelDefinitionLevel : ProofLevel
cmp109FrechetKernelDefinitionLevel = computed

cmp109FrechetEndpointSupportLevel : ProofLevel
cmp109FrechetEndpointSupportLevel = machineChecked

cmp109PhysicalDerivativeChainAssemblyLevel : ProofLevel
cmp109PhysicalDerivativeChainAssemblyLevel = machineChecked

physicalCMP109ComponentDerivativeInputsLevel : ProofLevel
physicalCMP109ComponentDerivativeInputsLevel = conditional

physicalCMP109ProductChainRuleInputsLevel : ProofLevel
physicalCMP109ProductChainRuleInputsLevel = conditional

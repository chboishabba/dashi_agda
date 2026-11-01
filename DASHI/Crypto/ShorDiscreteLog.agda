module DASHI.Crypto.ShorDiscreteLog where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Quantum.GeneralShor

------------------------------------------------------------------------
-- Shor's discrete-logarithm specialization.
------------------------------------------------------------------------

record CyclicDiscreteLogProblem : Set₁ where
  field
    Element : Set
    order : Nat
    generator : Element
    target : Element

    power : Element → Nat → Element
    logarithm : Nat
    logarithmBelowOrder : logarithm < order
    targetIsGeneratorPower :
      target ≡ power generator logarithm

open CyclicDiscreteLogProblem public

record ShorDiscreteLogRun
    (P : CyclicDiscreteLogProblem) : Set₁ where
  field
    hiddenSubgroupProblem : FiniteAbelianHiddenSubgroupProblem
    machine : GeneralShorMachine hiddenSubgroupProblem

    SampleWitness : Set
    sampleWitness : SampleWitness
    recoveredLogarithm : SampleWitness → Nat

    recoveredBelowOrder :
      recoveredLogarithm sampleWitness < order P

    recoveredSound :
      power P (generator P) (recoveredLogarithm sampleWitness)
      ≡ target P

open ShorDiscreteLogRun public

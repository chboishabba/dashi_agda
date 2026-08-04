module DASHI.Physics.Closure.NSTriadKNLuoOfficialIncrementKernelFullShellAdapterExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Separate the analytic increment-kernel identity from finite reindexing. The
-- caller supplies the spatial translation/integration formula and a concrete
-- contribution attached to every mature full-shell pair. The equality of the
-- physical hard-high fold and full-shell fold is derived from the pre-budget
-- exact list identification, preserving order and multiplicity and using no
-- terminal localized-gradient budget.
--
-- SOURCE-FIDELITY CORRECTION
-- The literal formula applies kernelWeight through scaleTensor before
-- integration.  This matches r_p's weighted increment integral.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact as FluxKernel
import DASHI.Physics.Closure.NSTriadKNLuoHardHighFullShellTermFoldExact as Fold
import DASHI.Physics.Closure.NSCompactGammaAnalyticClosureProgram as Closure

record OfficialIncrementKernelAnalyticInputs
    {d s t stateLevel tensorLevel scalarLevel spaceLevel contributionLevel : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {State : Set stateLevel}
    {Tensor : Set tensorLevel}
    {Scalar : Set scalarLevel}
    (data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time)
    (source : FluxKernel.LuoExactFluxKernelDecomposition
      State Tensor Scalar)
    (Space : Set spaceLevel)
    (Contribution : Set contributionLevel)
    : Set (lsuc
        (d ⊔ s ⊔ t ⊔ stateLevel ⊔ tensorLevel ⊔ scalarLevel
          ⊔ spaceLevel ⊔ contributionLevel)) where
  field
    translate : Space → State → State
    subtractState : State → State → State
    incrementTensor : State → State → Tensor
    kernelWeight : Nat → Space → Scalar
    scaleTensor : Scalar → Tensor → Tensor
    integrateTensor : (Space → Tensor) → Tensor

    literalIncrementKernelMeaning :
      (shell : Nat) → (u : State) →
      FluxKernel.incrementKernel source shell u
      ≡ integrateTensor
          (λ displacement →
            scaleTensor
              (kernelWeight shell displacement)
              (incrementTensor
                (subtractState (translate displacement u) u)
                (subtractState (translate displacement u) u)))

    pairContribution :
      Nat → State →
      Closure.Pair (PreBudget.program data) → Contribution

    combineContribution : Contribution → Contribution → Contribution
    zeroContribution : Contribution

    LowIncrementPieceMatchesPhysicalTriads : Set contributionLevel
    lowIncrementPieceMatchesPhysicalTriads :
      LowIncrementPieceMatchesPhysicalTriads

    HighIncrementPieceMatchesPhysicalTriads : Set contributionLevel
    highIncrementPieceMatchesPhysicalTriads :
      HighIncrementPieceMatchesPhysicalTriads

    HighTailSquareMatchesPhysicalTriads : Set contributionLevel
    highTailSquareMatchesPhysicalTriads :
      HighTailSquareMatchesPhysicalTriads

open OfficialIncrementKernelAnalyticInputs public

officialIncrementKernelPhysicalRealization :
  ∀ {d s t stateLevel tensorLevel scalarLevel spaceLevel contributionLevel}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {State : Set stateLevel}
    {Tensor : Set tensorLevel}
    {Scalar : Set scalarLevel}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    {source : FluxKernel.LuoExactFluxKernelDecomposition
      State Tensor Scalar}
    {Space : Set spaceLevel}
    {Contribution : Set contributionLevel} →
  OfficialIncrementKernelAnalyticInputs
    data source Space Contribution →
  FluxKernel.LuoIncrementKernelPhysicalRealization source Space
officialIncrementKernelPhysicalRealization
  {data = data} {source = source} inputs = record
  { translate = translate inputs
  ; subtractState = subtractState inputs
  ; incrementTensor = incrementTensor inputs
  ; kernelWeight = kernelWeight inputs
  ; scaleTensor = scaleTensor inputs
  ; integrateTensor = integrateTensor inputs
  ; literalIncrementKernelMeaning = literalIncrementKernelMeaning inputs
  ; FourierTerm = Contribution
  ; physicalTriadTerms = λ shell state →
      Fold.foldList
        (combineContribution inputs)
        (zeroContribution inputs)
        (Fold.hardHighPairContributionList
          data shell (pairContribution inputs shell state))
  ; fullShellIncidenceTerms = λ shell state →
      Fold.foldList
        (combineContribution inputs)
        (zeroContribution inputs)
        (Fold.fullShellPairContributionList
          data shell (pairContribution inputs shell state))
  ; incrementKernelFourierExpansion = λ shell state →
      Fold.hardHighContributionFoldMatchesFullShell
        data shell
        (pairContribution inputs shell state)
        (combineContribution inputs)
        (zeroContribution inputs)
  ; lowIncrementPieceMatchesPhysicalTriads =
      LowIncrementPieceMatchesPhysicalTriads inputs
  ; lowIncrementPieceMatchesPhysicalTriadsWitness =
      lowIncrementPieceMatchesPhysicalTriads inputs
  ; highIncrementPieceMatchesPhysicalTriads =
      HighIncrementPieceMatchesPhysicalTriads inputs
  ; highIncrementPieceMatchesPhysicalTriadsWitness =
      highIncrementPieceMatchesPhysicalTriads inputs
  ; highTailSquareMatchesPhysicalTriads =
      HighTailSquareMatchesPhysicalTriads inputs
  ; highTailSquareMatchesPhysicalTriadsWitness =
      highTailSquareMatchesPhysicalTriads inputs
  }

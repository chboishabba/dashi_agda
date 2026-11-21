module DASHI.Analysis.RiemannG2AlpogeZeroLineCosineCollapseExact where

-- P1 geometric/analytic source CONSUMER: trace what the real RH zero-location
-- theorem can pay on the original target-centred G2 determinant scalar problem.
-- No new zero family, taper, integral, signed estimate or RH theorem invented.
--
-- On a genuinely identified off-line zero carrier, every zero has zero
-- horizontal displacement under RH. The cosh(horizontal*u) factor then
-- collapses to 1 and leaves an actual target-centred signed cosine kernel.
-- That simplification is NOT a positivity, cancellation or strict Off/Gamma
-- allowance proof.  The correct zero-carrier weld is still required.
--
-- Source owner: RiemannG2TargetCenteredScalarCancellationAssemblyExact.
-- Cross-prover candidate: fork Claim.Zeta / RiemannHypothesis, whose
-- genuine analytic-to-G2 zero-carrier transport is NOT built here.
-- SOURCE WRITTEN; AGDA KERNEL CHECK PENDING; NO CI.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Original

private
  module P = Original.LiteralTargetCenteredScalarProblem

-- These are precisely the missing *mathematical* source-to-consumer laws;
-- they must be proved on the original selected G2 zero and integral, not
-- satisfied by a redefined model.
record SameZeroCarrierCollapse
    (problem : Original.LiteralTargetCenteredScalarProblem) : Set₁ where
  field
    -- A verified Lean RH theorem alone does not establish this:
    -- the zero index must be proved to range over the actual original
    -- Riemann-zeta nontrivial zeros with the same off-real normalization.
    horizontalDisplacementZero :
      (sigma : P.ZeroIndex problem) →
      P.offRealPart problem sigma ≡ P.zeroS problem

    zeroTimesParameter :
      (u : P.Parameter problem) →
      P.mulS problem (P.zeroS problem) u ≡ P.zeroS problem

    coshAtZero :
      P.coshS problem (P.zeroS problem) ≡ P.oneS problem

    -- Pointwise equality is enough for the original integral to agree.
    -- Do not assume dependent function extensionality or silently identify
    -- synthetic and actual G2 integration functionals.
    integrateCongruent :
      (f g : P.Parameter problem → P.Scalar problem) →
      ((u : P.Parameter problem) → f u ≡ g u) →
      P.integrate problem f ≡ P.integrate problem g

open SameZeroCarrierCollapse public

-- Preserve the original literal scalar and all coefficients (including 4,
-- q, multiplicity, target t and the exact source nearOff index).
collapsedCosineKernel :
  (problem : Original.LiteralTargetCenteredScalarProblem) →
  P.ZeroIndex problem → P.Parameter problem → P.Scalar problem
collapsedCosineKernel problem sigma u =
  P.mulS problem
    (P.mulS problem
      (P.mulS problem
        (P.fourS problem)
        (P.q problem u))
      (P.mulS problem
        (P.multiplicity problem sigma)
        (P.oneS problem)))
    (P.cosS problem
      (P.mulS problem
        (P.subS problem (P.ordinate problem sigma) (P.target problem))
        u))

sourceCosineCoshKernel :
  (problem : Original.LiteralTargetCenteredScalarProblem) →
  P.ZeroIndex problem → P.Parameter problem → P.Scalar problem
sourceCosineCoshKernel problem sigma u =
  P.mulS problem
    (P.mulS problem
      (P.mulS problem
        (P.fourS problem)
        (P.q problem u))
      (P.mulS problem
        (P.multiplicity problem sigma)
        (P.coshS problem
          (P.mulS problem
            (P.offRealPart problem sigma) u))))
    (P.cosS problem
      (P.mulS problem
        (P.subS problem (P.ordinate problem sigma) (P.target problem))
        u))

-- This is the exact finite source-level geometric simplification, not an
-- RH-equivalent terminal certificate.
pointwiseZeroLineCollapse :
  (problem : Original.LiteralTargetCenteredScalarProblem) →
  (weld : SameZeroCarrierCollapse problem) →
  (sigma : P.ZeroIndex problem) (u : P.Parameter problem) →
  sourceCosineCoshKernel problem sigma u
    ≡ collapsedCosineKernel problem sigma u
pointwiseZeroLineCollapse problem weld sigma u
  rewrite horizontalDisplacementZero weld sigma
        | zeroTimesParameter weld u
        | coshAtZero weld = refl

-- From the original G2 source definition, the actual dSigma is exactly the
-- integral of that simpler kernel, under the explicitly named weld fields.
originalDSigmaBecomesPureCosine :
  (problem : Original.LiteralTargetCenteredScalarProblem) →
  (weld : SameZeroCarrierCollapse problem) →
  (sigma : P.ZeroIndex problem) →
  P.dSigma problem sigma
    ≡ P.integrate problem (collapsedCosineKernel problem sigma)
originalDSigmaBecomesPureCosine problem weld sigma =
  trans
    (P.dSigmaIsLiteralKernel problem sigma)
    (integrateCongruent weld
      (sourceCosineCoshKernel problem sigma)
      (collapsedCosineKernel problem sigma)
      (pointwiseZeroLineCollapse problem weld sigma))

-- No statement asserting the resulting cosine sum is nonnegative, small
-- enough for G2, or that the universal pole-quotient Off/Gamma taper matches
-- this determinant taper. Those remain independent and are fail-closed.

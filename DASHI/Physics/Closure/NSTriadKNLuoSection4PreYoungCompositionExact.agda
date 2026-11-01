module DASHI.Physics.Closure.NSTriadKNLuoSection4PreYoungCompositionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- PURPOSE
-- Compose the exact Section-4 component inequalities into the preliminary
-- Young inequality and then invoke the checked terminal absorption theorem.
-- From
--
--   X^2 <= J1 + J2,
--   J1 <= delta a X,
--   J2 <= delta lambda,
--
-- the module proves
--
--   X^2 <= delta (a X + lambda).
--
-- Together with a^2 <= lambda and 0 <= delta <= 1 this yields
--
--   X^2 <= 3 delta lambda.
--
-- Neither the preliminary inequality nor the terminal estimate is a field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoSection4TerminalYoungClosureExact as Terminal

record Section4PreYoungData : Set where
  constructor section4-pre-young
  field
    X J1 J2 delta halfScale lambda : ℚ

    XNonnegative : 0ℚ ≤ X
    deltaNonnegative : 0ℚ ≤ delta
    halfScaleNonnegative : 0ℚ ≤ halfScale
    lambdaNonnegative : 0ℚ ≤ lambda
    deltaAtMostOne : delta ≤ 1ℚ
    halfScaleSquaredBelowLambda :
      Terminal.square halfScale ≤ lambda

    energyBelowComponents :
      Terminal.square X ≤ J1 + J2

    J1Bound :
      J1 ≤ delta * (halfScale * X)

    J2Bound :
      J2 ≤ delta * lambda

open Section4PreYoungData public

section4PreYoungInequality :
  (data : Section4PreYoungData) →
  Terminal.square (X data)
  ≤ delta data * (halfScale data * X data + lambda data)
section4PreYoungInequality data =
  let
    componentBound :
      J1 data + J2 data
      ≤ delta data * (halfScale data * X data)
        + delta data * lambda data
    componentBound =
      ℚₚ.+-mono-≤
        (J1Bound data)
        (J2Bound data)

    targetMeaning :
      delta data * (halfScale data * X data)
        + delta data * lambda data
      ≡ delta data * (halfScale data * X data + lambda data)
    targetMeaning =
      solve
        ( delta data
        ∷ halfScale data
        ∷ X data
        ∷ lambda data
        ∷ []
        )
  in
  ℚₚ.≤-trans
    (energyBelowComponents data)
    (subst
      (λ upper → J1 data + J2 data ≤ upper)
      targetMeaning
      componentBound)

asTerminalYoungData :
  Section4PreYoungData → Terminal.Section4TerminalYoungData
asTerminalYoungData data =
  Terminal.section4-terminal-young
    (X data)
    (delta data)
    (halfScale data)
    (lambda data)
    (XNonnegative data)
    (deltaNonnegative data)
    (halfScaleNonnegative data)
    (lambdaNonnegative data)
    (deltaAtMostOne data)
    (halfScaleSquaredBelowLambda data)
    (section4PreYoungInequality data)

section4TerminalEstimateFromComponents :
  (data : Section4PreYoungData) →
  Terminal.square (X data)
  ≤ Terminal.three * (delta data * lambda data)
section4TerminalEstimateFromComponents data =
  Terminal.section4TerminalYoungClosure
    (asTerminalYoungData data)

section4PreYoungCompositionClosed : Bool
section4PreYoungCompositionClosed = true

section4TerminalEstimateDerivedFromComponents : Bool
section4TerminalEstimateDerivedFromComponents = true

section4PreYoungCompositionClosedIsTrue :
  section4PreYoungCompositionClosed ≡ true
section4PreYoungCompositionClosedIsTrue = refl

section4TerminalEstimateDerivedFromComponentsIsTrue :
  section4TerminalEstimateDerivedFromComponents ≡ true
section4TerminalEstimateDerivedFromComponentsIsTrue = refl

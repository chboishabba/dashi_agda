module DASHI.Physics.YangMills.SetoidPhysicalInvolutionParityExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.PhysicalInvolutionParityExact as Parity

record SetoidEvenUnder
    {Domain Codomain : Set}
    (involution : Parity.SetoidInvolution Domain)
    (codomain : Parity.ParityCodomain Codomain)
    (function : Domain → Codomain) : Set₁ where
  field
    functionCongruent : ∀ {left right} →
      Parity.Equivalent involution left right →
      Parity.Equivalent codomain (function left) (function right)

    evenLaw : ∀ value →
      Parity.Equivalent codomain
        (function (Parity.reverse involution value))
        (function value)

open SetoidEvenUnder public

record SetoidOddUnder
    {Domain Codomain : Set}
    (involution : Parity.SetoidInvolution Domain)
    (codomain : Parity.ParityCodomain Codomain)
    (function : Domain → Codomain) : Set₁ where
  field
    functionCongruent : ∀ {left right} →
      Parity.Equivalent involution left right →
      Parity.Equivalent codomain (function left) (function right)

    oddLaw : ∀ value →
      Parity.Equivalent codomain
        (function (Parity.reverse involution value))
        (Parity.negate codomain (function value))

open SetoidOddUnder public

setoidOddPairCancels :
  ∀ {Domain Codomain : Set}
    {involution : Parity.SetoidInvolution Domain}
    {codomain : Parity.ParityCodomain Codomain}
    {function : Domain → Codomain} →
  SetoidOddUnder involution codomain function →
  ∀ value →
  Parity.Equivalent codomain
    (Parity.add codomain
      (function value)
      (function (Parity.reverse involution value)))
    (Parity.zero codomain)
setoidOddPairCancels {codomain = codomain} {function = function}
    odd value =
  Parity.equivalentTrans codomain
    (Parity.addCongruent codomain
      (Parity.equivalentRefl codomain (function value))
      (oddLaw odd value))
    (Parity.addInverseRight codomain (function value))

setoidPhysicalParityLevel : ProofLevel
setoidPhysicalParityLevel = machineChecked

setoidOddCancellationLevel : ProofLevel
setoidOddCancellationLevel = machineChecked

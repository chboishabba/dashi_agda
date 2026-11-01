module DASHI.Physics.Plasma.MHDMomentumTriadZeroSumBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Plasma.MHDHelicalCoefficientAnatomyExact as MHD

------------------------------------------------------------------------
-- MHD MOMENTUM-SECTOR CYCLIC ZERO-SUM KERNEL
--
-- If one helical triad uses a common geometric factor g and cyclic signed
-- radii a,b,c, then the momentum-sector radial differences
--
--   (b-c), (c-a), (a-b)
--
-- sum to zero before any estimate.  Multiplying each by the same g preserves
-- that cancellation.  This is the exact theorem-shape analogue of the NS
-- Round138 zero-sum slot structure.
------------------------------------------------------------------------

private
  sub : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

cyclicDifferenceK :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
cyclicDifferenceK a b c = sub b c

cyclicDifferenceP :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
cyclicDifferenceP a b c = sub c a

cyclicDifferenceQ :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
cyclicDifferenceQ a b c = sub a b

cyclicDifferencesSumZero :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Carrier F) →
  C3.add F
    (cyclicDifferenceK a b c)
    (C3.add F (cyclicDifferenceP a b c) (cyclicDifferenceQ a b c))
  ≡ C3.zero F
cyclicDifferencesSumZero {F = F} a b c =
  R.solve 3
    (λ a b c →
      ((b R.⊕ (R.⊝ c))
        R.⊕ ((c R.⊕ (R.⊝ a))
          R.⊕ (a R.⊕ (R.⊝ b))))
      R.⊜ R.Κ (C3.zero F))
    refl a b c
  where module R = Field.Solver F

commonGeometryPreservesZeroSum :
  ∀ {r} {F : C3.RealField r}
    (g a b c : C3.Carrier F) →
  C3.add F
    (C3.multiply F g (cyclicDifferenceK a b c))
    (C3.add F
      (C3.multiply F g (cyclicDifferenceP a b c))
      (C3.multiply F g (cyclicDifferenceQ a b c)))
  ≡ C3.zero F
commonGeometryPreservesZeroSum {F = F} g a b c =
  R.solve 4
    (λ g a b c →
      ((g R.⊗ (b R.⊕ (R.⊝ c)))
        R.⊕ ((g R.⊗ (c R.⊕ (R.⊝ a)))
          R.⊕ (g R.⊗ (a R.⊕ (R.⊝ b)))))
      R.⊜ R.Κ (C3.zero F))
    refl g a b c
  where module R = Field.Solver F

------------------------------------------------------------------------
-- Same-object weld required before this abstract algebra may be called the
-- literal MHD momentum triad.
------------------------------------------------------------------------

record LiteralMHDMomentumZeroSumWeld {r : _} (F : C3.RealField r) : Set r where
  constructor literal-mhd-momentum-zero-sum-weld
  field
    signedK signedP signedQ : C3.Carrier F
    commonGeometry : C3.Carrier F
    literalCoefficientK literalCoefficientP literalCoefficientQ : C3.Carrier F
    coefficientKIdentification :
      literalCoefficientK ≡ C3.multiply F commonGeometry (cyclicDifferenceK signedK signedP signedQ)
    coefficientPIdentification :
      literalCoefficientP ≡ C3.multiply F commonGeometry (cyclicDifferenceP signedK signedP signedQ)
    coefficientQIdentification :
      literalCoefficientQ ≡ C3.multiply F commonGeometry (cyclicDifferenceQ signedK signedP signedQ)
    sourceReference : String

open LiteralMHDMomentumZeroSumWeld public

record MHDMomentumZeroSumBoundary : Set where
  constructor mhd-momentum-zero-sum-boundary
  field
    abstractCyclicIdentityClosesLiteralMHDWithoutWeld : Bool
    abstractCyclicIdentityClosesLiteralMHDWithoutWeldIsFalse :
      abstractCyclicIdentityClosesLiteralMHDWithoutWeld ≡ false

    momentumZeroSumImpliesInductionZeroSum : Bool
    momentumZeroSumImpliesInductionZeroSumIsFalse :
      momentumZeroSumImpliesInductionZeroSum ≡ false

    nsRound138ReceiptClosesMHDMomentumWeld : Bool
    nsRound138ReceiptClosesMHDMomentumWeldIsFalse :
      nsRound138ReceiptClosesMHDMomentumWeld ≡ false

canonicalMHDMomentumZeroSumBoundary : MHDMomentumZeroSumBoundary
canonicalMHDMomentumZeroSumBoundary =
  mhd-momentum-zero-sum-boundary false refl false refl false refl

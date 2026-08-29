module DASHI.Analysis.RiemannG21ConjugateHeightSourceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannPhiCoshCoercivityReductionExact as Cosh

------------------------------------------------------------------------
-- Companion-source geometry.
--
-- Zeta23/Defs.lean:
--   f_k(u) = phi(u) exp(-i tau_k u)
--   h_{f_k}(z) = phiHat(z - tau_k).
--
-- Zeta23/Taper/Fourier.lean proves for a real even taper:
--   conj(phiHat(z)) = phiHat(conj z).
--
-- Therefore:
-- * literal Weil pole vectors sample phiHat(-tau_k +/- i/2), a conjugate pair;
-- * a reflected off-line zero pair samples phiHat((gamma-tau_k) +/- i alpha),
--   likewise a conjugate pair, with alpha = Re(rho)-1/2 up to sign convention.
--
-- G21 consequently needs a TWO-HEIGHT nondegeneracy theorem: the conjugate
-- pair at the off-line height must be transverse to the nuisance conjugate
-- pair at pole height 1/2.  Conjugacy alone does not imply this.
------------------------------------------------------------------------

record ConjugateHeightResponseFamily : Set₁ where
  field
    Height Sample Vector : Set

    responseAtHeight : Height → Vector
    conjugateHeight : Height → Height
    conjugateVector : Vector → Vector

    conjugateHeightInvolutive :
      (h : Height) → conjugateHeight (conjugateHeight h) ≡ h

    responseIntertwinesConjugation :
      (h : Height) →
      responseAtHeight (conjugateHeight h)
      ≡ conjugateVector (responseAtHeight h)

    familyReading : String

open ConjugateHeightResponseFamily public

record TwoHeightExteriorTarget
    (family : ConjugateHeightResponseFamily) : Set₁ where
  field
    offLineHeight poleHeight : Height family

    HeightsSeparated : Set
    heightsSeparated : HeightsSeparated

    ExteriorValue : Set
    exterior4 :
      Vector family → Vector family → Vector family → Vector family → ExteriorValue
    ExteriorNonzero : ExteriorValue → Set

    twoHeightTransversality :
      ExteriorNonzero
        (exterior4
          (responseAtHeight family offLineHeight)
          (responseAtHeight family (conjugateHeight family offLineHeight))
          (responseAtHeight family poleHeight)
          (responseAtHeight family (conjugateHeight family poleHeight)))

open TwoHeightExteriorTarget public

------------------------------------------------------------------------
-- Exact logical no-go: conjugate-pair structure is not transversality.
------------------------------------------------------------------------

data ToyHeight : Set where
  lowHeight highHeight : ToyHeight

data ToyVector : Set where
  collapsedVector : ToyVector

collapseResponse : ToyHeight → ToyVector
collapseResponse lowHeight = collapsedVector
collapseResponse highHeight = collapsedVector

swapHeight : ToyHeight → ToyHeight
swapHeight lowHeight = highHeight
swapHeight highHeight = lowHeight

swapHeightInvolutive : (h : ToyHeight) → swapHeight (swapHeight h) ≡ h
swapHeightInvolutive lowHeight = refl
swapHeightInvolutive highHeight = refl

identityConjugate : ToyVector → ToyVector
identityConjugate collapsedVector = collapsedVector

collapseIntertwinesConjugation :
  (h : ToyHeight) →
  collapseResponse (swapHeight h) ≡ identityConjugate (collapseResponse h)
collapseIntertwinesConjugation lowHeight = refl
collapseIntertwinesConjugation highHeight = refl

canonicalCollapsedConjugateFamily : ConjugateHeightResponseFamily
canonicalCollapsedConjugateFamily =
  record
    { Height = ToyHeight
    ; Sample = ⊤
    ; Vector = ToyVector
    ; responseAtHeight = collapseResponse
    ; conjugateHeight = swapHeight
    ; conjugateVector = identityConjugate
    ; conjugateHeightInvolutive = swapHeightInvolutive
    ; responseIntertwinesConjugation = collapseIntertwinesConjugation
    ; familyReading =
        "Counterexample family: exact conjugate-height symmetry can coexist with complete collapse of the two height responses."
    }

heightsDistinctButResponsesEqual :
  lowHeight ≡ highHeight → ⊥
heightsDistinctButResponsesEqual ()

collapsedHeightResponsesEqual :
  responseAtHeight canonicalCollapsedConjugateFamily lowHeight
  ≡ responseAtHeight canonicalCollapsedConjugateFamily highHeight
collapsedHeightResponsesEqual = refl

------------------------------------------------------------------------
-- Cross-pollination boundary with the existing cosh/coercivity lane.
--
-- Existing Phi(-2 i alpha)-Phi(0) coercivity detects off-line displacement
-- from the critical line.  It does not by itself prove independence of the
-- alpha-height response from the pole-height 1/2 response.
------------------------------------------------------------------------

record CoshToTwoHeightBoundary : Set where
  constructor coshToTwoHeightBoundary
  field
    alphaVsZeroSensitivityOwnedAsInterface : Bool
    alphaVsZeroSensitivityOwnedAsInterfaceIsTrue :
      alphaVsZeroSensitivityOwnedAsInterface ≡ true

    alphaVsZeroSensitivityImpliesAlphaVsHalfTransversality : Bool
    alphaVsZeroSensitivityImpliesAlphaVsHalfTransversalityIsFalse :
      alphaVsZeroSensitivityImpliesAlphaVsHalfTransversality ≡ false

    twoHeightTaperDeterminantStillRequired : Bool
    twoHeightTaperDeterminantStillRequiredIsTrue :
      twoHeightTaperDeterminantStillRequired ≡ true

canonicalCoshToTwoHeightBoundary : CoshToTwoHeightBoundary
canonicalCoshToTwoHeightBoundary =
  coshToTwoHeightBoundary true refl false refl true refl

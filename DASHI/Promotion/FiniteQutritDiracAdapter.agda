module DASHI.Promotion.FiniteQutritDiracAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Algebra.Quantum.FiniteQutrit
open import DASHI.Algebra.Quantum.QutritWeyl
open import DASHI.Algebra.Trit.QutritBasisBridge
import DASHI.Promotion.FiniteQuantumSchrodingerBornAdapter as FiniteTwoState
import DASHI.Promotion.QuantumQFTObligations as Quantum

------------------------------------------------------------------------
-- Scoped receipt connecting the finite qutrit basis/Dirac/Weyl layer to the
-- existing quantum promotion boundary.
--
-- The receipt certifies basis semantics and finite symbolic Weyl laws only.
-- It explicitly does not promote arbitrary complex superpositions, continuum
-- dynamics, general Born semantics, CHSH numerics, or QFT.

record FiniteQutritDiracAdapter : Set₁ where
  field
    upstreamQuantumObligations :
      Quantum.QuantumQFTPromotionObligationReceipt
    upstreamFiniteTwoStateAdapter :
      FiniteTwoState.FiniteQuantumSchrodingerBornAdapter
    basisStates : List QutritBasis
    tritBasisEquivalence : TritQutritBasisEquivalence
    weylCertificate : FiniteQutritWeylCertificate
    finiteBasisDiracSemantics : Bool
    finiteBasisDiracSemanticsIsTrue :
      finiteBasisDiracSemantics ≡ true
    qutritBasisWeylLaws : Bool
    qutritBasisWeylLawsIsTrue :
      qutritBasisWeylLaws ≡ true
    arbitrarySuperpositionsSupplied : Bool
    arbitrarySuperpositionsSuppliedIsFalse :
      arbitrarySuperpositionsSupplied ≡ false
    concreteComplexFieldSupplied : Bool
    concreteComplexFieldSuppliedIsFalse :
      concreteComplexFieldSupplied ≡ false
    numericalCHSHImported : Bool
    numericalCHSHImportedIsFalse :
      numericalCHSHImported ≡ false
    promotesFullBornSemantics : Bool
    promotesFullBornSemanticsIsFalse :
      promotesFullBornSemantics ≡ false
    promotesQFT : Bool
    promotesQFTIsFalse :
      promotesQFT ≡ false
    boundaryNotes : List String

open FiniteQutritDiracAdapter public

canonicalFiniteQutritDiracAdapter : FiniteQutritDiracAdapter
canonicalFiniteQutritDiracAdapter =
  record
    { upstreamQuantumObligations =
        Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; upstreamFiniteTwoStateAdapter =
        FiniteTwoState.canonicalFiniteQuantumSchrodingerBornAdapter
    ; basisStates = ket0 ∷ ket1 ∷ ket2 ∷ []
    ; tritBasisEquivalence =
        canonicalTritQutritBasisEquivalence
    ; weylCertificate =
        canonicalFiniteQutritWeylCertificate
    ; finiteBasisDiracSemantics = true
    ; finiteBasisDiracSemanticsIsTrue = refl
    ; qutritBasisWeylLaws = true
    ; qutritBasisWeylLawsIsTrue = refl
    ; arbitrarySuperpositionsSupplied = false
    ; arbitrarySuperpositionsSuppliedIsFalse = refl
    ; concreteComplexFieldSupplied = false
    ; concreteComplexFieldSuppliedIsFalse = refl
    ; numericalCHSHImported = false
    ; numericalCHSHImportedIsFalse = refl
    ; promotesFullBornSemantics = false
    ; promotesFullBornSemanticsIsFalse = refl
    ; promotesQFT = false
    ; promotesQFTIsFalse = refl
    ; boundaryNotes =
        "Trit is equivalent only to the three qutrit basis labels"
        ∷ "Finite basis bras, kets, normalization, and orthogonality are machine checked"
        ∷ "Generalized qutrit X and Z satisfy order-three and Weyl laws on the basis"
        ∷ "No concrete complex vector-space completion or arbitrary superposition carrier is supplied"
        ∷ "No numerical CHSH result is imported as a theorem"
        ∷ "Full Born, Stone, Schrodinger, continuum Hilbert, and QFT obligations remain open"
        ∷ []
    }

canonicalBasisDiracSemanticsTrue :
  finiteBasisDiracSemantics canonicalFiniteQutritDiracAdapter ≡ true
canonicalBasisDiracSemanticsTrue =
  finiteBasisDiracSemanticsIsTrue canonicalFiniteQutritDiracAdapter

canonicalQutritWeylLawsTrue :
  qutritBasisWeylLaws canonicalFiniteQutritDiracAdapter ≡ true
canonicalQutritWeylLawsTrue =
  qutritBasisWeylLawsIsTrue canonicalFiniteQutritDiracAdapter

canonicalKeepsBornPromotionFalse :
  promotesFullBornSemantics canonicalFiniteQutritDiracAdapter ≡ false
canonicalKeepsBornPromotionFalse =
  promotesFullBornSemanticsIsFalse canonicalFiniteQutritDiracAdapter

canonicalKeepsQFTPromotionFalse :
  promotesQFT canonicalFiniteQutritDiracAdapter ≡ false
canonicalKeepsQFTPromotionFalse =
  promotesQFTIsFalse canonicalFiniteQutritDiracAdapter

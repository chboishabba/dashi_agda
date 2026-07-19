module DASHI.Core.Base369UltrametricContraction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; z≤n; s≤s; pred)
open import Data.Vec using ([]; _∷_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Geometry.SSP369Ultrametric as Prefix using
  ( Digit369
  ; digit3
  ; digit6
  ; digit9
  ; Address
  ; distance
  ; ultrametric369
  )
import Ultrametric as UM

------------------------------------------------------------------------
-- The actual balanced-ternary Base369 carrier at three ordered scales.
--
-- The coordinates are roles, not the numerals 3, 6, and 9 themselves:
-- coarse / relational / fine.  Their order induces the prefix geometry.
------------------------------------------------------------------------

record Base369State : Set where
  constructor state369
  field
    coarse     : Trit
    relational : Trit
    fine       : Trit

open Base369State public

encodeDigit : Trit → Digit369
encodeDigit neg = digit3
encodeDigit zer = digit6
encodeDigit pos = digit9

encodeAddress : Base369State → Address (suc (suc (suc zero)))
encodeAddress (state369 a b c) =
  encodeDigit a ∷ encodeDigit b ∷ encodeDigit c ∷ []

------------------------------------------------------------------------
-- Concrete ultrametric.
--
-- Distance is the number of unresolved suffix coordinates after the longest
-- common prefix.  Thus a coarse disagreement has distance 3, a relational
-- disagreement has distance 2, a fine disagreement has distance 1, and
-- equality has distance 0.
------------------------------------------------------------------------

base369Distance : Base369State → Base369State → Nat
base369Distance x y = distance (encodeAddress x) (encodeAddress y)

base369Ultrametric : UM.Ultrametric Base369State
base369Ultrametric =
  record
    { d = base369Distance
    ; id-zero = λ x → UM.Ultrametric.id-zero ultrametric369 (encodeAddress x)
    ; symmetric = λ x y →
        UM.Ultrametric.symmetric ultrametric369 (encodeAddress x) (encodeAddress y)
    ; ultratriangle = λ x y z →
        UM.Ultrametric.ultratriangle ultrametric369
          (encodeAddress x) (encodeAddress y) (encodeAddress z)
    }

------------------------------------------------------------------------
-- A concrete nonconstant Base369 kernel.
--
-- It performs one guarded coarse-to-fine delay: the previous coarse trit is
-- retained as the new fine residue while the two exposed coordinates are
-- neutralised.  It is neither identity nor constant, but it strictly pushes
-- every surviving distinction to the deepest coordinate.
------------------------------------------------------------------------

base369Kernel : Base369State → Base369State
base369Kernel (state369 a b c) = state369 zer zer a

------------------------------------------------------------------------
-- Strict symbolic contraction.
--
-- `pred` is the discrete analogue of multiplication by rho, 0 < rho < 1:
-- every positive input distance loses at least one prefix level.
------------------------------------------------------------------------

base369Kernel-contractive :
  (x y : Base369State) →
  base369Distance (base369Kernel x) (base369Kernel y)
    ≤ pred (base369Distance x y)
base369Kernel-contractive (state369 neg b c) (state369 neg b′ c′) = z≤n
base369Kernel-contractive (state369 neg b c) (state369 zer b′ c′) = s≤s z≤n
base369Kernel-contractive (state369 neg b c) (state369 pos b′ c′) = s≤s z≤n
base369Kernel-contractive (state369 zer b c) (state369 neg b′ c′) = s≤s z≤n
base369Kernel-contractive (state369 zer b c) (state369 zer b′ c′) = z≤n
base369Kernel-contractive (state369 zer b c) (state369 pos b′ c′) = s≤s z≤n
base369Kernel-contractive (state369 pos b c) (state369 neg b′ c′) = s≤s z≤n
base369Kernel-contractive (state369 pos b c) (state369 zer b′ c′) = s≤s z≤n
base369Kernel-contractive (state369 pos b c) (state369 pos b′ c′) = z≤n

------------------------------------------------------------------------
-- Nontriviality witnesses.
------------------------------------------------------------------------

negativeExample : Base369State
negativeExample = state369 neg pos zer

positiveExample : Base369State
positiveExample = state369 pos neg zer

kernelChangesNegativeExample :
  base369Kernel negativeExample ≡ state369 zer zer neg
kernelChangesNegativeExample = refl

kernelChangesPositiveExample :
  base369Kernel positiveExample ≡ state369 zer zer pos
kernelChangesPositiveExample = refl

kernelPreservesARealDistinction :
  base369Kernel negativeExample ≡ base369Kernel positiveExample → ⊥
kernelPreservesARealDistinction ()

negativePositiveDistanceContracts :
  base369Distance (base369Kernel negativeExample) (base369Kernel positiveExample)
    ≤ pred (base369Distance negativeExample positiveExample)
negativePositiveDistanceContracts = s≤s z≤n

------------------------------------------------------------------------
-- Honest boundary for arbitrary production kernels.
--
-- A kernel is stability-certified only when it supplies this witness for the
-- concrete Base369 metric.  The record does not infer contraction from naming,
-- MDL intent, symmetry, or quotient compatibility.
------------------------------------------------------------------------

record Base369ContractionCertificate (K : Base369State → Base369State) : Set where
  field
    contracts : (x y : Base369State) →
      base369Distance (K x) (K y) ≤ pred (base369Distance x y)

base369KernelCertificate : Base369ContractionCertificate base369Kernel
base369KernelCertificate = record { contracts = base369Kernel-contractive }

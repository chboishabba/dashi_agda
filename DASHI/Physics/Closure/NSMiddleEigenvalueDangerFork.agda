module DASHI.Physics.Closure.NSMiddleEigenvalueDangerFork where

open import Agda.Primitive using (Set)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exact logical fork behind the middle-eigenvalue program.
--
-- P is the biaxial branch lambda2 <= 0.
-- Q is the small-middle-alignment branch alpha2 <= epsilon.
-- The complement is the genuine middle-channel leak. Resolving that branch
-- by turnover, loss of packet tightness, or viscous absorption yields the
-- five-way danger resolution used by the proof-seeking lane.
------------------------------------------------------------------------

¬_ : Set → Set
¬ P = P → ⊥

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : ¬ P → Dec P

data MiddleEigenvalueBranch (P Q : Set) : Set where
  biaxialBranch : P → MiddleEigenvalueBranch P Q
  middleAlignmentSmallBranch : ¬ P → Q → MiddleEigenvalueBranch P Q
  middleChannelLeakBranch : ¬ P → ¬ Q → MiddleEigenvalueBranch P Q

middleEigenvalueBranchExhaustive :
  {P Q : Set} → Dec P → Dec Q → MiddleEigenvalueBranch P Q
middleEigenvalueBranchExhaustive (yes p) q? = biaxialBranch p
middleEigenvalueBranchExhaustive (no notP) (yes q) =
  middleAlignmentSmallBranch notP q
middleEigenvalueBranchExhaustive (no notP) (no notQ) =
  middleChannelLeakBranch notP notQ

data MiddleLeakResolution (Turnover Tail Viscous : Set) : Set where
  turnoverResolution : Turnover → MiddleLeakResolution Turnover Tail Viscous
  lossOfTightnessResolution : Tail → MiddleLeakResolution Turnover Tail Viscous
  viscousAbsorptionResolution : Viscous → MiddleLeakResolution Turnover Tail Viscous

data DangerousTransferResolution
    (Biaxial AlignmentSmall Turnover Tail Viscous : Set) : Set where
  biaxialDepletion :
    Biaxial →
    DangerousTransferResolution Biaxial AlignmentSmall Turnover Tail Viscous
  alignmentDepletion :
    AlignmentSmall →
    DangerousTransferResolution Biaxial AlignmentSmall Turnover Tail Viscous
  coherenceTurnover :
    Turnover →
    DangerousTransferResolution Biaxial AlignmentSmall Turnover Tail Viscous
  packetTightnessLost :
    Tail →
    DangerousTransferResolution Biaxial AlignmentSmall Turnover Tail Viscous
  viscosityAbsorbs :
    Viscous →
    DangerousTransferResolution Biaxial AlignmentSmall Turnover Tail Viscous

middleLeakResolutionCompletesDangerFork :
  {Biaxial AlignmentSmall Turnover Tail Viscous : Set} →
  Dec Biaxial →
  Dec AlignmentSmall →
  (¬ Biaxial → ¬ AlignmentSmall →
    MiddleLeakResolution Turnover Tail Viscous) →
  DangerousTransferResolution
    Biaxial AlignmentSmall Turnover Tail Viscous
middleLeakResolutionCompletesDangerFork (yes biaxial) alignment? resolveLeak =
  biaxialDepletion biaxial
middleLeakResolutionCompletesDangerFork (no notBiaxial) (yes alignment) resolveLeak =
  alignmentDepletion alignment
middleLeakResolutionCompletesDangerFork
  (no notBiaxial) (no notAlignment) resolveLeak
  with resolveLeak notBiaxial notAlignment
... | turnoverResolution turnover = coherenceTurnover turnover
... | lossOfTightnessResolution tail = packetTightnessLost tail
... | viscousAbsorptionResolution viscous = viscosityAbsorbs viscous

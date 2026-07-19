module DASHI.Physics.YangMills.BalabanSU2CMP98PathFamily where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)

-- A candidate path transcription is not called source-exact merely because it
-- is finite.  The record requires the orientation and concatenation equations
-- that a term-by-term comparison with the target formula must discharge.
record CMP98PathFamily (Site Bond Path : Set) : Set₁ where
  field
    source root target : Path → Site
    bonds : Path → List Bond
    reversePath : Path → Path
    concatenate : Path → Path → Path
    finitePaths : Site → Site → List Path

    reverseSource : ∀ path → source (reversePath path) ≡ target path
    reverseTarget : ∀ path → target (reversePath path) ≡ source path
    reverseInvolutive : ∀ path → reversePath (reversePath path) ≡ path
    concatenateSource : ∀ left right → source (concatenate left right) ≡ source left
    concatenateTarget : ∀ left right → target (concatenate left right) ≡ target right

open CMP98PathFamily public

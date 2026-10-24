module DASHI.Physics.CondensedMatter.MATBGTHFSelfConsistencyObstructionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.CondensedMatter.MATBGTHFSelfConsistencyObstructionReceiptExact as O

finite-quadrature-paid : O.finiteQuadratureExecuted O.canonicalTHFSelfConsistencyObstructionBoundary ≡ true
finite-quadrature-paid = refl

cutoff-sensitivity-paid : O.unresolvedCutoffSensitivityExposed O.canonicalTHFSelfConsistencyObstructionBoundary ≡ true
cutoff-sensitivity-paid = refl

full-self-consistency-still-open : O.fullSourceFaithfulSelfConsistencyPaid O.canonicalTHFSelfConsistencyObstructionBoundary ≡ false
full-self-consistency-still-open = refl

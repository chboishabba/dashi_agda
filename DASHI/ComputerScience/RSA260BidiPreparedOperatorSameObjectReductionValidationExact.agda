module DASHI.ComputerScience.RSA260BidiPreparedOperatorSameObjectReductionValidationExact where

import DASHI.ComputerScience.RSA260BidiPreparedOperatorSameObjectReductionExact as O

------------------------------------------------------------------------
-- Regression surface: the prepared-operator weld must reduce function-level
-- runtime/formal identity to the exact matrix-A same-object payment in the
-- identity-permutation synthetic context.
------------------------------------------------------------------------

requiresMatrixA :
  O.PreparedOperatorBindingPayment -> O.MatrixASameObjectPayment
requiresMatrixA = O.preparedOperatorBindingRequiresMatrixA

firstResidualIsMatrixA : O.PreparedOperatorSameObjectResidual
firstResidualIsMatrixA = O.firstPreparedOperatorSameObjectResidual

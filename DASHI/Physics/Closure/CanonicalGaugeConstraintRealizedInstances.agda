module DASHI.Physics.Closure.CanonicalGaugeConstraintRealizedInstances where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem as PGCBT
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT
open import DASHI.Physics.Closure.SecondaryConstraintGaugeInstance as SCGI

record RealizedGaugeConstraintInstance : Setω where
  field
    package : CCGP.CanonicalConstraintGaugePackage
    theorem : PGCT.ParametricGaugeConstraintTheorem package
    bridge : PGCBT.ParametricGaugeConstraintBridgeTheorem package

record CanonicalGaugeConstraintRealizedInstances : Setω where
  field
    primary : RealizedGaugeConstraintInstance
    secondary : RealizedGaugeConstraintInstance

canonicalGaugeConstraintRealizedInstances :
  CanonicalGaugeConstraintRealizedInstances
canonicalGaugeConstraintRealizedInstances =
  record
    { primary =
        record
          { package = PGCT.canonicalConstraintGaugePackage
          ; theorem = PGCT.canonicalParametricGaugeConstraintTheorem
          ; bridge =
              PGCBT.parametricGaugeConstraintBridgeTheorem
                PGCT.canonicalConstraintGaugePackage
          }
    ; secondary =
        record
          { package = SCGI.secondaryConstraintGaugePackage
          ; theorem = SCGI.secondaryParametricGaugeConstraintTheorem
          ; bridge =
              PGCBT.parametricGaugeConstraintBridgeTheorem
                SCGI.secondaryConstraintGaugePackage
          }
    }

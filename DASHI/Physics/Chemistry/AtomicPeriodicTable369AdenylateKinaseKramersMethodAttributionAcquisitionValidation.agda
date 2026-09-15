module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseKramersMethodAttributionAcquisitionValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseKramersMethodAttributionAcquisitionExact as Target

-- RED-first validation surface: require the method-source identities and the
-- separation between AdK-derived rate cells and the general Kramers literature.

hanggiSource = Target.hanggi1990Source
sriramanSource = Target.sriramanKevrekidisHummer2005Source
hummerSource = Target.hummer2005Source

apoMethodReceipt = Target.apoKramersMethodReceipt
boundMethodReceipt = Target.boundKramersMethodReceipt

methodBoundary = Target.canonicalAdKKramersMethodAttributionBoundary

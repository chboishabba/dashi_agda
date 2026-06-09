# YM Forty-Three Step Balaban Target

This receipt records the sharpened finite Yang-Mills Balaban target.

Agda receipt:

```text
DASHI/Physics/Closure/YMFortyThreeStepBalabanTargetReceipt.agda
```

Strict seed target:

```text
beta_eff*c_min_BT - a_BT > log(2*p)
```

Current convention:

```text
p = 7
c_min_BT = 0.198
a_BT = 0.06
beta_strict = 13.631602675
robust target = beta_eff >= 13.7
margin at 13.7 = 0.0135426704
```

Finite target:

```text
(k : Fin 43) -> rho k < 1
sum_{k<43} leakage k < leakageBudget
beta_eff_43 >= 13.7
```

The one-loop map is a diagnostic scale only.  It does not prove:

```text
stepwise contraction
leakage summability
beta transfer
Shimura-to-Euclidean universality
OS/Wightman reconstruction
mass-gap survival
nontrivial SU3
Clay YM
```

Immediate YM blocker:

```text
YMFortyThreeStepBalabanUniformity
```

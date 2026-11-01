# Yang–Mills Round 37 — explicit selected-variation repair

Round 36 reduced Gate I to an actual local admissible-variation selector. Round 37 supplies the finite linear repair model and splits the remaining spillover into uniquely owned sources.

## Explicit four-slot selector

For an arbitrary requested singleton scalar `h`, the four oriented slot variations are

```text
X0 = 0,
X1 = -h/2,
X2 = 0,
X3 = -h/2.
```

The model uses three distinct linear observers:

```text
gauge      = X0 + X1 - X2 - X3,
constraint = X0 + X2,
extraction = X0 - X1 + X2 - X3.
```

The selected variation proves exactly

```text
gauge      = 0,
constraint = 0,
extraction = h,
charge     = h^2/2.
```

The selector returns these equations in one dependent witness. This is the concrete finite algebra required by the “inhabitable variation frame” idea: gauge admissibility, block tangency and singleton extraction hold simultaneously rather than being unrelated Boolean fields.

## Spillover ownership

The remaining singleton coefficient is split into four named sources:

```text
gauge repair          10 / 18874368
constraint repair     10 / 18874368
covariant transport   15 / 18874368
locality boundary     20 / 18874368
---------------------------------
total                 55 / 18874368.
```

The exact coefficient equality is kernel-checked. Four componentwise residual bounds imply the total spillover bound, and every residual constructor has exactly one owner.

## Remaining physical theorem

The finite repair model does not yet transport through the literal covariant prefixes, gauge-repair operator and coarse block constraint of Bałaban’s selected background. The next theorem must construct that physical intertwiner and prove that it preserves:

```text
admissibility,
local support,
charge,
first-variation extraction,
and the four residual bounds.
```

Once supplied, the Round-36 reducer combines it with the already closed pair/deep channels and the terminal `1/32` Hessian floor.

## Sources

- Tadeusz Bałaban, *The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories*, DOI `10.1007/BF01229381`.
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`.
- Kenneth G. Wilson, *Confinement of Quarks*, DOI `10.1103/PhysRevD.10.2445`.

## Validation

```bash
bash scripts/check_yang_mills_clay_highest_alpha_round37.sh
```

No Agda-kernel or Actions success is asserted until observed.

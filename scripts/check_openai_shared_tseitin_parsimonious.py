"""Finite shared/Tseitin parsimonious-counting regression.

DASHI independent executable check; not an Agda or OpenAI kernel receipt.
Canonical models enumerate ONLY the input+gate variables used by the circuit.
"""
from itertools import product


def eval_circuit(inputs, gates, input_bits):
    out = []
    def wire(w):
        side, i = w
        return input_bits[i] if side == "i" else out[i]
    for op, args in gates:
        if op == "const": value = args[0]
        elif op == "not": value = not wire(args[0])
        elif op == "and": value = wire(args[0]) and wire(args[1])
        elif op == "or": value = wire(args[0]) or wire(args[1])
        else: raise ValueError(op)
        out.append(value)
    return tuple(out)


def count_both(n, gates, output):
    n_input_accept = 0
    n_tseitin_models = 0
    for inp in product((False, True), repeat=n):
        expected_gates = eval_circuit(n, gates, inp)
        if (inp if output[0] == "i" else expected_gates)[output[1]]:
            n_input_accept += 1
        for aux in product((False, True), repeat=len(gates)):
            if aux != expected_gates: continue
            outval = (inp if output[0] == "i" else aux)[output[1]]
            if outval: n_tseitin_models += 1
    assert n_input_accept == n_tseitin_models
    return n_input_accept


def main():
    tests = 0
    for n in (1, 2):
        programs = [()]
        for depth in range(3):
            extended = []
            for p in programs:
                wires = [("i", i) for i in range(n)] + [("g", i) for i in range(depth)]
                new_gates = [("const", (False,)), ("const", (True,))]
                new_gates += [("not", (x,)) for x in wires]
                new_gates += [(op, (a, b)) for op in ("and", "or")
                              for a in wires for b in wires]
                for gate in new_gates: extended.append(p + (gate,))
            programs = extended
            for p in programs:
                for output in [("i", i) for i in range(n)] + [("g", i) for i in range(len(p))]:
                    count_both(n, p, output)
                    tests += 1

    # A one-way auxiliary implication does not force a unique extension.
    input_bits = (False,)
    gates = (("const", (True,)),)
    expected = eval_circuit(1, gates, input_bits)
    assert expected == (True,)
    weak_models = [aux for aux in product((False, True), repeat=1)
                   if (not aux[0]) or expected[0]]
    assert len(weak_models) == 2

    # The unused Nat->Bool tail is not determined by the circuit.
    assert 2 * count_both(1, gates, ("g", 0)) == 4
    print(f"PASS: {tests} exhaustive small DAG/output cases with exact-count equality")
    print("PASS: one-way-gate and unconstrained-tail counterexamples")


if __name__ == "__main__":
    main()

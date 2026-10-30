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



def count_whole_placed_cnf_models(n, gates, output):
    """Full 4g+1-clause CNF of the source DAG; count every finite model.

    The existing test's ('g',i) uses creation-order indexing; Agda's actual
    GateProgram.GateWire uses newest-first. We explicitly convert between
    these views before mapping into the original Tseitin numeric index.
    """
    clauses = []
    for older, (op, args) in enumerate(gates):
        new_output = n + older
        def index(w):
            if w[0] == "i":
                return w[1]
            newest_first = older - 1 - w[1]
            assert 0 <= newest_first < older
            return n + older - 1 - newest_first
        left_idx = new_output if op == "const" else index(args[0])
        right_idx = index(args[1]) if op in ("and", "or") else new_output
        for row in product((False, True), repeat=3):
            o, left, right = row
            expected = {
                "const": lambda: args[0],
                "not": lambda: not left,
                "and": lambda: left and right,
                "or": lambda: left or right,
            }[op]()
            if o != expected:
                clauses.append(((new_output, not o), (left_idx, not left),
                                (right_idx, not right)))
    final_index = output[1] if output[0] == "i" else n + output[1]
    clauses.append(((final_index, True),))
    assert len(clauses) == 4 * len(gates) + 1
    return sum(all(any(bits[j] == sign for j, sign in clause)
                   for clause in clauses)
               for bits in product((False, True), repeat=n + len(gates)))

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
    assert n_input_accept == count_whole_placed_cnf_models(n, gates, output)
    return n_input_accept



def check_local_three_bit_gate_cnf():
    """Original fixed-width truth-table CNF, specialized to DAG gate predicates.

    Explicitly different from expanding a whole n-bit circuit truth table.
    """
    kinds = ("const-false", "const-true", "not", "and", "or")
    rows = tuple(product((False, True), repeat=3))
    def predicate(kind, bits):
        output, left, right = bits
        expected = {
            "const-false": False,
            "const-true": True,
            "not": not left,
            "and": left and right,
            "or": left or right,
        }[kind]
        return output == expected

    for kind in kinds:
        # Original CNF.truthTableCNF excludes each rejected local row.
        clauses = [tuple((i, not bit) for i, bit in enumerate(row))
                   for row in rows if not predicate(kind, row)]
        assert len(clauses) <= 8
        assert all(len(clause) == 3 for clause in clauses)
        for candidate in rows:
            compiled = all(any(candidate[index] == literal
                               for index, literal in clause)
                           for clause in clauses)
            assert compiled == predicate(kind, candidate), (kind, candidate)
    print("PASS: 40 local three-bit gate/CNF evaluations; <=8 width-3 clauses")


def check_placed_gate_index_semantics():
    """Validate the same gate index mapping used by the Agda Fin placement.

    Earlier gate refs are newest-first (Fin.zero is the most recent gate),
    whereas the shared Tseitin numeric index is creation-time.
    """
    checked = 0
    for n in (1, 2):
        for older in (0, 1, 2):
            wires = [("i", j) for j in range(n)] + [("g", j) for j in range(older)]
            gates = [("const", (False,)), ("const", (True,))]
            gates += [("not", (src,)) for src in wires]
            gates += [(op, (a, b)) for op in ("and", "or")
                      for a in wires for b in wires]
            def wire_index(w):
                return w[1] if w[0] == "i" else n + older - 1 - w[1]
            for op, args in gates:
                output_index = n + older
                left_index = output_index if op == "const" else wire_index(args[0])
                right_index = (wire_index(args[1]) if op in ("and", "or")
                               else output_index)
                assert all(0 <= index <= output_index
                           for index in (left_index, right_index))
                def predicate(row):
                    out, left, right = row
                    target = {
                        "const": lambda: args[0],
                        "not": lambda: not left,
                        "and": lambda: left and right,
                        "or": lambda: left or right,
                    }[op]()
                    return out == target

                rows = tuple(product((False, True), repeat=3))
                excluded = [row for row in rows if not predicate(row)]
                assert len(excluded) == 4
                for bits in product((False, True), repeat=output_index + 1):
                    local = (bits[output_index], bits[left_index],
                             bits[right_index])
                    compiled = all(any(local[i] != row[i] for i in range(3))
                                   for row in excluded)
                    assert compiled == predicate(local), (n, older, op, args, bits)
                    checked += 1
    print(f"PASS: {checked} finite-index placed-gate cases")

def main():
    tests = 0
    for n in (1, 2):
        # Existing literal DAG owner permits zero gates and an input output.
        # Exercise that boundary before extending to programs with gates.
        for output in [("i", i) for i in range(n)]:
            count_both(n, (), output)
            tests += 1
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

    assert tests == 59293

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
    check_local_three_bit_gate_cnf()
    check_placed_gate_index_semantics()
    print(f"PASS: {tests} exhaustive DAG/output cases: input = canonical Tseitin = full 4g+1 CNF counts")
    print("PASS: one-way-gate and unconstrained-tail counterexamples")


if __name__ == "__main__":
    main()

"""Search exact n-cycle truth tables for TopForm circuits with a residual edge (0, 1)."""

import argparse

import z3


def pick(index, values):
    value = values[-1]
    for i in range(len(values) - 2, -1, -1):
        value = z3.If(index == i, values[i], value)
    return value


def bit(vector, at):
    return z3.Extract(at, at, vector) == 1


def solve(n, m, require_residual, seconds, fixture=False, compressed=False,
          graph_edges=None, query_edge=(0, 1), minimum=False):
    assert n >= 5 and m >= 1
    if graph_edges is None:
        graph_edges = [(v, (v + 1) % n) for v in range(n)]
        graph_name = f"C_{n}"
    else:
        graph_name = f"G({n}, {len(graph_edges)})"
    edges = [(1 << a) | (1 << b) for a, b in graph_edges]
    is_positive = [any(assignment & edge == edge for edge in edges)
                   for assignment in range(1 << n)]
    if compressed:
        maximal_independent = [
            x for x, on in enumerate(is_positive) if not on and
            all(x & (1 << v) or is_positive[x | (1 << v)] for v in range(n))
        ]
        cases = edges + maximal_independent
    else:
        cases = list(range(1 << n))
    case_index = {assignment: i for i, assignment in enumerate(cases)}
    truth_width = len(cases)
    wire_count = n + m
    index_width = wire_count.bit_length()
    target = sum(1 << i for i, assignment in enumerate(cases) if is_positive[assignment])
    forbidden = ((1 << truth_width) - 1) ^ target

    solver = z3.SolverFor("QF_BV")
    solver.set(timeout=seconds * 1000)
    values = [z3.BitVecVal(sum(1 << i for i, x in enumerate(cases) if x & (1 << v)), truth_width)
              for v in range(n)]
    or_leaves = [z3.BitVecVal(1 << v, wire_count) for v in range(n)]
    cones = [z3.BitVecVal(0, m) for _ in range(n)]
    gates = []
    operands = []
    tops = []
    junks = []
    top_mask = z3.BitVecVal(0, m)
    depths = [z3.BitVecVal(0, index_width) for _ in range(n)]
    for j in range(m):
        w = n + j
        l = z3.BitVec(f"left{j}", index_width)
        r = z3.BitVec(f"right{j}", index_width)
        is_and = z3.Bool(f"and{j}")
        solver.add(z3.ULT(l, r) if minimum else z3.ULE(l, r), z3.ULT(r, w))
        if minimum:
            left_depth, right_depth = pick(l, depths), pick(r, depths)
            depth = z3.BitVec(f"depth{j}", index_width)
            solver.add(depth == 1 + z3.If(z3.ULT(left_depth, right_depth), right_depth, left_depth))
            if j > 0:
                op_prev, l_prev, r_prev = gates[-1]
                prev_depth = depths[-1]
                ordered_key = z3.Concat(z3.If(is_and, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1)), l, r)
                prev_key = z3.Concat(z3.If(op_prev, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1)),
                                     l_prev, r_prev)
                solver.add(z3.ULE(prev_depth, depth),
                           z3.Implies(prev_depth == depth, z3.ULT(prev_key, ordered_key)))
            depths.append(depth)
        left, right = pick(l, values), pick(r, values)
        output = z3.BitVec(f"value{j}", truth_width)
        solver.add(output == z3.If(is_and, left & right, left | right))

        l_leaf, r_leaf = pick(l, or_leaves), pick(r, or_leaves)
        leaf_mask = z3.BitVec(f"leaves{j}", wire_count)
        solver.add(leaf_mask == z3.If(is_and, z3.BitVecVal(1 << w, wire_count), l_leaf | r_leaf))
        strict_cone = pick(l, cones) | pick(r, cones)
        cone = z3.BitVec(f"cone{j}", m)
        solver.add(cone == strict_cone | (1 << j))

        below = (output & forbidden) == 0
        top = z3.And(is_and, below)
        junk = z3.And(is_and, z3.Not(below))
        if require_residual:
            solver.add(z3.Implies(is_and, strict_cone & top_mask == 0))
        top_mask = top_mask | z3.If(top, z3.BitVecVal(1 << j, m), z3.BitVecVal(0, m))
        values.append(output)
        or_leaves.append(leaf_mask)
        cones.append(cone)
        gates.append((is_and, l, r))
        operands.append((l_leaf, r_leaf))
        tops.append(top)
        junks.append(junk)
    solver.add(values[-1] == target)
    if minimum:
        # Equality on the selected monotone boundary tests permits alias deletion.
        # Reachability of all wires follows from leastness and input relevance.
        solver.add(z3.Distinct(*values))
        for w in range(wire_count - 1):
            solver.add(z3.Or(*(z3.Or(l == w, r == w) for _, l, r in gates)))

    if fixture:
        assert (n, m) == (5, 12)
        expected = [
            ("or", 1, 4), ("or", 0, 2), ("or", 0, 3), ("and", 6, 7),
            ("or", 0, 1), ("and", 8, 9), ("and", 5, 10), ("or", 1, 3),
            ("and", 2, 12), ("and", 3, 4), ("or", 11, 13), ("or", 14, 15),
        ]
        for (op, l, r), (kind, a, b) in zip(gates, expected, strict=True):
            solver.add(op == (kind == "and"), l == a, r == b)

    if require_residual:
        a, b = query_edge
        assert ((1 << a) | (1 << b)) in edges
        direct_edges, exposed, witnessed = [], [], []
        for j, (left, right) in enumerate(operands):
            direct_edges.append(z3.And(tops[j], z3.Or(
                z3.And(bit(left, a), bit(right, b)), z3.And(bit(left, b), bit(right, a)))))
            for g in range(j):
                child_l, child_r = operands[g]
                raw_l = z3.Or(bit(child_l, a), bit(child_l, b))
                raw_r = z3.Or(bit(child_r, a), bit(child_r, b))
                reach = z3.Or(
                    z3.And(z3.Or(bit(left, a), bit(left, b)), bit(right, n + g)),
                    z3.And(z3.Or(bit(right, a), bit(right, b)), bit(left, n + g)),
                )
                context = z3.And(tops[j], junks[g], reach)
                exposed.append(z3.And(context, raw_l, raw_r))
                witnessed.append(z3.And(context, bit(values[n + g], case_index[(1 << a) | (1 << b)])))
        solver.add(z3.Or(witnessed), z3.Not(z3.Or(exposed)), z3.Not(z3.Or(direct_edges)))

    outcome = solver.check()
    print(f"{graph_name}, gates={m}, residual={require_residual}, edge={query_edge}: {outcome}",
          flush=True)
    if outcome == z3.sat:
        model = solver.model()
        for j, (op, l, r) in enumerate(gates):
            kind = "and" if z3.is_true(model.eval(op)) else "or"
            print(f"  {n + j}: {kind} {model.eval(l).as_long()}, {model.eval(r).as_long()}")
    elif outcome == z3.unknown:
        print(solver.reason_unknown(), flush=True)
    return outcome


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("vertices", type=int)
    parser.add_argument("gates", type=int)
    parser.add_argument("--seconds", type=int, default=90)
    parser.add_argument("--unrestricted", action="store_true")
    parser.add_argument("--fixture", action="store_true")
    parser.add_argument("--compressed", action="store_true")
    parser.add_argument("--minimum", action="store_true")
    args = parser.parse_args()
    solve(args.vertices, args.gates, not args.unrestricted, args.seconds, args.fixture,
          args.compressed, minimum=args.minimum)

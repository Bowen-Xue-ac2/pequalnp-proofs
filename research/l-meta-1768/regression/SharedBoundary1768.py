r"""L-meta-1768 Card 2 -- shared boundary of the explicit AND(u,W) and batch ledgers.

Reuses `SharedBirth1768.build(p)` (the non-minimal host), `ReadMultiplicity1768`
(certificate multiplicity) and the affine incidence graph.  Writes no file.

Objects
-------
For a line u let

    top_u    = AND(u, masked_u)            (the explicit AND(u, W), W = masked_u)
    masked_u = AND(birth, support_u)
    support_u= AND over the 2^3 choice clauses OR(choice_1,choice_2,choice_3, N(u))
    birth    = AND(left_last, right_last)  (left = OR of all lines, right = OR of all points)

The *private cone* C_u is the part of the backward cone of W that is used only by
top_u: `{masked_u} + {support_u} + the 8 clause chains` (8p+24 gates).  The wire
`birth` is read by every `masked_u` and by nothing else; it is therefore the single
shared boundary wire of every private cone.  On an incidence edge {u,v} the input u
is actually read twice: once at the mouth `top_u` and once on the shared left fold
under `birth`.  All p^3 incidence edges are high-multiplicity witnesses (capped
state (2,2) for both endpoints).

The original (residual) graph is the p^3 incidence edges; the 3p^2 private matching
edges are control edges (they are not part of the original graph, but they are graph
edges used to keep the private supports clean and to reject independent sets).

Candidates (batch K = a set of anchors / external readers of birth)
--------------------------------------------------------------------
Z  zero the boundary at K: `masked_u := 0`           (downward; loses p edges/anchor)
B  bypass the common AND at K: `masked_u := support_u`          (upward, safe, loss 0)
P  B plus cutting every partner blocking condition in support_u, without repair
   (upward, safe, loses p edges/anchor)
C  P plus one AND(u,v) per lost edge and one OR mouth (upward, safe, loss 0)
G  group-mouth rewrite: replace the whole private cone and top by AND(u, OR(N(u)))
   (upward, safe, loss 0; at K = all anchors this is the known 299/685-gate circuit)
X  sample unsafe upward variant: bypass and set support_u := true (no repair);
   it accepts the independent singleton {u}.  Marked as a sample, not a candidate
   that is safe.

Every row reports the cut domain, the gates that become truly dead, the repair gates
added, the net saved gates, every lost original edge and every lost control edge.
Safety is checked twice: (i) every assignment of each modified top's input support is
enumerated, so `top=true => the assignment contains an edge` holds on all global
assignments (this also proves every host top safe, because the host top is B's top
with the extra conjunct birth); (ii) the whole output is checked on the complete
dominating family T(u) x (all 27 private patterns), where T(u) = {u} + (points \
N(u)) is maximal independent in the incidence graph. Its point set contains all
possible points of an independent assignment that contains u.
The X row prints an explicit independent negative sample.

The host is non-minimal.  By `ZeroGate1768.least_safe_repair_bound` a safe IsAO2
circuit D with L lost graph edges satisfies m <= |D| + 2|L|, i.e. net saving <= 2|lost|.
Every safe candidate below has net saving > 2*lost (positive *slack*), so it is a
non-minimality certificate.  B/C/G even accept every edge, so they compute F exactly
and are strictly smaller exact circuits.  Nothing here proves the mainline target;
it calibrates the non-minimal regime and the exact budgets.
"""

import sys
from collections import defaultdict
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ReadMultiplicity1768 import certificate_states, state_list
from SharedBirth1768 import build
from SharedStop1768 import evaluate, indicators
from SlotFreeCoreExample1768 import incidence_graph

CANDIDATES = ("Z", "B", "P", "C", "G", "X")
MODE = {
    "Z": "zero",
    "B": "bypass",
    "P": "prune",
    "C": "prune_repair",
    "G": "star",
    "X": "unsafe",
}


# --------------------------------------------------------------------- circuit builder
def fold(gates, prefix, op, wires):
    head = wires[0]
    for i, wire in enumerate(wires[1:], start=1):
        name = f"{prefix}.{i}"
        gates.append((name, op, head, wire))
        head = name
    return head


def build_variant(p, batch):
    """Rebuild the host with the anchors in `batch` (dict u -> candidate letter)."""
    points, neighborhoods = incidence_graph(p)
    lines = list(neighborhoods)
    inputs = points + lines
    gates = []
    modes = {u: MODE[letter] for u, letter in batch.items()}
    # Only orig anchors read birth; zero/bypass/prune/star/unsafe all remove it.
    if any(modes.get(u, "orig") == "orig" for u in lines):
        left = fold(gates, "left", "or", lines)
        right = fold(gates, "right", "or", points)
        gates.append(("birth", "and", left, right))
        birth = "birth"
    else:
        birth = None

    top_wires = []
    for u in lines:
        mode = modes.get(u, "orig")
        pairs = [(f"{u}.a{i}", f"{u}.b{i}") for i in range(3)]
        inputs.extend(vertex for pair in pairs for vertex in pair)
        choices = list(product(*pairs))
        if mode in ("orig", "bypass", "prune", "prune_repair"):
            pruned = mode in ("prune", "prune_repair")
            clauses = [
                fold(gates, f"{u}.clause{i}", "or",
                     list(choice) if pruned else [*choice, *neighborhoods[u]])
                for i, choice in enumerate(choices)
            ]
            support = fold(gates, f"{u}.support", "and", clauses)
            top = f"{u}.top"
            if mode == "orig":
                masked = f"{u}.masked"
                gates.append((masked, "and", birth, support))
                gates.append((top, "and", u, masked))
            else:
                gates.append((top, "and", u, support))
            top_wires.append(top)
            if mode == "prune_repair":
                terms = []
                for k, v in enumerate(neighborhoods[u]):
                    name = f"{u}.repair.{k}"
                    gates.append((name, "and", u, v))
                    terms.append(name)
                top_wires.append(fold(gates, f"{u}.repair_or", "or", terms))
        elif mode == "star":
            star = fold(gates, f"{u}.star", "or", neighborhoods[u])
            top = f"{u}.startop"
            gates.append((top, "and", u, star))
            top_wires.append(top)
        elif mode == "zero":
            pass
        elif mode == "unsafe":
            top_wires.append(u)  # output reads the input directly
        else:
            raise ValueError(mode)
        for i, (a, b) in enumerate(pairs):
            name = f"{u}.private{i}"
            gates.append((name, "and", a, b))
            top_wires.append(name)

    output = fold(gates, "output", "or", sorted(top_wires))
    return inputs, gates, output


# --------------------------------------------------------------------- base bookkeeping
def base_data(p):
    inputs, gates, edges, neighborhoods, starts, birth, tops, root = build(p)
    return {
        "inputs": inputs,
        "gates": gates,
        "edges": edges,
        "ns": neighborhoods,
        "starts": starts,
        "birth": birth,
        "tops": tops,
        "root": root,
    }


def edge_sets(ns):
    residual = {frozenset((u, v)) for u in ns for v in ns[u]}
    control = {
        frozenset((f"{u}.a{i}", f"{u}.b{i}")) for u in ns for i in range(3)
    }
    return residual, control


def bit(mask, i):
    return (mask >> i) & 1


def check_ao2(inputs, gates):
    """Every gate is binary AND/OR and reads only inputs or earlier gates."""
    seen = set(inputs)
    assert len(seen) == len(inputs)
    for name, op, left, right in gates:
        assert op in ("and", "or"), (name, op)
        assert left in seen and right in seen, (name, left, right)
        assert name not in seen, name
        seen.add(name)
    return seen


# --------------------------------------------------------------------- boundary enumeration
def enumerate_boundary(p):
    data = base_data(p)
    gates, ns, starts, birth = data["gates"], data["ns"], data["starts"], data["birth"]
    lines = list(ns)
    points = [v for v in data["inputs"] if v.startswith("P")]
    table = {name: (op, left, right) for name, op, left, right in gates}
    readers = defaultdict(list)
    for name, _, left, right in gates:
        readers[left].append(name)
        readers[right].append(name)

    memo = {}

    def ancestors(wire):
        if wire in memo:
            return memo[wire]
        if wire not in table:
            return frozenset()
        op, left, right = table[wire]
        out = frozenset((wire,)) | ancestors(left) | ancestors(right)
        memo[wire] = out
        return out

    boundary_rows = []
    residual, _ = edge_sets(ns)
    residual = sorted(residual, key=lambda e: tuple(sorted(e)))
    edge_index = {edge: i for i, edge in enumerate(residual)}
    edge_values = evaluate(gates, indicators(data["inputs"], residual))
    assert all(bit(edge_values[data["root"]], i) for i in range(len(residual)))
    assert len(readers[birth]) == len(lines)
    assert sorted(readers[birth]) == sorted(f"{u}.masked" for u in lines)
    total_witnesses = 0
    for u in lines:
        top, masked = starts[u]
        cone = ancestors(masked) - ancestors(birth) - {birth}
        boundary = set()
        for gate in cone:
            for child in table[gate][1:]:
                if child in table and child not in cone:
                    boundary.add(child)
        assert boundary == {birth}, (p, u, boundary)
        direct_readers = readers[u]
        assert len(direct_readers) == 2, (p, u, direct_readers)
        # every incident edge is a high-multiplicity witness, and both direct
        # readers of u are true on its pair assignment.
        witnesses = 0
        for v in ns[u]:
            states = state_list(certificate_states(gates, data["inputs"], u, v)[
                data["root"]])
            assert states == [(2, 2)], (p, u, v, states)
            edge = frozenset((u, v))
            assert bit(edge_values[data["root"]], edge_index[edge])
            assert all(bit(edge_values[reader], edge_index[edge])
                       for reader in direct_readers), (p, u, v)
            witnesses += 1
        total_witnesses += witnesses
        boundary_rows.append({
            "u": u,
            "top": top,
            "masked": masked,
            "cone": len(cone),
            "direct_readers": tuple(direct_readers),
            "witnesses": witnesses,
            "external": len([r for r in readers[birth] if r not in cone]),
        })
    assert total_witnesses == p ** 3
    assert all(row["cone"] == 8 * p + 24 for row in boundary_rows)

    shared = 2 * (len(lines) - 1) + 1
    per_anchor = 8 * p + 28
    m = len(gates)
    assert m == len(lines) * per_anchor + shared + (4 * len(lines) - 1)

    print(f"p={p}: boundary enumeration")
    print(f"  inputs={len(data['inputs'])}, gates={m}, residual edges={p ** 3}, "
          f"control edges={3 * len(lines)}, anchors={len(lines)}")
    print(f"  private cone C_u = clauses+support+masked = {8 * p + 24} gates; "
          f"private cones total {len(lines) * (8 * p + 24)}")
    print(f"  shared boundary: birth (1 wire), read by all {len(lines)} masked_u "
          f"(fan-out {len(lines)}); shared prefix left+right+birth = {shared} gates")
    print(f"  high-multiplicity witnesses: {total_witnesses} = {len(lines)} anchors x {p}; "
          f"each has capped state (2,2) and exactly 2 direct read sites of u")
    for row in boundary_rows:
        print(f"    {row['u']}: {row['witnesses']} witnesses; direct readers of u = "
              f"{row['direct_readers']}; C_u={row['cone']} gates; "
              f"boundary=birth; external readers of birth outside C_u = "
              f"{row['external']}")
    return boundary_rows, m


# --------------------------------------------------------------------- safety family
def private_patterns(u):
    for code in range(27):
        chosen, rest = [], code
        for i in range(3):
            digit, rest = rest % 3, rest // 3
            if digit == 1:
                chosen.append(f"{u}.a{i}")
            elif digit == 2:
                chosen.append(f"{u}.b{i}")
        yield frozenset(chosen)


def safety_family(p, ns, points):
    lines = list(ns)
    tests = []
    for u in lines:
        base = frozenset({u} | (set(points) - set(ns[u])))
        for pattern in private_patterns(u):
            tests.append(base | pattern)
    return tests


def support_signals(names):
    """Truth tables over all 2^m subsets of `names`, as big integers."""
    m = len(names)
    size = 1 << m
    signals = {}
    for j, name in enumerate(names):
        half = 1 << j
        period = half << 1
        block = ((1 << half) - 1) << half
        repeats = ((1 << size) - 1) // ((1 << period) - 1)
        signals[name] = block * repeats
    return signals


def local_top_safety(p, letter):
    """Exhaust every assignment to the input support of every modified top.

    For every anchor u, the modified top of candidate `letter` is evaluated on
    all 2^|support| assignments of u, N(u) and u's six private bits.  If the top
    is true only when the assignment contains an original or control edge, then
    the top is below F on *all* assignments, not only on independent sets.
    B's top is AND(u, support_u); the host top is the same AND with the extra
    conjunct birth, so this check also proves that every host top is below F.
    """
    _, ns = incidence_graph(p)
    lines = list(ns)
    _, gates, _ = build_variant(p, {u: letter for u in lines})
    table = {name: (op, left, right) for name, op, left, right in gates}
    residual, control = edge_sets(ns)
    all_edges = residual | control
    failures = []
    for u in lines:
        if letter == "X":
            top = u
        elif letter == "G":
            top = f"{u}.startop"
        else:
            top = f"{u}.top"
        if top in table:
            needed, stack = set(), [top]
            while stack:
                wire = stack.pop()
                if wire in needed or wire not in table:
                    continue
                needed.add(wire)
                _, left, right = table[wire]
                stack.extend((left, right))
            cone = [gate for gate in gates if gate[0] in needed]
            operands = {wire for gate in cone for wire in gate[2:]}
            support_inputs = sorted(operands - needed)
        else:
            cone, support_inputs = [], [u]
        size = 1 << len(support_inputs)
        signals = support_signals(support_inputs)
        values = dict(signals)
        for name, op, left, right in cone:
            values[name] = (values[left] | values[right] if op == "or"
                            else values[left] & values[right])
        cover = 0
        for edge in all_edges:
            if edge <= set(support_inputs):
                inside = (1 << size) - 1
                for wire in edge:
                    inside &= signals[wire]
                cover |= inside
        true_mask = values[top]
        fail = true_mask & ~cover & ((1 << size) - 1)
        if fail:
            first = (fail & -fail).bit_length() - 1
            assignment = frozenset(
                support_inputs[j] for j in range(len(support_inputs))
                if first >> j & 1
            )
            failures.append((u, assignment))
    return len(lines), failures


def variant_structure_safety(p, letter):
    """Every repair gate of C is AND(u,v) with {u,v} an original edge."""
    _, ns = incidence_graph(p)
    residual, control = edge_sets(ns)
    all_edges = residual | control
    if letter != "C":
        return 0
    lines = list(ns)
    _, gates, _ = build_variant(p, {u: letter for u in lines})
    checked = 0
    for name, op, left, right in gates:
        if ".repair." in name:
            assert op == "and"
            assert frozenset((left, right)) in all_edges, (name, left, right)
            checked += 1
    return checked


def independence_checks(p, ns, points, tests, all_edges):
    lines = list(ns)
    for u in lines:
        base = frozenset({u} | (set(points) - set(ns[u])))
        assert not any(edge <= base for edge in all_edges)
        # Maximal in the incidence graph: every outside line or point touches the test.
        for v in points + lines:
            if v in base:
                continue
            neighbors = set(ns[v]) if v in ns else {
                w for w, ws in ns.items() if v in ws
            }
            assert neighbors & base, (p, u, v)
    for test in tests:
        assert not any(edge <= test for edge in all_edges)


# --------------------------------------------------------------------- candidate ledger
def ledger(p, letter, batch_lines):
    data = base_data(p)
    ns = data["ns"]
    lines = list(ns)
    points = [v for v in data["inputs"] if v.startswith("P")]
    base_gates = data["gates"]
    base_root = data["root"]
    a = len(lines)
    assert set(batch_lines) <= set(lines)
    assert len(set(batch_lines)) == len(batch_lines)

    inputs, gates, output = build_variant(p, {u: letter for u in batch_lines})
    check_ao2(inputs, gates)
    assert output in {name for name, _, _, _ in gates}
    # the all-orig rebuild must be the host itself
    if not batch_lines:
        assert gates == base_gates, "all-orig rebuild differs from SharedBirth"
        assert inputs == data["inputs"]
    check_ao2(data["inputs"], base_gates)

    residual, control = edge_sets(ns)
    residual = sorted(residual, key=lambda e: tuple(sorted(e)))
    control = sorted(control, key=lambda e: tuple(sorted(e)))
    edge_list = residual + control
    safety = safety_family(p, ns, points)
    samples = [frozenset({u}) for u in lines]
    assignments = list(dict.fromkeys(edge_list + safety + samples))
    index = {x: i for i, x in enumerate(assignments)}
    mask_all = (1 << len(assignments)) - 1

    base_values = evaluate(base_gates, indicators(data["inputs"], assignments))
    values = evaluate(gates, indicators(inputs, assignments))
    edge_mask = (1 << len(edge_list)) - 1
    safety_mask = ((1 << len(safety)) - 1) << len(edge_list)
    assert base_values[base_root] & edge_mask == edge_mask
    assert base_values[base_root] & safety_mask == 0

    lost_res = sum(
        1 for e in residual if not bit(values[output], index[e])
    )
    lost_ctrl = sum(
        1 for e in control if not bit(values[output], index[e])
    )
    lost_res_set = {e for e in residual if not bit(values[output], index[e])}
    lost_ctrl_set = {e for e in control if not bit(values[output], index[e])}
    if letter in ("Z", "P"):
        expected = {frozenset((u, v)) for u in batch_lines for v in ns[u]}
        assert lost_res_set == expected, (p, letter, sorted(lost_res_set)[:3])
    elif letter in ("B", "C", "G", "X"):
        assert not lost_res_set
    assert not lost_ctrl_set
    bad = [
        (assignment, i)
        for i, assignment in enumerate(assignments[len(edge_list):], len(edge_list))
        if bit(values[output], i)
    ]

    # cut domain / dead / added / net, excluding the output fold
    base_names = {name for name, _, _, _ in base_gates if not name.startswith("output.")}
    var_names = {name for name, _, _, _ in gates if not name.startswith("output.")}
    out_base = sum(1 for name, _, _, _ in base_gates if name.startswith("output."))
    out_var = sum(1 for name, _, _, _ in gates if name.startswith("output."))
    assert out_base == 4 * a - 1
    cut = base_names - var_names
    added_names = var_names - base_names
    shared_cut = sum(1 for name in cut if name == "birth"
                     or name.startswith("left.") or name.startswith("right."))
    m = len(base_gates)
    m_var = len(gates)
    dead = len(cut) + max(0, out_base - out_var)
    added = len(added_names) + max(0, out_var - out_base)
    net = dead - added
    assert net == m - m_var, (p, letter, len(batch_lines), dead, added, m, m_var)

    safe = not bad
    slack = net - 2 * (lost_res + lost_ctrl)
    # B/C/G accept every edge and are safe, hence compute F exactly by monotonicity.
    exact = False
    if letter in ("B", "C", "G"):
        assert lost_res == 0 and lost_ctrl == 0
        exact = True
    # downward candidate: the rewritten output never exceeds the host output
    downward = (letter == "Z")
    if downward:
        assert values[output] & ~base_values[base_root] & mask_all == 0
    # structural safety: every new top is implied by an original or control edge
    if letter in ("B", "P", "C", "G"):
        assert safe, (p, letter, len(batch_lines), bad[:3])
        assert slack > 0
    if letter == "Z":
        assert safe and slack > 0

    return {
        "letter": letter,
        "p": p,
        "a": a,
        "r": len(batch_lines),
        "batch": list(batch_lines),
        "m": m,
        "m_var": m_var,
        "cut": len(cut),
        "shared_cut": shared_cut,
        "private_cut": len(cut) - shared_cut,
        "dead": dead,
        "added": added,
        "net": net,
        "lost_res": lost_res,
        "lost_ctrl": lost_ctrl,
        "kept_res": len(residual) - lost_res,
        "kept_ctrl": len(control) - lost_ctrl,
        "slack": slack,
        "safe": safe,
        "exact": exact,
        "bad": bad,
        "downward": downward,
        "witness": min(bad, key=lambda item: (len(item[0]), sorted(item[0])))[0]
        if bad else None,
        "witness_size": len(min(bad, key=lambda item: len(item[0]))[0]) if bad else None,
    }


# --------------------------------------------------------------------- reporting
def print_scopes(p):
    print(f"p={p}: cut domains and directions")
    print("  Z down: for u in K delete top_u, masked_u, support_u and the 8 clause "
          "chains; the output fold loses one input per u; if K = all anchors the")
    print("          shared prefix (left+right+birth) also dies.")
    print("  B up:   for u in K delete masked_u only; top_u := AND(u, support_u). "
          "If K = all anchors the shared prefix dies.")
    print("  P up:   as B, then prune all p partner leaves from all 8 clauses "
          "(8p gates per u) and keep the pruned support/top; no repair.")
    print("  C up:   as P, then add one AND(u,v) per lost edge and one OR mouth "
          "per anchor; the pruned support/top stay as the retained witness.")
    print("  G up:   for u in K delete the whole private cone and top, then add "
          "OR(N(u)) and AND(u, OR(N(u))).")
    print("  X up:   SAMPLE only: bypass birth and replace support_u by true "
          "(no repair); the output reads u directly. Not safe.")


def print_table(p, a, shared):
    lines = list(incidence_graph(p)[1])
    sizes = list(dict.fromkeys([1, p, a // 2, a - 1, a]))
    print(f"p={p}: batch candidates (r = anchors in K; |K| = p*r witnesses; "
          f"shared prefix = {shared} gates)")
    print("  lossR/lossC count every edge of E_res/E_ctrl; Z/P lose exactly "
          "{ {u,v} : u in K, v in N(u) }, B/C/G/X lose no residual edge, "
          "all safe rows keep every control edge")
    header = (f"  {'cand':>4} {'dir':>4} {'r':>3} {'|K|':>4} {'cut':>5} "
              f"{'shared':>6} {'dead':>5} {'add':>4} {'net':>5} {'lossR':>5} "
              f"{'lossC':>5} {'slack':>6} {'safe':>4} {'m':>5} "
              f"{'net/|K|':>7} {'loss/|K|':>8} {'slack/|K|':>9}")
    print(header)
    for letter in CANDIDATES:
        for r in sizes:
            row = ledger(p, letter, lines[:r])
            k = p * r
            direction = "down" if row["downward"] else "up"
            print(f"  {letter:>4} {direction:>4} {r:>3} {k:>4} {row['cut']:>5} "
                  f"{row['shared_cut']:>6} {row['dead']:>5} {row['added']:>4} "
                  f"{row['net']:>5} {row['lost_res']:>5} {row['lost_ctrl']:>5} "
                  f"{row['slack']:>6} {str(row['safe']):>4} {row['m_var']:>5} "
                  f"{row['net'] / k:>7.3f} "
                  f"{(row['lost_res'] + row['lost_ctrl']) / k:>8.3f} "
                  f"{row['slack'] / k:>9.3f}")
            if letter == "X" and row["witness"] is not None:
                print(f"       sample negative: {sorted(row['witness'])} "
                      f"({row['witness_size']} inputs, independent, F=0, "
                      f"rewritten output=1)")
            elif letter == "G" and r == a:
                print(f"       full group-mouth circuit: {row['m_var']} gates "
                      f"(known direct circuit)")
    return sizes


def print_overlap(p, a, shared):
    lines = list(incidence_graph(p)[1])
    print(f"p={p}: budget-overlap checks (disjoint batches; shared cut counted once)")
    for letter in ("Z", "B", "P", "C", "G"):
        r0 = max(1, p)
        first, second = lines[:r0], lines[r0:2 * r0]
        one = ledger(p, letter, first)
        two = ledger(p, letter, second)
        union = ledger(p, letter, first + second)
        if 2 * r0 < a:
            assert union["net"] == one["net"] + two["net"]
            assert union["shared_cut"] == 0
            print(f"  {letter}: r={r0}+{r0}: {one['net']}+{two['net']}="
                  f"{union['net']}; shared=0; additive")
        else:
            assert union["net"] == one["net"] + two["net"] + shared
            print(f"  {letter}: r={r0}+{r0}: {one['net']}+{two['net']}+{shared}="
                  f"{union['net']}; shared={shared} once")
        full = ledger(p, letter, lines)
        rest = ledger(p, letter, lines[r0:])
        assert full["net"] == one["net"] + rest["net"] + shared
        print(f"  {letter}: full {a} = {r0}+{a - r0} + shared {shared}: "
              f"{full['net']} = {one['net']}+{rest['net']}+{shared}; "
              f"m'={full['m_var']}")


def print_summary(p, a):
    lines = list(incidence_graph(p)[1])
    print(f"p={p}: mainline calibration (non-minimal host; no proof claim)")
    for letter in ("Z", "B", "P", "C", "G", "X"):
        row = ledger(p, letter, lines)
        k = p * a
        loss = row["lost_res"] + row["lost_ctrl"]
        print(f"  {letter}: |K|={k}, net={row['net']}, "
              f"keptR={row['kept_res']}, lostR={row['lost_res']}, "
              f"keptC={row['kept_ctrl']}, lostC={row['lost_ctrl']}, "
              f"c=net/|K|={row['net'] / k:.3f}, l=loss/|K|={loss / k:.3f}, "
              f"c-2l={(row['net'] - 2 * loss) / k:.3f}, "
              f"slack={row['slack']}, safe={row['safe']}, exact={row['exact']}, "
              f"m'={row['m_var']}")
        if row["safe"]:
            assert row["slack"] > 0
    print("  every safe row has slack = net - 2*lost > 0; by ZeroGate's")
    print("  least_safe_repair_bound this certifies that the host is not least.")
    print("  B/C/G are safe and accept every edge, so they compute F exactly")
    print("  (monotone edge agreement); B alone is a strictly smaller exact circuit.")
    print("  least circuits force net <= 2*lost (c <= 2*l for the rewrite); but the")
    print("  target's additive O(m) slack can absorb a constant fraction of m.")
    print("  the displayed saving/loss pairs are non-minimal calibration, not a proof")
    print("  of the target.")


def main():
    for p in (5, 7):
        rows, m = enumerate_boundary(p)
        a = len(rows)
        shared = 2 * (a - 1) + 1
        assert m == len(rows) * (8 * p + 28) + shared + (4 * a - 1)
        points, ns = incidence_graph(p)
        residual, control = edge_sets(ns)
        tests = safety_family(p, ns, points)
        independence_checks(p, ns, points, tests, residual | control)
        print(f"p={p}: {len(tests)} tests T(u) x 27 checked independent; "
              f"each T(u) is a maximal independent set of the incidence graph")
        print()
        print_scopes(p)
        print()
        print(f"p={p}: local support enumeration (all assignments of each top's support)")
        for letter in ("B", "P", "C", "G"):
            count, failures = local_top_safety(p, letter)
            assert not failures, (letter, failures[:3])
            print(f"  {letter}: {count} tops; every assignment of the support of each top "
                  f"satisfies top=true => contains an edge")
        count, failures = local_top_safety(p, "X")
        assert failures
        print(f"  X SAMPLE: {count} tops; first failure at "
              f"{sorted(failures[0][1])} (top=u true, no edge); sample, not safe")
        if variant_structure_safety(p, "C"):
            print(f"  C: {variant_structure_safety(p, 'C')} repair gates are AND(u,v) "
                  f"with {{u,v}} an original edge")
        print()
        print_table(p, a, shared)
        print()
        print_overlap(p, a, shared)
        print()
        print_summary(p, a)
        print()
    print("reproduce: python -B SharedBoundary1768.py")


if __name__ == "__main__":
    main()

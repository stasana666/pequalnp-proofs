"""Reduce a fan-in-two AND/OR circuit on a one-row, one-column promise."""

import argparse
import json
import random
import time
from pathlib import Path


def input_tables(rows, columns):
    row_tables = [((1 << columns) - 1) << (r * columns) for r in range(rows)]
    first_column = sum(1 << (r * columns) for r in range(rows))
    return row_tables + [first_column << c for c in range(columns)]


def gate_value(op, left, right):
    if op == 'or':
        return left | right
    if op == 'and':
        return left & right
    raise ValueError(f'Unsupported gate {op}')


def evaluate(inputs, gates):
    values = inputs.copy()
    for op, a, b in gates:
        if min(a, b) < 0 or max(a, b) >= len(values):
            raise ValueError('Gate reads an invalid wire')
        values.append(gate_value(op, values[a], values[b]))
    return values


def rebuild(n, gates, output, rng, substitute=None):
    """Drop unreachable gates and randomize the order of independent subcircuits."""
    new_gates = []
    names = {i: i for i in range(n)}
    known = {}

    def walk(w):
        if substitute and w == substitute[0]:
            return walk(substitute[1])
        if w in names:
            return names[w]
        op, a, b = gates[w - n]
        if rng.randrange(2):
            a, b = b, a
        a, b = sorted((walk(a), walk(b)))
        key = op, a, b
        if a == b:
            names[w] = a
        else:
            if key not in known:
                known[key] = n + len(new_gates)
                new_gates.append(key)
            names[w] = known[key]
        return names[w]

    new_output = walk(output)
    return new_gates, new_output


def forced_output(values, gates, n, index, output, forced):
    bank = values[:n + index] + [forced]
    for op, a, b in gates[index + 1:]:
        bank.append(gate_value(op, bank[a], bank[b]))
    return bank[output]


def find_reduction(inputs, gates, output, full, rng):
    n = len(inputs)
    values = evaluate(inputs, gates)
    uses = [0] * len(values)
    for _, a, b in gates:
        uses[a] += 1
        uses[b] += 1
    order = list(range(len(gates)))
    rng.shuffle(order)
    for i in order:
        wire = n + i
        care = forced_output(values, gates, n, i, output, 0) ^ forced_output(values, gates, n, i, output, full)
        want = values[wire] & care
        masked = [v & care for v in values[:wire]]
        for w, val in enumerate(masked):
            if val == want:
                return rebuild(n, gates, output, rng, substitute=(wire, w))
        _, left, right = gates[i]
        if all(w < n or uses[w] > 1 for w in (left, right)):
            continue
        for op in ('and', 'or'):
            pool = [w for w, val in enumerate(masked) if (val & want == want if op == 'and' else val | want == want)]
            rng.shuffle(pool)
            for j, a in enumerate(pool):
                for b in pool[:j]:
                    if gate_value(op, masked[a], masked[b]) != want:
                        continue
                    if {a, b} == {left, right}:
                        continue
                    candidate = gates.copy()
                    candidate[i] = (op, a, b)
                    reduced, out = rebuild(n, candidate, output, rng)
                    if len(reduced) < len(gates):
                        return reduced, out
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--rounds', type=int, default=12)
    parser.add_argument('--seed', type=int, default=0)
    args = parser.parse_args()
    doc = json.loads(args.input.read_text())
    rows = [int(x, 0) if isinstance(x, str) else x for x in doc['rows']]
    cols = doc['columns']
    if not rows or cols < 1 or any(not 0 <= x < 1 << cols for x in rows):
        raise ValueError('Invalid graph dimensions or row masks')
    inputs = input_tables(len(rows), cols)
    expected = sum(v << (r * cols) for r, v in enumerate(rows))
    full = (1 << (len(rows) * cols)) - 1
    rng = random.Random(args.seed)
    gates, output = doc['gates'], doc['output']
    if not 0 <= output < len(inputs) + len(gates) or evaluate(inputs, gates)[output] != expected:
        raise ValueError('Input certificate fails the posted table')
    started = time.monotonic()
    start_size = len(gates)
    best, best_out = rebuild(len(inputs), gates, output, rng)
    for round_no in range(args.rounds):
        gates, output = rebuild(len(inputs), best, best_out, rng)
        while (result := find_reduction(inputs, gates, output, full, rng)) is not None:
            candidate, candidate_out = result
            if len(candidate) >= len(gates) or evaluate(inputs, candidate)[candidate_out] != expected:
                raise RuntimeError('Rewritten circuit failed independent full-table replay')
            gates, output = candidate, candidate_out
            print(f'round {round_no + 1}: {len(gates)} gates', flush=True)
        if len(gates) < len(best):
            best, best_out = gates, output
    if evaluate(inputs, best)[best_out] != expected:
        raise RuntimeError('Final certificate fails the complete table')
    doc.update(gates=best, output=best_out)
    args.output.write_text(json.dumps(doc, separators=(',', ':')) + '\n')
    print(f'{start_size} -> {len(best)} gates, {len(rows) * cols} entries, {time.monotonic() - started:.2f}s')


if __name__ == '__main__':
    main()

"""Compute real ranks exactly on every connected labeled graph of orders 2 through 6."""
from itertools import combinations
from math import gcd


def rank(matrix):
    """Fraction-free Gaussian elimination. Dividing out a row gcd preserves rank over Q."""
    rows = [row[:] for row in matrix]
    size = len(rows)
    pivots = 0
    for column in range(size):
        pivot = next((i for i in range(pivots, size) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[pivots], rows[pivot] = rows[pivot], rows[pivots]
        for i in range(pivots + 1, size):
            factor = rows[i][column]
            if factor:
                leading = rows[pivots][column]
                updated = [leading * x - factor * y for x, y in zip(rows[i], rows[pivots])]
                divisor = gcd(*updated) or 1
                rows[i] = [x // divisor for x in updated]
        pivots += 1
    return pivots


def is_connected(adjacency):
    reached = {0}
    frontier = [0]
    while frontier:
        for v, edge in enumerate(adjacency[frontier.pop()]):
            if edge and v not in reached:
                frontier.append(v)
                reached.add(v)
    return len(reached) == len(adjacency)


def check(order):
    possible_edges = list(combinations(range(order), 2))
    checked = ties = 0
    for mask in range(1 << len(possible_edges)):
        if mask.bit_count() < order - 1:
            continue
        adjacency = [[0] * order for _ in range(order)]
        for k, (u, v) in enumerate(possible_edges):
            if (mask >> k) & 1:
                adjacency[u][v] = adjacency[v][u] = 1
        if not is_connected(adjacency):
            continue
        laplacian = [
            [sum(row) if i == j else -entry for j, entry in enumerate(row)]
            for i, row in enumerate(adjacency)
        ]
        adjacency_rank = rank(adjacency)
        laplacian_rank = rank(laplacian)
        trace = sum(laplacian[i][i] for i in range(order))
        power_bound = adjacency_rank ** laplacian_rank
        if laplacian_rank != order - 1 or trace > power_bound:
            raise ArithmeticError((order, mask, trace, adjacency_rank, laplacian_rank))
        if trace > adjacency_rank * 2 ** (order - 2):
            raise ArithmeticError(("linear bound", order, mask))
        checked += 1
        ties += trace == power_bound
    print(f"n={order}: {checked} connected labeled graphs, {ties} equalities")


if __name__ == "__main__":
    for n in range(2, 7):
        check(n)

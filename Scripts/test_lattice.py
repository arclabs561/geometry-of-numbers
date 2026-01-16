import math

def find_lattice_points(n, u, v, radius_sq):
    points = []
    limit_c = int(math.sqrt(radius_sq))
    for c in range(-limit_c, limit_c + 1):
        rem_sq_c = radius_sq - c**2
        if rem_sq_c < 0: continue
        limit_val = math.sqrt(rem_sq_c)
        min_a = int(math.floor((-limit_val - u*c) / n))
        max_a = int(math.ceil((limit_val - u*c) / n))
        for a in range(min_a - 1, max_a + 2):
            x = n*a + u*c
            min_b = int(math.floor((-limit_val - v*c) / n))
            max_b = int(math.ceil((limit_val - v*c) / n))
            for b in range(min_b - 1, max_b + 2):
                y = n*b + v*c
                val = x**2 + y**2 + c**2
                if val <= radius_sq:
                    points.append((x, y, c, val))
    return points

def test_n(n):
    # Find u, v such that u^2 + v^2 + 1 = 0 mod n
    found = False
    for u in range(n):
        for v in range(n):
            if (u**2 + v**2 + 1) % n == 0:
                points = find_lattice_points(n, u, v, 2*n)
                nonzero = [p for p in points if p[0]**2 + p[1]**2 + p[2]**2 > 0]
                if nonzero:
                    # Sort by sum of squares
                    nonzero.sort(key=lambda x: x[3])
                    best = nonzero[0]
                    print(f"n={n}, u={u}, v={v}, best_point={best[:3]}, sum_sq={best[3]}")
                    if best[3] == n:
                        print("  SUCCESS: found sum of 3 squares!")
                    else:
                        print(f"  FAILED: found {best[3]} instead of {n}")
                found = True
                break
        if found: break
    if not found:
        print(f"n={n}: No u, v found")

for n in [1019, 10007, 10009]:
    test_n(n)

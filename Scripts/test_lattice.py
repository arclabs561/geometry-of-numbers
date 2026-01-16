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
    best_k = float('inf')
    for u in range(n):
        for v in range(n):
            if (u**2 + v**2 + 1) % n == 0:
                # Radius squared up to 4n or something
                points = find_lattice_points(n, u, v, 10*n)
                nonzero = [p for p in points if p[0]**2 + p[1]**2 + p[2]**2 > 0]
                if nonzero:
                    nonzero.sort(key=lambda x: x[3])
                    best = nonzero[0]
                    k = best[3] / n
                    if k < best_k:
                        best_k = k
                        best_point = best[:3]
                        best_u, best_v = u, v
                found = True
                # Keep searching for better u, v?
        if found: 
            print(f"n={n:4}, u={best_u:4}, v={best_v:4}, k={best_k:6.2f}, best_point={best_point}")
            if best_k == 1.0:
                print("  SUCCESS: found sum of 3 squares!")
            elif int(best_k) == best_k:
                print(f"  FOUND: representation of {int(best_k)}n")
            else:
                print(f"  STRANGE: k={best_k}")
            break
    if not found:
        print(f"n={n}: No u, v found")

for n in [3, 5, 7, 11, 13, 15, 19]:
    test_n(n)

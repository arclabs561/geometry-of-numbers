import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

def find_q(n):
    # q = 1 mod 4, q = -1/2 mod n
    target_rem = (-1 * pow(2, -1, n)) % n
    for k in range(1000):
        q = target_rem + k * n
        if q % 4 == 1 and is_prime(q):
            return q
    return None

def test_ankeny(n):
    print(f"Testing Ankeny for n={n}...")
    q = find_q(n)
    if q is None:
        print("  No q found")
        return
    print(f"  Found q={q}")
    
    # Find b such that b^2 = -n mod 4q
    b = -1
    for x in range(4*q):
        if (x**2 + n) % (4*q) == 0:
            b = x
            break
    if b == -1:
        print("  No b found")
        return
    print(f"  Found b={b}")
    
    # Search for (x, y, z) in L with Q = 2nq
    target_Q = 2 * n * q
    print(f"  Target Q={target_Q}")
    
    # L = { (x,y,z) : x = y mod n, y = bz mod 2q }
    # Limit for z: nz^2 < 2nq => z^2 < 2q
    limit_z = int(math.sqrt(target_Q / n)) + 1
    for z in range(-limit_z, limit_z + 1):
        # y = bz + 2q*k2
        # y^2 < 2nq => |y| < sqrt(2nq)
        limit_y = int(math.sqrt(target_Q)) + 1
        # y = bz mod 2q
        y_start = (b * z) % (2 * q)
        if y_start > q: y_start -= 2 * q
        for y in range(y_start - 2*q, y_start + 2*q + 1, 2*q):
            if abs(y) > limit_y: continue
            # x = y mod n
            x_start = y % n
            if x_start > n//2: x_start -= n
            limit_x = int(math.sqrt(target_Q / (2*q))) + 1
            for x in range(x_start - n, x_start + n + 1, n):
                if abs(x) > limit_x: continue
                if x == 0 and y == 0 and z == 0: continue
                Q = 2*q*x**2 + y**2 + n*z**2
                if Q == target_Q:
                    print(f"  Found point: x={x}, y={y}, z={z}")
                    # Reduction
                    # n - x^2 = (y^2 + n z^2) / (2q)
                    val = n - x**2
                    print(f"  n - x^2 = {n} - {x**2} = {val}")
                    # Is val sum of two squares?
                    for s in range(int(math.sqrt(val)) + 1):
                        t2 = val - s**2
                        t = int(math.sqrt(t2))
                        if t**2 == t2:
                            print(f"  SUCCESS: {n} = {x}^2 + {s}^2 + {t}^2")
                            return
    print("  FAILED to find point")

for n in [3, 11, 19, 35, 43, 51]:
    test_ankeny(n)

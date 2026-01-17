
import math

def is_sum_two_squares(k):
    """Checks if k is a sum of two squares using prime factorization."""
    if k < 0: return False
    d = 2
    temp = k
    while d * d <= temp:
        if temp % d == 0:
            count = 0
            while temp % d == 0:
                count += 1
                temp //= d
            if d % 4 == 3 and count % 2 != 0:
                return False
        d += 1
    if temp > 1:
        if temp % 4 == 3:
            return False
    return True

def solve_ankeny(n):
    """
    Finds (x, y, z, q) satisfying Ankeny conditions:
    n % 8 == 3
    q % 4 == 1 (prime)
    2q = -1 mod n  => 2q = k*n - 1
    2q*x^2 + y^2 + n*z^2 = 2nq
    x,y,z != 0
    Returns True if n - x^2 is a sum of two squares.
    """
    if n % 8 != 3: return None
    
    # Find q
    # 2q = -1 (mod n) -> 2q = k*n - 1
    # We need q to be prime and q % 4 == 1
    # Try k = 1, 3, ... (since 2q is even, k*n must be odd => k odd, n odd)
    # n is odd (3 mod 8).
    
    found_q = False
    q = 0
    for k in range(1, 1000, 2):
        val = k * n - 1
        if val % 2 == 0:
            cand_q = val // 2
            if cand_q % 4 == 1 and cand_q > n: # Ankeny usually requires q > n for ellipsoid size
                # check prime
                is_prime = True
                for i in range(2, int(cand_q**0.5) + 2):
                    if cand_q % i == 0:
                        is_prime = False
                        break
                if is_prime:
                    q = cand_q
                    found_q = True
                    break
    
    if not found_q:
        print(f"No suitable q found for n={n}")
        return None

    # Search for x, y, z in the ellipsoid
    # 2q x^2 + y^2 + n z^2 = 2nq
    # Bounds:
    # 2q x^2 < 2nq => x^2 < n => |x| < sqrt(n)
    # y^2 < 2nq => |y| < sqrt(2nq)
    # n z^2 < 2nq => z^2 < 2q => |z| < sqrt(2q)
    
    limit_x = int(n**0.5) + 1
    # We only need one solution.
    # Ankeny guarantees a solution exists via Minkowski.
    # We search small integers.
    
    for x in range(0, limit_x + 1): # x can be 0? Lemma says (x,y,z) != 0. 
        # But for n-x^2 to be sum of 2 sq, we usually want x > 0 or n itself sum of 2 sq (impossible for n=3 mod 8)
        # So x must be > 0.
        if x == 0: continue 
        
        rem1 = 2*n*q - 2*q*x*x
        if rem1 < 0: continue
        
        # We need y^2 + n*z^2 = rem1
        # Iterate z
        limit_z = int((rem1/n)**0.5) + 1
        for z in range(limit_z + 1):
            rem2 = rem1 - n*z*z
            if rem2 < 0: continue
            y = int(rem2**0.5)
            if y*y == rem2:
                # Found solution!
                # Check reduction
                target = n - x*x
                is_rep = is_sum_two_squares(target)
                print(f"n={n}, q={q}: Found ({x},{y},{z}) -> 2*{q}*{x}^2 + {y}^2 + {n}*{z}^2 = {2*n*q}")
                print(f"  Check: {n} - {x}^2 = {target}. Sum of 2 squares? {is_rep}")
                return is_rep

    print(f"n={n}, q={q}: No solution found in search limits (unexpected).")
    return False

# Test for n = 3, 11, 19, ...
print("Checking Ankeny reduction hypothesis...")
failures = 0
for n in [3, 11, 19, 27, 35, 43, 51, 59, 67, 83]:
    if n % 8 == 3:
        if solve_ankeny(n) == False:
            failures += 1

if failures == 0:
    print("SUCCESS: Hypothesis holds for all tested cases.")
else:
    print(f"FAILURE: Hypothesis failed for {failures} cases.")

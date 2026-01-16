def polygonal(s, n):
    return n + (s - 2) * n * (n - 1) // 2

def can_represent(n, s, num_terms, current_sum=0, start_k=0, memo=None):
    if memo is None: memo = {}
    state = (n - current_sum, num_terms)
    if state in memo: return memo[state]
    
    if current_sum == n: return True
    if num_terms == 0: return False
    
    # Try k such that P(s, k) <= n - current_sum
    k = start_k
    while True:
        p = polygonal(s, k)
        if p > n - current_sum: break
        if can_represent(n, s, num_terms - 1, current_sum + p, k, memo):
            memo[state] = True
            return True
        k += 1
    
    memo[state] = False
    return False

def check_s(s, limit):
    print(f"Checking s={s} up to {limit}...")
    fails = []
    for n in range(limit):
        if not can_represent(n, s, s):
            fails.append(n)
    if not fails:
        print(f"  SUCCESS: All n < {limit} are representable by {s} {s}-gonal numbers.")
    else:
        print(f"  FAILED: {len(fails)} numbers not representable: {fails[:10]}...")

def max_terms_needed(s, limit):
    needed = [0] * limit
    for n in range(1, limit):
        res = n # Worst case: all 1s
        k = 2
        while True:
            p = polygonal(s, k)
            if p > n: break
            res = min(res, 1 + needed[n - p])
            k += 1
        needed[n] = res
    return max(needed)

for s in [3, 4, 5, 6, 10, 20, 50]:
    m = s - 2
    limit = 108 * m
    mx = max_terms_needed(s, limit)
    print(f"s={s}, limit={limit}, max_terms={mx}")

def check_sum_three_squares_mod8():
    squares = [ (i**2)%8 for i in range(8) ]
    # squares = [0, 1, 4, 1, 0, 1, 4, 1]
    # Unique values: {0, 1, 4}
    valid = []
    for x in range(8):
        for y in range(8):
            for z in range(8):
                if (x**2 + y**2 + z**2) % 8 == 3:
                    valid.append((x, y, z))
    
    for x, y, z in valid:
        if x%2 == 0 or y%2 == 0 or z%2 == 0:
            print(f"FAILED: {x},{y},{z} is not all odd")
            return
    print("SUCCESS: All combinations summing to 3 mod 8 are odd")

check_sum_three_squares_mod8()

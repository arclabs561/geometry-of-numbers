import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

#check Nat.pow_mod

-- padic valuation / `padicValNat` spelunking
#check padicValNat
#check padicValNat_def
#check padicValNat_def'
#check padicValNat.zero
#check padicValNat.one
#check padicValNat.eq_zero_iff
#check padicValNat.mul
#check padicValNat.pow
#check padicValNat.eq_zero_of_not_dvd
#check padicValNat_self
#check Nat.pow_dvd_pow_iff
#check Nat.dvd_of_mem_primeFactors
#check Nat.prime_of_mem_primeFactors

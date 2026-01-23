import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

-- Silent API probes (avoid `#check` noise during builds).
private def _probe_pow_mod := @Nat.pow_mod

-- padic valuation / `padicValNat` spelunking
private def _probe_padicValNat := @padicValNat
private def _probe_padicValNat_def := @padicValNat_def
private def _probe_padicValNat_def' := @padicValNat_def'
private def _probe_padicValNat_zero := @padicValNat.zero
private def _probe_padicValNat_one := @padicValNat.one
private def _probe_padicValNat_eq_zero_iff := @padicValNat.eq_zero_iff
private def _probe_padicValNat_mul := @padicValNat.mul
private def _probe_padicValNat_pow := @padicValNat.pow
private def _probe_padicValNat_eq_zero_of_not_dvd := @padicValNat.eq_zero_of_not_dvd
private def _probe_padicValNat_self := @padicValNat_self
private def _probe_pow_dvd_pow_iff := @Nat.pow_dvd_pow_iff
private def _probe_dvd_of_mem_primeFactors := @Nat.dvd_of_mem_primeFactors
private def _probe_prime_of_mem_primeFactors := @Nat.prime_of_mem_primeFactors

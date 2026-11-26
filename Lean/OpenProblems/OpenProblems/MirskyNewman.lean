import OpenProblems.Prelude
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Nat.ModEq

/-!
# The Mirsky–Newman theorem (Davenport–Mirsky–Newman–Radó)

Listed as not yet formalized in Mathlib's `docs/1000.yaml` ("Mirsky–Newman theorem").

A finite system of residue classes `a_i (mod n_i)` with **distinct** moduli `n_i > 1` can never
cover every natural number exactly once.

Proof (Newman's generating-function argument, made purely algebraic): with `L = ∏ n_i` and
`ζ` a primitive `N`-th root of unity for the largest modulus `N`, evaluate
`∑_{m < L} ζ^m = ∑_i ∑_{m < L, m ≡ a_i (n_i)} ζ^m`. The left side and every term with `n_i < N`
vanish (geometric sums), while the term with `n_i = N` equals `ζ^{a} · L/N ≠ 0`.
-/

namespace OpenProblems.MirskyNewman

open Finset

theorem sum_range_mul (q n : ℕ) (f : ℕ → ℂ) :
    ∑ m ∈ range (q * n), f m = ∑ j ∈ range q, ∑ s ∈ range n, f (j * n + s) := by
  induction q with
  | zero => simp
  | succ q ih => rw [add_mul, one_mul, sum_range_add, ih, sum_range_succ]

theorem sum_residue (q n r : ℕ) (hr : r < n) (ζ : ℂ) :
    ∑ m ∈ range (q * n), (if m % n = r then ζ ^ m else 0) =
      ζ ^ r * ∑ j ∈ range q, (ζ ^ n) ^ j := by
  rw [sum_range_mul, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_eq_single r]
  · rw [if_pos (by rw [Nat.mul_add_mod_of_lt hr])]
    rw [← pow_mul, ← pow_add]; ring_nf
  · intro s hs hsr
    rw [if_neg]
    rw [Nat.mul_add_mod_of_lt (mem_range.1 hs)]; exact hsr
  · intro h; exact absurd (mem_range.2 hr) h

/-- **Mirsky–Newman.** No exact covering system with pairwise distinct moduli `> 1`. -/
theorem mirsky_newman {k : ℕ} (a n : Fin k → ℕ) (hn : ∀ i, 1 < n i)
    (hinj : Function.Injective n) (hcover : ∀ m : ℕ, ∃! i, m ≡ a i [MOD n i]) : False := by
  obtain ⟨i₀, -⟩ := hcover 0
  obtain ⟨i₀, -, hmax⟩ := exists_max_image (univ : Finset (Fin k)) n ⟨i₀, mem_univ _⟩
  set N := n i₀ with hN
  have hN1 : 1 < N := hn i₀
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N (by omega)
  set L := ∏ i, n i with hL
  have hdvd : ∀ i, n i ∣ L := fun i => dvd_prod_of_mem _ (mem_univ i)
  have hL0 : 0 < L := prod_pos fun i _ => by have := hn i; omega
  have hζL : ζ ^ L = 1 := (hζ.pow_eq_one_iff_dvd L).2 (hdvd i₀)
  have hζ1 : ζ ≠ 1 := hζ.ne_one hN1
  -- the geometric sums
  have geom0 : ∀ x : ℂ, x ≠ 1 → ∀ q, x ^ q = 1 → ∑ j ∈ range q, x ^ j = 0 := by
    intro x hx q hq
    rw [geom_sum_eq hx, hq, sub_self, zero_div]
  have hcols : ∀ i, ∑ m ∈ range L, (if m % n i = a i % n i then ζ ^ m else 0) =
      ζ ^ (a i % n i) * ∑ j ∈ range (L / n i), (ζ ^ n i) ^ j := by
    intro i
    have := sum_residue (L / n i) (n i) (a i % n i) (Nat.mod_lt _ (by have := hn i; omega)) ζ
    rwa [Nat.div_mul_cancel (hdvd i)] at this
  have hother : ∀ i, i ≠ i₀ → ∑ m ∈ range L, (if m % n i = a i % n i then ζ ^ m else 0) = 0 := by
    intro i hi
    rw [hcols i]
    have hlt : n i < N := lt_of_le_of_ne (hmax i (mem_univ _)) (fun h => hi (hinj h))
    have hne : ζ ^ n i ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by have := hn i; omega) hlt
    rw [geom0 _ hne _ (by rw [← pow_mul, Nat.mul_div_cancel' (hdvd i), hζL]), mul_zero]
  have hmain : ∑ m ∈ range L, (if m % n i₀ = a i₀ % n i₀ then ζ ^ m else 0) =
      ζ ^ (a i₀ % N) * (L / N : ℕ) := by
    rw [hcols i₀, ← hN, hζ.pow_eq_one]; simp
  -- regroup the full geometric sum by residue classes
  have htot : ∑ m ∈ range L, ζ ^ m =
      ∑ i, ∑ m ∈ range L, (if m % n i = a i % n i then ζ ^ m else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    obtain ⟨i, hi, huniq⟩ := hcover m
    rw [sum_eq_single i]
    · rw [if_pos (show m % n i = a i % n i from hi)]
    · intro j _ hj; rw [if_neg]; exact fun h => hj (huniq j h)
    · intro h; exact absurd (mem_univ i) h
  rw [geom0 ζ hζ1 L hζL, sum_eq_single i₀ (fun i _ hi => hother i hi) (by simp), hmain] at htot
  have hpos : (0 : ℂ) ≠ ((L / N : ℕ) : ℂ) := by
    have : 0 < L / N := Nat.div_pos (Nat.le_of_dvd hL0 (hdvd i₀)) (by omega)
    exact_mod_cast this.ne
  have hζ0 : ζ ^ (a i₀ % N) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
  exact (mul_ne_zero hζ0 hpos.symm) htot.symm

end OpenProblems.MirskyNewman

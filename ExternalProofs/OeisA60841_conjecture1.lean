/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# OEIS A060841, `conjecture1`: a complete proof

Statement (Robert G. Wilson v, 2015): for the $n \times n$ matrix $M$ with
$M[i,j] = 1/\operatorname{lcm}(i,j)$, the number $1/\det(M)$ is an integer exactly for
$n \in \{1, \dots, 34\} \cup \{36, 38\}$.

The definitions `lcmMatrix` and `integerDetN` and the statement of `conjecture1` are copied
verbatim from `FormalConjectures/OEIS/60841.lean`.

Proof outline.
* Closed form $1/\det(M) = (n!)^2 / \prod_{k \le n} \varphi(k)$ (Smith's determinant). The
  lemmas `a608E` to `a608_det` are taken from the proof of `conjecture2` in
  https://github.com/anatoliiohorodnyk/lean-fc-proofs (Apache-2.0).
* For $n \ge 103$ the $2$-adic valuation of $\prod \varphi(k)$ exceeds that of $(n!)^2$.
  This uses $v_2(\varphi(k)) \ge v_2(k) - [2 \mid k] + \sum_{q \mid k} v_2(q-1)$ over the
  odd primes $q \le 47$.
* The cases $n < 103$ are decided by kernel computation (`decide`, no `native_decide`).

Check: `lake env lean ExternalProofs/OeisA60841_conjecture1.lean` in a checkout of
formal-conjectures; the final `#print axioms` shows `[propext, Classical.choice, Quot.sound]`.
-/

open Finset Nat

namespace OeisA60841

def lcmMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j : Fin n ↦ 1 / ((Nat.lcm (i.val + 1) (j.val + 1) : ℚ))

def integerDetN : Set ℕ :=
  Set.Icc 1 34 ∪ {36, 38}

open Finset in
/-- Divisor-incidence matrix. -/
def a608E (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i k : Fin n => if (k.val + 1) ∣ (i.val + 1) then 1 else 0

open Finset in
lemma a608_E_det (n : ℕ) : (a608E n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [a608E]
  · intro i k hik
    simp only [a608E, Matrix.of_apply]
    rw [if_neg]
    intro hdvd
    have := Nat.le_of_dvd (Nat.succ_pos _) hdvd
    have hik' : i < k := hik
    have : i.val < k.val := hik'
    omega

open Finset in
lemma a608_sum_dvd (n a b : ℕ) (ha : 1 ≤ a) (han : a ≤ n) (hb : 1 ≤ b) :
    ∑ k : Fin n, (if (k.val + 1) ∣ a ∧ (k.val + 1) ∣ b then (Nat.totient (k.val + 1) : ℚ) else 0)
      = Nat.gcd a b := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if (k + 1) ∣ a ∧ (k + 1) ∣ b then
    (Nat.totient (k + 1) : ℚ) else 0) n, ← Finset.sum_filter]
  have hg : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  have : ((range n).filter fun k => (k + 1) ∣ a ∧ (k + 1) ∣ b).map (addRightEmbedding 1)
      = (Nat.gcd a b).divisors := by
    ext d
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_range, addRightEmbedding_apply,
      Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨k, ⟨hk, h1, h2⟩, rfl⟩
      exact ⟨⟨h1, h2⟩, hg⟩
    · rintro ⟨⟨h1, h2⟩, -⟩
      have hd : 1 ≤ d := Nat.pos_of_dvd_of_pos h1 (by omega)
      refine ⟨d - 1, ⟨?_, ?_, ?_⟩, by omega⟩
      · have := Nat.le_of_dvd (by omega) h1; omega
      · rwa [Nat.sub_add_cancel hd]
      · rwa [Nat.sub_add_cancel hd]
  have hsum := congrArg (fun s => ∑ d ∈ s, (Nat.totient d : ℚ)) this
  simp only [Finset.sum_map, addRightEmbedding_apply] at hsum
  rw [hsum]
  exact_mod_cast Nat.sum_totient (Nat.gcd a b)

open Finset in
lemma a608_G (n : ℕ) (i j : Fin n) :
    (a608E n * Matrix.diagonal (fun k : Fin n => (Nat.totient (k.val + 1) : ℚ)) * (a608E n).transpose) i j
      = Nat.gcd (i.val + 1) (j.val + 1) := by
  rw [← a608_sum_dvd n (i.val + 1) (j.val + 1) (by omega) i.isLt (by omega), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [a608E, Matrix.of_apply]
  split_ifs <;> simp_all

open Finset in
lemma a608_factor (n : ℕ) :
    lcmMatrix n = Matrix.diagonal (fun i : Fin n => 1 / ((i.val + 1 : ℕ) : ℚ)) *
      (a608E n * Matrix.diagonal (fun k : Fin n => (Nat.totient (k.val + 1) : ℚ)) * (a608E n).transpose) *
      Matrix.diagonal (fun j : Fin n => 1 / ((j.val + 1 : ℕ) : ℚ)) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, a608_G]
  simp only [lcmMatrix, Matrix.of_apply]
  have hl := Nat.gcd_mul_lcm (i.val + 1) (j.val + 1)
  have hl' : ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℚ) * (Nat.lcm (i.val + 1) (j.val + 1) : ℕ)
      = ((i.val + 1 : ℕ) : ℚ) * ((j.val + 1 : ℕ) : ℚ) := by exact_mod_cast hl
  have hlcm : ((Nat.lcm (i.val + 1) (j.val + 1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.lcm_ne_zero (by omega) (by omega)
  have hi : ((i.val + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : i.val + 1 ≠ 0)
  have hj : ((j.val + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : j.val + 1 ≠ 0)
  have hg : ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.gcd_ne_zero_left (by omega)
  field_simp
  linear_combination (-1 : ℚ) * hl'

open Finset in
lemma a608_det (n : ℕ) : (lcmMatrix n).det =
    ∏ i : Fin n, ((Nat.totient (i.val + 1) : ℚ) / ((i.val + 1 : ℕ) : ℚ) ^ 2) := by
  rw [a608_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, a608_E_det, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [one_mul, mul_one]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-! ### New material: proof of `conjecture1` -/

instance fact_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma inv_det_eq (n : ℕ) : ((lcmMatrix n).det)⁻¹ =
    ((n ! ^ 2 : ℕ) : ℚ) / ((∏ i ∈ range n, φ (i + 1) : ℕ) : ℚ) := by
  have hq : ((lcmMatrix n).det)⁻¹ =
      ∏ i ∈ Finset.range n, (((i + 1 : ℕ) : ℚ) ^ 2 / (Nat.totient (i + 1) : ℚ)) := by
    simp only [a608_det, ← Finset.prod_inv_distrib, inv_div]
    exact Fin.prod_univ_eq_prod_range (fun i => (((i + 1 : ℕ) : ℚ) ^ 2 / (Nat.totient (i + 1) : ℚ))) n
  rw [hq, Finset.prod_div_distrib, Finset.prod_pow, ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  rfl

lemma den_one_iff (a b : ℕ) (hb : b ≠ 0) : ((a : ℚ) / (b : ℚ)).den = 1 ↔ b ∣ a := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  constructor
  · intro h
    rw [Rat.den_eq_one_iff] at h
    have h2 : (a : ℚ) = (((a : ℚ) / b).num : ℚ) * b := by rw [h]; field_simp
    have h3 : (a : ℤ) = ((a : ℚ) / b).num * b := by exact_mod_cast h2
    have h4 : (b : ℤ) ∣ (a : ℤ) := ⟨_, by rw [h3]; ring⟩
    exact_mod_cast h4
  · rintro ⟨c, rfl⟩
    have h1 : ((b * c : ℕ) : ℚ) / (b : ℚ) = (c : ℚ) := by push_cast; field_simp
    rw [h1]; exact Rat.den_natCast c

lemma v2_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat 2 (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat 2 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hfs : (∏ i ∈ s, f i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [padicValNat.mul hfa hfs, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

lemma key (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (k : ℕ) (hk : 0 < k) :
    padicValNat 2 k + ∑ q ∈ S, (if q ∣ k then padicValNat 2 (q - 1) else 0)
      ≤ padicValNat 2 (φ k) + (if 2 ∣ k then 1 else 0) := by
  have hrad_dvd := Nat.prod_primeFactors_dvd k
  have hr0 : (∏ p ∈ k.primeFactors, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hdiv0 : k / (∏ p ∈ k.primeFactors, p) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hk hrad_dvd) (Nat.pos_of_ne_zero hr0)).ne'
  have hpm : ∀ p ∈ k.primeFactors, p - 1 ≠ 0 := fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  have hprod0 : ∏ p ∈ k.primeFactors, (p - 1) ≠ 0 := Finset.prod_ne_zero_iff.mpr hpm
  have hvr : padicValNat 2 (∏ p ∈ k.primeFactors, p) = if 2 ∣ k then 1 else 0 := by
    rw [v2_prod _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    have h1 : ∀ p ∈ k.primeFactors, padicValNat 2 p = if p = 2 then 1 else 0 := by
      intro p hp
      split_ifs with h
      · subst h; exact padicValNat_self
      · haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
        exact padicValNat_primes (Ne.symm h)
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq']
    simp [Nat.mem_primeFactors, hk.ne', Nat.prime_two]
  have hle : padicValNat 2 (∏ p ∈ k.primeFactors, p) ≤ padicValNat 2 k :=
    (padicValNat_dvd_iff_le hk.ne').mp (dvd_trans pow_padicValNat_dvd hrad_dvd)
  have hsum : ∑ q ∈ S, (if q ∣ k then padicValNat 2 (q - 1) else 0)
      ≤ ∑ p ∈ k.primeFactors, padicValNat 2 (p - 1) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset
    intro q hq
    rw [Finset.mem_filter] at hq
    exact Nat.mem_primeFactors.mpr ⟨hS q hq.1, hq.2, hk.ne'⟩
  rw [Nat.totient_eq_div_primeFactors_mul k, padicValNat.mul hdiv0 hprod0,
    padicValNat.div_of_dvd hrad_dvd, v2_prod _ _ hpm]
  rw [hvr] at hle ⊢
  generalize (if 2 ∣ k then 1 else 0) = t at hle ⊢
  omega

lemma sum_bound (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (n : ℕ) :
    padicValNat 2 (n !) + ∑ q ∈ S, padicValNat 2 (q - 1) * (n / q)
      ≤ padicValNat 2 (∏ i ∈ range n, φ (i + 1)) + n / 2 := by
  have h1 : padicValNat 2 (n !) = ∑ i ∈ range n, padicValNat 2 (i + 1) := by
    rw [← Finset.prod_range_add_one_eq_factorial, v2_prod _ _ (fun i _ => Nat.succ_ne_zero i)]
  have h2 : padicValNat 2 (∏ i ∈ range n, φ (i + 1)) = ∑ i ∈ range n, padicValNat 2 (φ (i + 1)) :=
    v2_prod _ _ (fun i _ => (Nat.totient_pos.mpr (Nat.succ_pos i)).ne')
  have h3 : n / 2 = ∑ i ∈ range n, (if 2 ∣ i + 1 then 1 else 0) := by
    rw [← Nat.card_multiples n 2, Finset.card_filter]
  have h4 : ∑ q ∈ S, padicValNat 2 (q - 1) * (n / q)
      = ∑ i ∈ range n, ∑ q ∈ S, (if q ∣ i + 1 then padicValNat 2 (q - 1) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Nat.card_multiples n q, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [h1, h2, h3, h4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => key S hS (i + 1) (Nat.succ_pos i)

def S14 : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47}

def c14 (q : ℕ) : ℕ :=
  if q = 5 ∨ q = 13 ∨ q = 29 ∨ q = 37 then 2 else if q = 17 then 4 else if q = 41 then 3 else 1

lemma S14_prime : ∀ q ∈ S14, q.Prime := by
  intro q hq
  simp only [S14, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma c14_le : ∀ q ∈ S14, c14 q ≤ padicValNat 2 (q - 1) := by
  intro q hq
  simp only [S14, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num [c14])

lemma e14 (f : ℕ → ℕ) : ∑ q ∈ S14, f q =
    f 3 + (f 5 + (f 7 + (f 11 + (f 13 + (f 17 + (f 19 + (f 23 + (f 29 + (f 31 + (f 37 + (f 41 + (f 43 + f 47)))))))))))) := by
  unfold S14
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]

lemma ee (n : ℕ) : ∑ q ∈ S14, c14 q * (n / q) =
      n / 3 + 2 * (n / 5) + n / 7 + n / 11 + 2 * (n / 13) + 4 * (n / 17) + n / 19 + n / 23
      + 2 * (n / 29) + n / 31 + 2 * (n / 37) + 3 * (n / 41) + n / 43 + n / 47 := by
  rw [e14]
  have h3 : c14 3 = 1 := by decide
  have h5 : c14 5 = 2 := by decide
  have h7 : c14 7 = 1 := by decide
  have h11 : c14 11 = 1 := by decide
  have h13 : c14 13 = 2 := by decide
  have h17 : c14 17 = 4 := by decide
  have h19 : c14 19 = 1 := by decide
  have h23 : c14 23 = 1 := by decide
  have h29 : c14 29 = 2 := by decide
  have h31 : c14 31 = 1 := by decide
  have h37 : c14 37 = 2 := by decide
  have h41 : c14 41 = 3 := by decide
  have h43 : c14 43 = 1 := by decide
  have h47 : c14 47 = 1 := by decide
  rw [h3, h5, h7, h11, h13, h17, h19, h23, h29, h31, h37, h41, h43, h47]
  simp only [one_mul]
  ac_rfl

lemma weights (n : ℕ) :
    n / 3 + 2 * (n / 5) + n / 7 + n / 11 + 2 * (n / 13) + 4 * (n / 17) + n / 19 + n / 23
      + 2 * (n / 29) + n / 31 + 2 * (n / 37) + 3 * (n / 41) + n / 43 + n / 47
      ≤ ∑ q ∈ S14, padicValNat 2 (q - 1) * (n / q) := by
  have h : ∑ q ∈ S14, c14 q * (n / q) ≤ ∑ q ∈ S14, padicValNat 2 (q - 1) * (n / q) :=
    Finset.sum_le_sum fun q hq => Nat.mul_le_mul_right _ (c14_le q hq)
  rw [ee] at h
  exact h

lemma div_lb (n q : ℕ) (hq : 0 < q) : n + 1 ≤ q * (n / q) + q := by
  have h1 := Nat.div_add_mod n q
  have h2 := Nat.mod_lt n hq
  omega

lemma weights_big (n : ℕ) (hn : 103 ≤ n) :
    n + n / 2 < n / 3 + 2 * (n / 5) + n / 7 + n / 11 + 2 * (n / 13) + 4 * (n / 17) + n / 19
      + n / 23 + 2 * (n / 29) + n / 31 + 2 * (n / 37) + 3 * (n / 41) + n / 43 + n / 47 := by
  have h2 : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have h3 := div_lb n 3 (by norm_num)
  have h5 := div_lb n 5 (by norm_num)
  have h7 := div_lb n 7 (by norm_num)
  have h11 := div_lb n 11 (by norm_num)
  have h13 := div_lb n 13 (by norm_num)
  have h17 := div_lb n 17 (by norm_num)
  have h19 := div_lb n 19 (by norm_num)
  have h23 := div_lb n 23 (by norm_num)
  have h29 := div_lb n 29 (by norm_num)
  have h31 := div_lb n 31 (by norm_num)
  have h37 := div_lb n 37 (by norm_num)
  have h41 := div_lb n 41 (by norm_num)
  have h43 := div_lb n 43 (by norm_num)
  have h47 := div_lb n 47 (by norm_num)
  generalize n / 2 = d2 at *
  generalize n / 3 = d3 at *
  generalize n / 5 = d5 at *
  generalize n / 7 = d7 at *
  generalize n / 11 = d11 at *
  generalize n / 13 = d13 at *
  generalize n / 17 = d17 at *
  generalize n / 19 = d19 at *
  generalize n / 23 = d23 at *
  generalize n / 29 = d29 at *
  generalize n / 31 = d31 at *
  generalize n / 37 = d37 at *
  generalize n / 41 = d41 at *
  generalize n / 43 = d43 at *
  generalize n / 47 = d47 at *
  linarith

set_option maxRecDepth 100000 in
lemma small : ∀ n < 103, 1 ≤ n →
    ((∏ i ∈ range n, φ (i + 1)) ∣ (n ! ^ 2) ↔ (n ≤ 34 ∨ n = 36 ∨ n = 38)) := by
  decide

theorem conjecture1 :
    ∀ n : ℕ, 1 ≤ n → (((lcmMatrix n).det)⁻¹.den = 1 ↔ n ∈ integerDetN) := by
  intro n hn
  have hQ0 : (∏ i ∈ range n, φ (i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.totient_pos.mpr (Nat.succ_pos i)).ne'
  rw [inv_det_eq, den_one_iff _ _ hQ0]
  have hmem : n ∈ integerDetN ↔ (n ≤ 34 ∨ n = 36 ∨ n = 38) := by
    simp only [integerDetN, Set.mem_union, Set.mem_Icc, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    omega
  rw [hmem]
  by_cases h : n < 103
  · exact small n h hn
  · constructor
    · intro hdvd
      exfalso
      have hv : padicValNat 2 (∏ i ∈ range n, φ (i + 1)) ≤ padicValNat 2 (n ! ^ 2) :=
        (padicValNat_dvd_iff_le (pow_ne_zero 2 (Nat.factorial_ne_zero n))).mp
          (dvd_trans pow_padicValNat_dvd hdvd)
      rw [padicValNat.pow] at hv
      have h103 : 103 ≤ n := by omega
      have hV : padicValNat 2 (n !) ≤ n := by
        have := sub_one_mul_padicValNat_factorial (p := 2) n
        simp at this
        omega
      have hbig := weights_big n h103
      have hw := weights n
      have hb := sum_bound S14 S14_prime n
      generalize (∑ q ∈ S14, padicValNat 2 (q - 1) * (n / q)) = W at hb hw
      generalize (n / 3 + 2 * (n / 5) + n / 7 + n / 11 + 2 * (n / 13) + 4 * (n / 17) + n / 19
        + n / 23 + 2 * (n / 29) + n / 31 + 2 * (n / 37) + 3 * (n / 41) + n / 43 + n / 47) = E
        at hw hbig
      generalize n / 2 = d2 at hb hbig
      omega
    · intro h'
      omega

end OeisA60841

#print axioms OeisA60841.conjecture1

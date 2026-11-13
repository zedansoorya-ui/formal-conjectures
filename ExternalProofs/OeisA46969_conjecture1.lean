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
# OEIS A046969, `conjecture1`: a complete proof

Statement (Lorenzo Sauras Altuzarra, 2020): if $p > 3$ and $2p - 1$ are both prime, then
$a(p)/12$ is prime, where $a(n)$ is the denominator of $B_{2n} / (2n(2n-1))$.

We prove $a(p) = 12(2p - 1)$. The definition `a` and the statement of `conjecture1` are copied
verbatim from `FormalConjectures/OEIS/46969.lean`.

Proof outline, with $q = 2p - 1$ and $B = B_{2p}$.
* von Staudt–Clausen (`Bernoulli.vonStaudt_clausen`): the only primes $s$ with $s - 1 \mid 2p$
  are $2$ and $3$, so $6B = Z$ is an integer with $Z \equiv 1 \pmod 6$.
* Faulhaber (`sum_range_pow`) plus von Staudt–Clausen for $B_i$, $i < 2p$: for $\ell \in \{p, q\}$,
  $\sum_{k<\ell} k^{2p} \equiv \ell B \pmod{\ell^2}$ in the $\ell$-integral sense (`faulhaber_pdiv`).
* A Voronoi-type identity with multiplier $2$ (`voronoi_two`) gives $p^2 \mid \sum_{k<p} k^{2p}$
  (`partA`, a special case of Adams' theorem) and $q^2 \nmid \sum_{k<q} k^{2p}$ (`partB`, a special
  case of Kummer's congruence).
* Hence $p \mid Z$ and $q \nmid Z$, so $B / (2pq) = M / (12q)$ with $\gcd(M, 12q) = 1$.

Check: `lake env lean ExternalProofs/OeisA46969_conjecture1.lean` in a checkout of
formal-conjectures; the final `#print axioms` shows `[propext, Classical.choice, Quot.sound]`.
-/

open Finset Nat

namespace OeisA46969Proof

/-- `PDiv ℓ e x`: the rational `x` is `ℓ^e` times an `ℓ`-integral rational. -/
def PDiv (ℓ e : ℕ) (x : ℚ) : Prop := ∃ u v : ℤ, ¬ (ℓ : ℤ) ∣ v ∧ x * v = (ℓ : ℚ) ^ e * u

section PDiv
variable {ℓ : ℕ} (hℓ : ℓ.Prime)
include hℓ

lemma not_dvd_mul {v w : ℤ} (hv : ¬ (ℓ : ℤ) ∣ v) (hw : ¬ (ℓ : ℤ) ∣ w) : ¬ (ℓ : ℤ) ∣ v * w := by
  intro h
  rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_or_dvd h with h | h <;> contradiction

lemma PDiv.add {e : ℕ} {x y : ℚ} (hx : PDiv ℓ e x) (hy : PDiv ℓ e y) : PDiv ℓ e (x + y) := by
  obtain ⟨u₁, v₁, h₁, e₁⟩ := hx
  obtain ⟨u₂, v₂, h₂, e₂⟩ := hy
  refine ⟨u₁ * v₂ + u₂ * v₁, v₁ * v₂, not_dvd_mul hℓ h₁ h₂, ?_⟩
  push_cast
  linear_combination (v₂ : ℚ) * e₁ + (v₁ : ℚ) * e₂

omit hℓ in
lemma PDiv.neg {e : ℕ} {x : ℚ} (hx : PDiv ℓ e x) : PDiv ℓ e (-x) := by
  obtain ⟨u, v, h, e₁⟩ := hx
  exact ⟨-u, v, h, by push_cast; linear_combination -e₁⟩

lemma PDiv.sub {e : ℕ} {x y : ℚ} (hx : PDiv ℓ e x) (hy : PDiv ℓ e y) : PDiv ℓ e (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hℓ hy.neg

lemma PDiv.zero (e : ℕ) : PDiv ℓ e 0 :=
  ⟨0, 1, fun h => hℓ.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by omega) h), by simp⟩

lemma PDiv.sum {ι : Type*} (s : Finset ι) (e : ℕ) (f : ι → ℚ) (hf : ∀ i ∈ s, PDiv ℓ e (f i)) :
    PDiv ℓ e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using PDiv.zero hℓ e
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add hℓ (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma PDiv.mul {e f : ℕ} {x y : ℚ} (hx : PDiv ℓ e x) (hy : PDiv ℓ f y) : PDiv ℓ (e + f) (x * y) := by
  obtain ⟨u₁, v₁, h₁, e₁⟩ := hx
  obtain ⟨u₂, v₂, h₂, e₂⟩ := hy
  refine ⟨u₁ * u₂, v₁ * v₂, not_dvd_mul hℓ h₁ h₂, ?_⟩
  push_cast
  rw [pow_add]
  linear_combination (y * v₂) * e₁ + ((ℓ : ℚ) ^ e * u₁) * e₂

lemma PDiv.ofInt (e : ℕ) (n : ℤ) : PDiv ℓ e ((ℓ : ℚ) ^ e * n) :=
  ⟨n, 1, fun h => hℓ.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by omega) h), by simp⟩

lemma PDiv.int (n : ℤ) : PDiv ℓ 0 (n : ℚ) := by simpa using PDiv.ofInt hℓ 0 n

omit hℓ in
lemma PDiv.inv (v : ℤ) (hv : ¬ (ℓ : ℤ) ∣ v) : PDiv ℓ 0 (1 / (v : ℚ)) := by
  have hv0 : (v : ℚ) ≠ 0 := by
    rintro h; exact hv (by rw [show v = 0 by exact_mod_cast h]; exact dvd_zero _)
  exact ⟨1, v, hv, by field_simp; simp⟩

/-- An integer that is `PDiv ℓ e` is divisible by `ℓ ^ e`. -/
lemma PDiv.int_dvd {e : ℕ} {n : ℤ} (h : PDiv ℓ e (n : ℚ)) : (ℓ : ℤ) ^ e ∣ n := by
  obtain ⟨u, v, hv, h₁⟩ := h
  have h₂ : n * v = (ℓ : ℤ) ^ e * u := by exact_mod_cast h₁
  have hcop : IsCoprime ((ℓ : ℤ) ^ e) v :=
    IsCoprime.pow_left ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).mpr hv)
  exact hcop.dvd_of_dvd_mul_right ⟨u, by rw [h₂]⟩

end PDiv

/-- Multiplying by `2` permutes the residues modulo an odd prime. -/
lemma sum_two_mul_mod {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (f : ℕ → ℤ) :
    ∑ k ∈ range ℓ, f ((2 * k) % ℓ) = ∑ k ∈ range ℓ, f k := by
  have hcop : ℓ.gcd 2 = 1 :=
    (Nat.coprime_primes hℓ Nat.prime_two).mpr hℓ2
  have hinj : Set.InjOn (fun k => (2 * k) % ℓ) (range ℓ : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h : 2 * a ≡ 2 * b [MOD ℓ] := hab
    have := Nat.ModEq.cancel_left_of_coprime hcop h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have himg : (range ℓ).image (fun k => (2 * k) % ℓ) = range ℓ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨k, -, rfl⟩ := hx
      exact Nat.mod_lt _ hℓ.pos
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image hinj, himg]

/-- Voronoi-type congruence with multiplier `2`. -/
lemma voronoi_two {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (m : ℕ) :
    (ℓ : ℤ) ^ 2 ∣ (2 ^ m - 1) * (∑ k ∈ range ℓ, (k : ℤ) ^ m)
      - m * ℓ * 2 ^ (m - 1) * ∑ k ∈ range ℓ, (k : ℤ) ^ (m - 1) * ((2 * k / ℓ : ℕ) : ℤ) := by
  have hperm := sum_two_mul_mod hℓ hℓ2 (fun j => (j : ℤ) ^ m)
  have hterm : ∀ k ∈ range ℓ, (ℓ : ℤ) ^ 2 ∣
      (((2 * k) % ℓ : ℕ) : ℤ) ^ m - (2 : ℤ) ^ m * (k : ℤ) ^ m
        + m * ℓ * 2 ^ (m - 1) * ((k : ℤ) ^ (m - 1) * ((2 * k / ℓ : ℕ) : ℤ)) := by
    intro k _
    have hmod : (((2 * k) % ℓ : ℕ) : ℤ) = 2 * k + (-(ℓ * ((2 * k / ℓ : ℕ) : ℤ))) := by
      have := Nat.mod_add_div (2 * k) ℓ
      have : (((2 * k) % ℓ : ℕ) : ℤ) + ℓ * ((2 * k / ℓ : ℕ) : ℤ) = 2 * k := by exact_mod_cast this
      linarith
    have key := sq_dvd_add_pow_sub_sub (-(ℓ * ((2 * k / ℓ : ℕ) : ℤ))) (2 * (k : ℤ)) m
    have hsq : (ℓ : ℤ) ^ 2 ∣ (-(ℓ * ((2 * k / ℓ : ℕ) : ℤ))) ^ 2 :=
      ⟨((2 * k / ℓ : ℕ) : ℤ) ^ 2, by ring⟩
    rw [hmod]
    have heq : (2 * (k : ℤ) + -(ℓ * ((2 * k / ℓ : ℕ) : ℤ))) ^ m - (2 : ℤ) ^ m * (k : ℤ) ^ m
        + m * ℓ * 2 ^ (m - 1) * ((k : ℤ) ^ (m - 1) * ((2 * k / ℓ : ℕ) : ℤ))
        = (2 * (k : ℤ) + -(ℓ * ((2 * k / ℓ : ℕ) : ℤ))) ^ m
          - (2 * (k : ℤ)) ^ (m - 1) * -(ℓ * ((2 * k / ℓ : ℕ) : ℤ)) * m - (2 * (k : ℤ)) ^ m := by
      ring
    rw [heq]
    exact dvd_trans hsq key
  have hsum := Finset.dvd_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hperm, ← Finset.mul_sum,
    ← Finset.mul_sum] at hsum
  have : (2 ^ m - 1) * (∑ k ∈ range ℓ, (k : ℤ) ^ m)
      - m * ℓ * 2 ^ (m - 1) * ∑ k ∈ range ℓ, (k : ℤ) ^ (m - 1) * ((2 * k / ℓ : ℕ) : ℤ)
      = -((∑ k ∈ range ℓ, (k : ℤ) ^ m - 2 ^ m * ∑ k ∈ range ℓ, (k : ℤ) ^ m)
        + m * ℓ * 2 ^ (m - 1) * ∑ k ∈ range ℓ, (k : ℤ) ^ (m - 1) * ((2 * k / ℓ : ℕ) : ℤ)) := by
    ring
  rw [this]
  exact (dvd_neg).mpr hsum


/-- `ℓ · B_i` is `ℓ`-integral for every `i` (von Staudt–Clausen). -/
lemma pdiv_mul_bernoulli {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (i : ℕ) :
    PDiv ℓ 0 ((ℓ : ℚ) * bernoulli i) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
  · obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    have hB : (ℓ : ℚ) * bernoulli (2 * k) = ((ℓ * z : ℤ) : ℚ)
        - ∑ s ∈ range (2 * k + 2) with Nat.Prime s ∧ s - 1 ∣ 2 * k, (ℓ : ℚ) * (1 / (s : ℚ)) := by
      rw [← Finset.mul_sum]; push_cast; rw [hz]; ring
    rw [hB]
    refine (PDiv.int hℓ _).sub hℓ (PDiv.sum hℓ _ 0 _ fun s hs => ?_)
    have hsp : s.Prime := (Finset.mem_filter.mp hs).2.1
    by_cases hsl : s = ℓ
    · subst hsl
      have : (s : ℚ) * (1 / (s : ℚ)) = ((1 : ℤ) : ℚ) := by
        have : (s : ℚ) ≠ 0 := by exact_mod_cast hsp.ne_zero
        field_simp; simp
      rw [this]; exact PDiv.int hℓ 1
    · have hnd : ¬ (ℓ : ℤ) ∣ (s : ℤ) := by
        intro h
        exact hsl ((Nat.prime_dvd_prime_iff_eq hℓ hsp).mp (Int.natCast_dvd_natCast.mp h)).symm
      have := (PDiv.int hℓ (ℓ : ℤ)).mul hℓ (PDiv.inv (s : ℤ) hnd)
      simpa using this
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hnd : ¬ (ℓ : ℤ) ∣ (2 : ℤ) := by
        intro h
        have : ℓ ∣ 2 := Int.natCast_dvd_natCast.mp (by exact_mod_cast h)
        exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this)
      have := (PDiv.int hℓ (-(ℓ : ℤ))).mul hℓ (PDiv.inv (2 : ℤ) hnd)
      have e : (ℓ : ℚ) * bernoulli (2 * 0 + 1) = ((-(ℓ : ℤ) : ℤ) : ℚ) * (1 / ((2 : ℤ) : ℚ)) := by
        simp [bernoulli_one]; ring
      rw [e]; exact this
    · rw [bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega), mul_zero]
      exact PDiv.zero hℓ 0

/-- Faulhaber: `∑_{k<ℓ} k^m ≡ ℓ B_m (mod ℓ²)` in the `ℓ`-integral sense. -/
lemma faulhaber_pdiv {ℓ m : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hm : 3 ≤ m) (hodd : Odd (m - 1))
    (hcop : ¬ (ℓ : ℤ) ∣ ((m + 1 : ℕ) : ℤ)) :
    PDiv ℓ 2 ((∑ k ∈ range ℓ, (k : ℚ) ^ m) - ℓ * bernoulli m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hn3 : ((n + 2 : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  rw [sum_range_pow, Finset.sum_range_succ, show range (n + 2) = range (n + 1 + 1) from rfl,
    Finset.sum_range_succ]
  have hodd' : Odd (n + 1) := by simpa using hodd
  rw [bernoulli_eq_zero_of_odd hodd' (by omega), Nat.choose_succ_self_right,
    show n + 2 + 1 - (n + 2) = 1 by omega]
  have htop : bernoulli (n + 2) * ((n + 2 + 1 : ℕ) : ℚ) * (ℓ : ℚ) ^ 1 / (((n + 2 : ℕ) : ℚ) + 1)
      = ℓ * bernoulli (n + 2) := by
    field_simp; push_cast; ring
  rw [htop, zero_mul, zero_mul, zero_div, add_zero, add_sub_cancel_right]
  refine PDiv.sum hℓ _ 2 _ fun i hi => ?_
  have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
  have hcop' : ¬ (ℓ : ℤ) ∣ (((n + 2 + 1 : ℕ) : ℤ)) := hcop
  have e : bernoulli i * (((n + 2 + 1).choose i : ℕ) : ℚ) * (ℓ : ℚ) ^ (n + 2 + 1 - i)
        / (((n + 2 : ℕ) : ℚ) + 1)
      = ((ℓ : ℚ) * bernoulli i) * ((ℓ : ℚ) ^ 2 * ((((n + 2 + 1).choose i : ℕ) * ℓ ^ (n - i) : ℕ) : ℤ))
        * (1 / ((((n + 2 + 1 : ℕ) : ℤ)) : ℚ)) := by
    rw [show n + 2 + 1 - i = (n - i) + 1 + 2 by omega]
    push_cast
    field_simp
    ring
  rw [e]
  exact ((pdiv_mul_bernoulli hℓ hℓ2 i).mul hℓ (PDiv.ofInt hℓ 2 _)).mul hℓ (PDiv.inv _ hcop')

/-- Adams-type step: `p² ∣ ∑_{k<p} k^{2p}` for a prime `p > 3`. -/
lemma partA {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    (p : ℤ) ^ 2 ∣ ∑ k ∈ range p, (k : ℤ) ^ (2 * p) := by
  have v := voronoi_two hp (by omega) (2 * p)
  have hB : (p : ℤ) ^ 2 ∣ ((2 * p : ℕ) : ℤ) * p * 2 ^ (2 * p - 1)
      * ∑ k ∈ range p, (k : ℤ) ^ (2 * p - 1) * ((2 * k / p : ℕ) : ℤ) :=
    ⟨2 * 2 ^ (2 * p - 1) * ∑ k ∈ range p, (k : ℤ) ^ (2 * p - 1) * ((2 * k / p : ℕ) : ℤ),
      by push_cast; ring⟩
  have hA : (p : ℤ) ^ 2 ∣ (2 ^ (2 * p) - 1) * ∑ k ∈ range p, (k : ℤ) ^ (2 * p) := by
    have := dvd_add v hB
    rwa [sub_add_cancel] at this
  have := Fact.mk hp
  have hnd : ¬ (p : ℤ) ∣ (2 ^ (2 * p) - 1 : ℤ) := by
    intro h
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    push_cast at h0
    rw [pow_mul', ZMod.pow_card] at h0
    have h3' : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h0
    have := (ZMod.natCast_eq_zero_iff 3 p).mp h3'
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hcop : IsCoprime ((p : ℤ) ^ 2) (2 ^ (2 * p) - 1 : ℤ) :=
    IsCoprime.pow_left ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hnd)
  exact hcop.dvd_of_dvd_mul_left hA

/-- Kummer-type step: `q² ∤ ∑_{k<q} k^{2p}` where `q = 2p - 1` is prime and `p > 3`. -/
lemma partB {p : ℕ} (hq : (2 * p - 1).Prime) (h3 : 3 < p) :
    ¬ ((2 * p - 1 : ℕ) : ℤ) ^ 2 ∣ ∑ k ∈ range (2 * p - 1), (k : ℤ) ^ (2 * p) := by
  set q := 2 * p - 1 with hqdef
  intro hT
  have v := voronoi_two hq (by omega) (2 * p)
  have hA : (q : ℤ) ^ 2 ∣ (2 ^ (2 * p) - 1) * ∑ k ∈ range q, (k : ℤ) ^ (2 * p) :=
    dvd_mul_of_dvd_right hT _
  have hX : (q : ℤ) ^ 2 ∣ ((2 * p : ℕ) : ℤ) * q * 2 ^ (2 * p - 1)
      * ∑ k ∈ range q, (k : ℤ) ^ (2 * p - 1) * ((2 * k / q : ℕ) : ℤ) := by
    have := dvd_sub hA v
    rwa [sub_sub_cancel] at this
  set Y := ∑ k ∈ range q, (k : ℤ) ^ (2 * p - 1) * ((2 * k / q : ℕ) : ℤ) with hYdef
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hW : (q : ℤ) ∣ ((2 * p : ℕ) : ℤ) * 2 ^ (2 * p - 1) * Y := by
    have : (q : ℤ) * q ∣ (q : ℤ) * (((2 * p : ℕ) : ℤ) * 2 ^ (2 * p - 1) * Y) := by
      rw [← sq]; convert hX using 1; ring
    exact (mul_dvd_mul_iff_left hq0).mp this
  have hqpr : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  rcases hqpr.dvd_or_dvd hW with h | hY
  · rcases hqpr.dvd_or_dvd h with h | h
    · have h1 : ((2 * p : ℕ) : ℤ) = q + 1 := by rw [hqdef]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * p)]; ring
      rw [h1] at h
      have := (Int.dvd_add_right (dvd_refl _)).mp h
      have := Int.eq_one_of_dvd_one (by positivity) this
      have : q = 1 := by exact_mod_cast this
      omega
    · have := Int.le_of_dvd (by norm_num) (hqpr.dvd_of_dvd_pow h)
      have : q ≤ 2 := by exact_mod_cast this
      omega
  · have := Fact.mk hq
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd Y q).mpr hY
    rw [hYdef] at h0
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast] at h0
    rw [show 2 * p - 1 = q from rfl] at h0
    simp only [ZMod.pow_card] at h0
    have hW' : ((∑ k ∈ range q, k * (2 * k / q) : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sum]; simp only [Nat.cast_mul]; exact h0
    have hdvd := (ZMod.natCast_eq_zero_iff _ q).mp hW'
    have hsum : ∑ k ∈ range q, k * (2 * k / q) = ∑ k ∈ Ico p q, k := by
      have h1 : ∑ k ∈ range q, k * (2 * k / q) = ∑ k ∈ range q, if p ≤ k then k else 0 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k < q := Finset.mem_range.mp hk
        split_ifs with hpk
        · rw [Nat.div_eq_of_lt_le (by omega : 1 * q ≤ 2 * k) (by omega : 2 * k < (1 + 1) * q),
            mul_one]
        · rw [Nat.div_eq_of_lt (by omega), mul_zero]
      have h2 : (range q).filter (fun k => p ≤ k) = Ico p q := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [h1, ← Finset.sum_filter, h2]
    rw [hsum] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have g1 := Finset.sum_range_id_mul_two q
    have g2 := Finset.sum_range_id_mul_two p
    have g3 := Finset.sum_range_add_sum_Ico (fun k => k) (by omega : p ≤ q)
    have key : q * (q - 1) = p * (p - 1) + q * (2 * c) := by
      rw [← g1, ← g2, ← g3, hc]; ring
    have hpp : q ∣ p * (p - 1) := (Nat.dvd_add_right (dvd_mul_right q (2 * c))).mp
      (by rw [add_comm, ← key]; exact dvd_mul_right q (q - 1))
    rcases (Nat.Prime.dvd_mul hq).mp hpp with h | h
    · have := Nat.le_of_dvd (by omega) h; omega
    · have := Nat.le_of_dvd (by omega) h; omega


/-- Denominators of coefficients in Stirling's expansion for $\log(\Gamma(z))$
(copied verbatim from `FormalConjectures/OEIS/46969.lean`). -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

/-- The only primes `s` with `s - 1 ∣ 2p` are `2` and `3`. -/
lemma vonStaudt_primes {p : ℕ} (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    ((range (2 * p + 2)).filter fun s => Nat.Prime s ∧ s - 1 ∣ 2 * p) = {2, 3} := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hs, hd⟩
    have hs2 := hs.two_le
    obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.mp hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hy with rfl | rfl <;>
      rcases (Nat.dvd_prime hp).mp hz with rfl | rfl
    · left; omega
    · exfalso
      have hodd : Odd z := hp.odd_of_ne_two (by omega)
      have hev : Even s := by
        obtain ⟨r, hr⟩ := hodd
        exact ⟨r + 1, by omega⟩
      have := (hs.even_iff).mp hev
      omega
    · right; omega
    · exfalso
      have h3p : ¬ 3 ∣ z := fun h => by
        rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
      have h3q : ¬ 3 ∣ 2 * z - 1 := fun h => by
        rcases (Nat.dvd_prime hp').mp h with h | h <;> omega
      have hz0 : z % 3 ≠ 0 := fun h => h3p (Nat.dvd_of_mod_eq_zero h)
      have hq0 : (2 * z - 1) % 3 ≠ 0 := fun h => h3q (Nat.dvd_of_mod_eq_zero h)
      have hz1 : z % 3 = 1 := by
        have := Nat.mod_lt z (by norm_num : 3 > 0)
        interval_cases h : z % 3
        · exact absurd rfl hz0
        · rfl
        · exfalso; apply hq0; omega
      have h3s : 3 ∣ s := Nat.dvd_of_mod_eq_zero (by omega)
      rcases (Nat.dvd_prime hs).mp h3s with h | h <;> omega
  · rintro (rfl | rfl)
    · exact ⟨by omega, Nat.prime_two, by simp⟩
    · exact ⟨by omega, Nat.prime_three, ⟨p, by omega⟩⟩

theorem conjecture1 (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    (a p / 12).Prime := by
  set q := 2 * p - 1 with hqdef
  set B := bernoulli (2 * p) with hBdef
  -- von Staudt–Clausen: `B + 1/2 + 1/3` is an integer
  obtain ⟨N, hN⟩ := Bernoulli.vonStaudt_clausen p
  rw [vonStaudt_primes hp hp' h3, Finset.sum_pair (by decide)] at hN
  push_cast at hN
  set Z : ℤ := 6 * N - 5 with hZdef
  have hZ : 6 * B = (Z : ℚ) := by rw [hZdef]; push_cast; rw [hN]; ring
  -- Faulhaber + Voronoi at `p`: `p ∣ Z`
  have hpZ : (p : ℤ) ∣ Z := by
    have hF := faulhaber_pdiv (ℓ := p) (m := 2 * p) hp (by omega) (by omega) ⟨p - 1, by omega⟩
      (fun h => by
        have h' : p ∣ 2 * p + 1 := Int.natCast_dvd_natCast.mp h
        have := (Nat.dvd_add_right (dvd_mul_left p 2)).mp h'
        exact hp.one_lt.ne' (Nat.dvd_one.mp this))
    obtain ⟨c, hc⟩ := partA hp h3
    have hT : PDiv p 2 (∑ k ∈ range p, (k : ℚ) ^ (2 * p)) := by
      have : (∑ k ∈ range p, (k : ℚ) ^ (2 * p)) = (p : ℚ) ^ 2 * c := by exact_mod_cast hc
      rw [this]; exact PDiv.ofInt hp 2 c
    have hpB := hT.sub hp hF
    rw [sub_sub_cancel] at hpB
    obtain ⟨u, v, hv, huv⟩ := hpB
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hBv : B * v = p * u := by
      have : (p : ℚ) * (B * v - p * u) = 0 := by linear_combination huv
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hp0
      · linarith
    have hZv : Z * v = 6 * p * u := by
      have : (Z : ℚ) * v = 6 * p * u := by rw [← hZ]; linear_combination 6 * hBv
      exact_mod_cast this
    have hdvd : (p : ℤ) ∣ Z * v := ⟨6 * u, by rw [hZv]; ring⟩
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdvd with h | h
    · exact h
    · exact absurd h hv
  -- Faulhaber + Voronoi at `q`: `q ∤ Z`
  have hqZ : ¬ (q : ℤ) ∣ Z := by
    rintro ⟨Z', hZ'⟩
    have hq7 : 7 ≤ q := by omega
    have hF := faulhaber_pdiv (ℓ := q) (m := 2 * p) hp' (by omega) (by omega) ⟨p - 1, by omega⟩
      (fun h => by
        have h' : q ∣ 2 * p + 1 := Int.natCast_dvd_natCast.mp h
        have : q ∣ 2 := (Nat.dvd_add_right (dvd_refl q)).mp (by rwa [show 2 * p + 1 = q + 2 by omega] at h')
        have := Nat.le_of_dvd (by norm_num) this
        omega)
    have hn6 : ¬ (q : ℤ) ∣ 6 := fun h => by
      have : q ∣ 6 := Int.natCast_dvd_natCast.mp (by exact_mod_cast h)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have hqB : PDiv q 2 ((q : ℚ) * B) :=
      ⟨Z', 6, hn6, by
        have : (Z : ℚ) = q * Z' := by exact_mod_cast hZ'
        push_cast
        linear_combination (q : ℚ) * hZ + (q : ℚ) * this⟩
    have hT := hF.add hp' hqB
    rw [sub_add_cancel] at hT
    have hT' : PDiv q 2 ((∑ k ∈ range q, (k : ℤ) ^ (2 * p) : ℤ) : ℚ) := by push_cast; exact hT
    exact partB hp' h3 (hT'.int_dvd hp')
  -- the denominator
  obtain ⟨M, hM⟩ := hpZ
  have hq1 : 1 ≤ q := hp'.one_lt.le
  have ha : a p = 12 * q := by
    have hdef : a p = (B / ((2 * p * q : ℕ) : ℚ)).den := by
      simp [a, hp.ne_zero, hBdef, hqdef]
    rw [hdef]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hp'.ne_zero
    have heq : B / ((2 * p * q : ℕ) : ℚ) = ((M : ℤ) : ℚ) / ((12 * (q : ℤ) : ℤ) : ℚ) := by
      have hB' : B = (p : ℚ) * M / 6 := by
        have : (Z : ℚ) = p * M := by exact_mod_cast hM
        linear_combination hZ / 6 + this / 6
      rw [hB']; push_cast; field_simp; ring
    rw [heq]
    have h2 : ¬ (2 : ℤ) ∣ M := fun h => by
      have : (2 : ℤ) ∣ Z := hM ▸ dvd_mul_of_dvd_right h _
      omega
    have h3' : ¬ (3 : ℤ) ∣ M := fun h => by
      have : (3 : ℤ) ∣ Z := hM ▸ dvd_mul_of_dvd_right h _
      omega
    have hqM : ¬ (q : ℤ) ∣ M := fun h => hqZ (hM ▸ dvd_mul_of_dvd_right h _)
    have c2 : Nat.Coprime M.natAbs 2 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        fun h => h2 (by exact_mod_cast Int.natCast_dvd.mpr h))
    have c3 : Nat.Coprime M.natAbs 3 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        fun h => h3' (by exact_mod_cast Int.natCast_dvd.mpr h))
    have cq : Nat.Coprime M.natAbs q :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp').mpr
        fun h => hqM (Int.natCast_dvd.mpr h))
    have hcop : Nat.Coprime M.natAbs (12 * (q : ℤ)).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_natCast, show Int.natAbs 12 = 2 ^ 2 * 3 from rfl]
      exact ((c2.pow_right 2).mul_right c3).mul_right cq
    have hden := Rat.den_div_eq_of_coprime (by positivity : (0 : ℤ) < 12 * (q : ℤ)) hcop
    exact_mod_cast hden
  rw [ha, Nat.mul_div_cancel_left q (by norm_num)]
  exact hp'

end OeisA46969Proof

#print axioms OeisA46969Proof.conjecture1

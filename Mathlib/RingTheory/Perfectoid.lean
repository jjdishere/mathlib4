/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.RingTheory.Perfection
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

universe u

/-!
# Perfectoid Rings and Perfectoid Fields
-/


open Valuation Valued Function NNReal CategoryTheory MonoidWithZeroHom.ValueGroup₀

class PerfectoidField (p : outParam ℕ) [Fact p.Prime] (K : Type*) [Field K] [u : UniformSpace K]
    : Prop extends IsUniformAddGroup K, IsTopologicalDivisionRing K, CompleteSpace K where
--   exists_val_top : ∃ v : Valuation K ℝ≥0, ∀ (s : Set K),
--       s ∈ nhds 0 ↔ ∃ (γ : ℝ≥0ˣ), {x : K | v x < γ} ⊆ s
        -- This is wrong, wait for change of Valued.
  exists_val_top : ∃ vK : Valued K ℝ≥0, vK.toUniformSpace = u
  exists_p_mem_span_pow_p :
      let _ : Valued K ℝ≥0 := Classical.choose exists_val_top
      ∃ π : 𝒪[K], ¬ IsUnit π ∧ (p : 𝒪[K]) ∈ Ideal.span {π ^ p}
  exist_p_th_root :
      let _ : Valued K ℝ≥0 := Classical.choose exists_val_top
      ∀ x : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])}, ∃ y : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])} , x = y ^ p
      -- Surjective <| frobenius (𝒪[K]⧸Ideal.span {(p : 𝒪[K])}) p

-- This is for the definition of the category of perfectoid fields
class PerfectoidFieldObj (p : outParam ℕ) [Fact p.Prime] (K : Type u)
    : Type (u + 1) extends Field K, UniformSpace K, PerfectoidField p K

-- `Valuation is not a part of information it only require the topology comes from a valuation`

/--
A convenience class, for a perfectoid field endowed with a valuation.
No instance of this class should be registered: It should be used as `letI := valuedPerfectoidField`
to endow a perfectoid field with a valued instance.
-/
class ValuedPerfectoidField (p : outParam ℕ) [Fact p.Prime] (K : Type u) [Field K]
    : Type (u + 1) extends Valued K ℝ≥0, CompleteSpace K
    where
  exists_p_mem_span_pow_p : ∃ π : 𝒪[K], ¬ IsUnit π ∧ (p : 𝒪[K]) ∈ Ideal.span {π ^ p}
  exist_p_th_root : ∀ x : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])},
      ∃ y : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])} , x = y ^ p
      -- Surjective <| frobenius (𝒪[K]⧸Ideal.span {(p : 𝒪[K])}) p

noncomputable
def valuedPerfectoidField (p : outParam ℕ) [Fact p.Prime] (K : Type*) [Field K] [u : UniformSpace K]
    [h : PerfectoidField p K] : ValuedPerfectoidField p K where
  -- toValued := h.exists_val_top.choose.replaceTopology
-- (congrArg _ h.exists_val_top.choose_spec.symm)
  -- `should use above`
  v := h.exists_val_top.choose.v
  is_topological_valuation := sorry
  exists_p_mem_span_pow_p := h.exists_p_mem_span_pow_p
  exist_p_th_root := h.exist_p_th_root



namespace ValuedPerfectoidField

variable (p : outParam ℕ) [Fact p.Prime] (K : Type*) [Field K]

/-- The valuation of `p` is `< 1` — a consequence of the class's own
`exists_p_mem_span_pow_p` axiom (a non-unit `π ∈ 𝒪[K]` with `p ∈ (π^p)`):
writing `p = π^p · a` with `a ∈ 𝒪[K]`, one gets
`v p = (v π)^p · v a ≤ (v π)^p ≤ v π < 1`.
Cf. Scholze, Lemma 3.2 (p. 15) (the p-divisibility of the value group, proved
from the same hypothesis — not formalized here) and Wedhorn, Lemma 6.6.
Stated with the class's own valuation (the data version); the ∃-valuation
form of `PerfectoidField` would need the equivalence-of-valuations machinery. -/
theorem val_p_lt_1 [perf : ValuedPerfectoidField p K] : perf.toValued.v p < 1 := by
  let v : Valuation K ℝ≥0 := perf.toValued.v
  obtain ⟨π, hπ, hp⟩ := perf.exists_p_mem_span_pow_p
  -- v π ≤ 1 (π ∈ 𝒪[K]) and v π ≠ 1 (π not a unit of 𝒪[K] ⟹ v π = 1 would be
  -- a unit by the integer API), hence v π < 1
  have hπ_le : v π.1 ≤ 1 := by
    exact (Valuation.mem_integer_iff v π.1).mp (by simpa [v] using π.2)
  have hπ_ne : v π.1 ≠ 1 := by
    intro h1
    have hunit : IsUnit π := (integer.integers v).isUnit_iff_valuation_eq_one.mpr (by
      change v (π : K) = 1
      simpa [v] using h1)
    exact hπ hunit
  have hπ_lt : v π.1 < 1 := lt_of_le_of_ne hπ_le hπ_ne
  -- p = π^p · a for some a ∈ 𝒪[K]
  rcases (Ideal.mem_span_singleton.mp hp) with ⟨a, ha⟩
  -- v p = (v π)^p · v a
  have hp_val : v (p : K) = v (π.1 : K) ^ p * v (a.1 : K) := by
    have hco : (p : K) = (π.1 : K) ^ p * (a.1 : K) := by
      exact_mod_cast ha
    rw [hco, map_mul, map_pow]
  have ha_le : v (a.1 : K) ≤ 1 := by
    exact (Valuation.mem_integer_iff v (a.1 : K)).mp (by simpa [v] using a.2)
  have hpow : v (π.1 : K) ^ p ≤ v (π.1 : K) := by
    have hp1 : 1 ≤ p := by
      have hp2 : 2 ≤ p := (Nat.Prime.two_le (Fact.out : p.Prime))
      omega
    simpa using pow_le_pow_of_le_one zero_le hπ_le (m := 1) (n := p) hp1
  calc
    v (p : K) = v (π.1 : K) ^ p * v (a.1 : K) := hp_val
    _ ≤ v (π.1 : K) ^ p * 1 := mul_le_mul' le_rfl ha_le
    _ = v (π.1 : K) ^ p := by rw [mul_one]
    _ ≤ v (π.1 : K) := hpow
    _ < 1 := hπ_lt

end ValuedPerfectoidField

namespace PerfectoidField

variable (p : outParam ℕ) [Fact (p.Prime)] (K : Type*) {Γ : outParam Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [vK : Valued K ℝ≥0] [CompleteSpace K]
    [perf : PerfectoidField p K]

/-- An element of a topological ring is *topologically nilpotent* if its powers
converge to zero. Wedhorn, Lemma 6.6 (p. 48): "for every topologically
nilpotent element f ∈ A there exists n ∈ ℕ such that f^n ∈ a" for every open
ideal a — i.e. the powers are eventually in every neighborhood of 0. -/
def IsTopologicalNilpotent (x : K) : Prop :=
  Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds 0)

/-- If the valuation of `x` is `< 1`, then `x` is topologically nilpotent:
`v (x^n) = (v x)^n → 0` and the sets `{y | v y < γ}` form a neighborhood
basis of `0` in the valuation topology (the `is_topological_valuation` axiom
of `Valued`). This is the standard fact behind Scholze, Lemma 3.2 / Wedhorn,
Lemma 6.6: `p` is topologically nilpotent. -/
theorem topologicallyNilpotent_of_val_lt_one {x : K} (hx : vK.v x < 1) :
    Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds 0) := by
  intro U hU
  have hU' : (0 : K) ∈ U := mem_of_mem_nhds hU
  rcases ((inferInstance : Valued K ℝ≥0).is_topological_valuation U).mp hU with ⟨γ, hγ⟩
  -- the value-group ball {r | r < embedding γ.1} is a neighborhood of 0 in ℝ≥0
  have hγ0 : 0 < embedding γ.1 := by
    have hne : embedding γ.1 ≠ 0 := by
      simpa using (embedding_strictMono (v := vK.v)).injective.ne (Units.ne_zero γ)
    exact lt_of_le_of_ne zero_le (Ne.symm hne)
  have hset : {r : ℝ≥0 | r < embedding γ.1} ∈ nhds (0 : ℝ≥0) :=
    isOpen_Iio.mem_nhds hγ0
  have hpow : Filter.Tendsto (fun n : ℕ => (vK.v x) ^ n) Filter.atTop (nhds (0 : ℝ≥0)) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hx
  have hevent : ∀ᶠ n in Filter.atTop, (vK.v x) ^ n < embedding γ.1 := by
    simpa using hpow.eventually hset
  change ∀ᶠ n in Filter.atTop, x ^ n ∈ U
  filter_upwards [hevent] with n hn
  exact hγ (by
    -- v (x^n) = (v x)^n < embedding γ.1, and restrict_lt_iff_lt_embedding
    change vK.v.restrict (x ^ n) < γ.1
    rw [restrict_lt_iff_lt_embedding (v := vK.v)]
    simpa [map_pow] using hn)



/-- A perfectoid field is algebraically closed iff its tilt is. (The reverse
direction via the untilt is out of scope; the statement is a placeholder in
jjdishere's draft.) -/
theorem isAlgClosed_iff_isAlgClosed_tilt (K : Type*) {Γ : outParam Type*}
    [Field K] [LinearOrderedCommGroupWithZero Γ]
    [vK : Valued K ℝ≥0] [CompleteSpace K] [perf : PerfectoidField p K] :
    IsAlgClosed K ↔
      IsAlgClosed (@_root_.Tilt K _ vK.v 𝒪[K] _ _ (integer.integers vK.v) p _
        ⟨ne_of_lt <| (by
          -- the vK-based `val_p_lt_1`; the equivalence-of-valuations machinery (see `Tilt`)
          sorry)⟩) :=
    sorry -- TODO(sfingali): both directions; the tilt of an algebraically closed field is algebraically closed (perfectoid-fields folklore)

def valuedRankOneValuationFiniteDimensional (K L : Type*) [Field K]
    [vK : Valued K ℝ≥0] [CompleteSpace K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    Valued L ℝ≥0 := sorry

-- `In the case L has is an extension of K complete with respect to a rank one valuation, L has a`
-- `unique extension of valuation. But it cannot be an instance`

def ofFiniteDimensional (p : outParam ℕ) [Fact p.Prime] (K L : Type*) [Field K]
    [vK : Valued K ℝ≥0] [CompleteSpace K] [PerfectoidField p K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [UniformSpace L] :
    PerfectoidField p L := sorry -- uniform space structure comes from K v.s.

section FiniteExts


-- `How to define the category of finite extensions?`
-- `It depends on how to recover the Galois group from this category?`
-- 1. subfields of algebraic closure
-- 2. all fields inside some type universe
--    (CategoryTheory.Bundled Field, CategoryTheory.BundledHom),
--    then use CategoryTheory.Over and CategoryTheory.FullSubcategory
-- 3. first define a structure FiniteExtensionOver K and its boundled hom,
--    then use CategoryTheory.Bundled.
-- 3 is easiest but not so aligned to mathlib style??
-- connect
def FiniteExtension (K : Type*) [Field K] : Type* := sorry

instance FiniteExtension.category (K : Type*) [Field K] : Category (FiniteExtension K) := sorry

end FiniteExts

-- `How to define the category of perfectoid fields over K?`
-- CategoryTheory.Over
-- 2. the category of all perfectoid fields then use CategoryTheory.Over?
-- 3. first define a structure perfectoid fields K and its boundled hom,
--    then use CategoryTheory.Bundled.

-- inorder to use Cat.bundled, One need to create a extending structure
def PerfFieldCat := CategoryTheory.Bundled (PerfectoidFieldObj p)
-- topological field only + some prop

def PerfectoidFieldOver (K : Type*) [Field K]: Type* := sorry

instance PerfectoidFieldOver.category (K : Type*) [Field K] :
    Category (PerfectoidFieldOver K) := sorry

def PerfectoidField.TiltingFunctor : (PerfectoidFieldOver K) ⥤
    (PerfectoidFieldOver
      (@_root_.Tilt K _ vK.v 𝒪[K] _ _ (integer.integers vK.v) p _
        ⟨ne_of_lt <| (by
          -- TODO(sfingali): as in `Tilt` (the vK-based `val_p_lt_1`).
          sorry)⟩)) := sorry

def PerfectoidField.TiltingFinExt : FiniteExtension K ≌
    FiniteExtension
      (@_root_.Tilt K _ vK.v 𝒪[K] _ _ (integer.integers vK.v) p _
        ⟨ne_of_lt <| (by
          -- TODO(sfingali): as in `Tilt` (the vK-based `val_p_lt_1`).
          sorry)⟩) := sorry

end PerfectoidField


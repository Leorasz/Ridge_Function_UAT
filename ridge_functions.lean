import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

variable {n : ℕ}
variable (K : Set (EuclideanSpace ℝ (Fin n)))

--setup to restrict polynomials to K
def coord (i : Fin n) : C(K, ℝ) :=
  ContinuousMap.mk
    (fun x => x.val i)
    ((continuous_apply i).comp continuous_subtype_val)

--used to switch between MvPolynomial and generic continuous functions
def polyHom : MvPolynomial (Fin n) ℝ →ₐ[ℝ] C(K, ℝ) :=
  MvPolynomial.aeval fun i => coord K i

--base ridge function
def ridgeFunction (Ω : Finset (Fin n → ℝ)) (a : Ω) (f : C(ℝ, ℝ)) : C(↑K, ℝ) :=
  ContinuousMap.mk
    (fun x => f ((fun y : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, a.val i * y i) x.val))
    (by
    apply Continuous.comp' (ContinuousMap.continuous f)
    apply Continuous.comp'
    · exact continuous_finset_sum Finset.univ (fun i _ => continuous_apply i)
    exact Continuous.mul continuous_const continuous_subtype_val)

--monomial ridge functions
def monoRidges (Ω : Finset (Fin n → ℝ)) (m : ℕ) : Submodule ℝ C(↑K, ℝ) :=
  Submodule.span ℝ {g | ∃ (a : Ω), g = ridgeFunction K Ω a ⟨fun (x : ℝ) => x ^ m, continuous_pow m⟩}

--monoRidges but for the homogeneous submodule to properly use ⊥ and ⊤
def monoPoly (Ω : Finset (Fin n → ℝ)) (m : ℕ) : Submodule ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) :=
  Submodule.comap
    (LinearMap.domRestrict (polyHom K).toLinearMap (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m))
    (monoRidges K Ω m)

--show you can make homogeneous polynomials out of ridge functions, given Ω is good enough
theorem trivial_annihilator_implies_eq (Ω : Finset (Fin n → ℝ)) (m : ℕ)
  (h_annihilator : (monoPoly K Ω m).dualAnnihilator = ⊥) :
  Submodule.map (polyHom K).toLinearMap (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) =
    monoRidges K Ω m := by
  apply le_antisymm
  ·
    intro g hg
    rw [Submodule.mem_map] at hg
    obtain ⟨p, hp, rfl⟩ := hg
    have : ⟨p, hp⟩ ∈ monoPoly K Ω m := by
      rw [Submodule.dualAnnihilator_eq_bot_iff.mp h_annihilator]
      exact trivial
    exact this
  refine Submodule.span_le.mpr fun g hg => ?_
  simp only [Set.mem_setOf_eq] at hg
  obtain ⟨a, rfl⟩ := hg
  let q : MvPolynomial (Fin n) ℝ := ∑ i : Fin n, MvPolynomial.C (a.val i) * MvPolynomial.X i
  have hq : q.IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    exact MvPolynomial.isHomogeneous_C_mul_X ((a : Fin n → ℝ) i) i
  let p := q ^ m
  have hp : p.IsHomogeneous m := by
    simp [p]
    nth_rewrite 2 [← one_mul m]
    exact MvPolynomial.IsHomogeneous.pow hq m
  have hp_mem : p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ m := by
    exact hp
  have heq : (polyHom K) p = ridgeFunction K Ω a ⟨fun x => x ^ m, continuous_pow m⟩ := by
    ext x
    simp only [ridgeFunction, ContinuousMap.coe_mk, polyHom]
    simp [p, q, coord]
  exact heq ▸ Submodule.mem_map_of_mem hp_mem

def coords : Set C(K, ℝ) := Set.range (coord K)

--this is the subalgebra to use for Stone-Weierstrass
def polySubalg : Subalgebra ℝ C(K, ℝ) :=
  Algebra.adjoin ℝ (coords K)

--relation between polySubalg and polyHom, needed to go from MvPolynomial to Algebras for Stone-Weierstrass
lemma polySubalg_eq_range_aeval : polySubalg K = (polyHom K).range := by
  rw [polySubalg, coords, Algebra.adjoin_range_eq_range_aeval,
    polyHom]

--entire span of ridge functions
def ridges (Ω : Finset (Fin n → ℝ)) : Submodule ℝ C(↑K, ℝ) :=
  Submodule.span ℝ {g | ∃ (a : Ω) (f : C(ℝ, ℝ)), g = ridgeFunction K Ω a f}

--showing you can make polynomials out of ridge functions by using what we have for homogeneous polynomials
theorem homogeneous_ridged_implies_polynomials (Ω : Finset (Fin n → ℝ))
  (h : ∀(m : ℕ), Submodule.map (polyHom K).toLinearMap (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) = monoRidges K Ω m) :
  (polySubalg K).toSubmodule ≤ ridges K Ω := by
  rw [polySubalg_eq_range_aeval]
  intro f hf
  obtain ⟨p, rfl⟩ := hf
  rw [← MvPolynomial.sum_homogeneousComponent p]
  have mono_submod_ridges (m : ℕ) : monoRidges K Ω m ≤ ridges K Ω := by
    apply Submodule.span_mono
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    obtain ⟨a, f, rfl⟩ := hg
    exact ⟨a, ⟨(· ^ m), continuous_pow m⟩, rfl⟩
  have h_map_sum : (polyHom K).toRingHom (∑ i ∈ Finset.range (p.totalDegree + 1), (MvPolynomial.homogeneousComponent i) p) =
    ∑ i ∈ Finset.range (p.totalDegree + 1), (polyHom K) ((MvPolynomial.homogeneousComponent i) p) := by
    exact map_sum (polyHom K).toRingHom _ _
  rw [h_map_sum]
  have h_each_in_ridges (m : ℕ) (hm : m ∈ Finset.range (p.totalDegree + 1)) :
    (polyHom K) ((MvPolynomial.homogeneousComponent m) p) ∈ ridges K Ω := by
    have hmem : (MvPolynomial.homogeneousComponent m) p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ m := by
      exact MvPolynomial.homogeneousComponent_mem m p
    have : (polyHom K).toLinearMap ((MvPolynomial.homogeneousComponent m) p) ∈
        Submodule.map (polyHom K).toLinearMap (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) := by
      exact Submodule.mem_map_of_mem hmem
    rw [h m] at this
    exact mono_submod_ridges m this
  exact Submodule.sum_mem (ridges K Ω) h_each_in_ridges

--ridge functions except the 1D function is a polynomial
def polynomialRidges (Ω : Finset (Fin n → ℝ)) : Submodule ℝ C(↑K, ℝ) :=
  Submodule.span ℝ {g | ∃ (a : Ω) (f : Polynomial ℝ), g = ridgeFunction K Ω a
    ⟨fun t => f.eval t, f.continuous⟩}

--shows that polynomial ridges are ridges
lemma polynomial_ridges_submod_ridges (Ω : Finset (Fin n → ℝ)): polynomialRidges K Ω ≤ ridges K Ω := by
  rw [polynomialRidges, ridges]
  apply Submodule.span_mono
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  obtain ⟨a, f, rfl⟩ := hg
  exact ⟨a, ⟨fun t ↦ f.eval t, f.continuous⟩, rfl⟩

variable [CompactSpace K]

--basically just getting Stone-Weierstrass ready for polySubalg
lemma polySubalg_dense : (polySubalg K).topologicalClosure = ⊤ := by
  have hp : (polySubalg K).SeparatesPoints := by
    rw [Subalgebra.SeparatesPoints, Set.SeparatesPoints]
    intro x y hxy
    have : ∃ i, x.val i ≠ y.val i := by
      by_contra h'
      push_neg at h'
      exact hxy (Subtype.ext (funext h'))
    obtain ⟨i, hi⟩ := this
    refine ⟨⇑(coord K i), ⟨coord K i, Algebra.subset_adjoin (Set.mem_range_self i), rfl⟩, ?_⟩
    simpa [coord] using hi
  exact ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints (polySubalg K) hp

--since polySubalg K is a submodule of S, the closure of S should be the whole space too
theorem dense_of_contains_polySubalg {S : Submodule ℝ C(↑K, ℝ)}
  (h : (polySubalg K).toSubmodule ≤ S) :
  S.topologicalClosure = ⊤ := by
  have h_subset : (polySubalg K : Set C(↑K, ℝ)) ⊆ ↑S := h
  have h_dense : closure (polySubalg K : Set C(↑K, ℝ)) = (⊤ : Set C(↑K, ℝ)) := by
    have := (polySubalg K).topologicalClosure_coe
    rw [polySubalg_dense] at this
    exact id (Eq.symm this)
  have h_closure_mono := closure_mono h_subset
  rw [h_dense] at h_closure_mono
  have h_univ : closure (↑S) = (⊤ : Set C(↑K, ℝ)) := by
    exact Eq.symm (Set.Subset.antisymm h_closure_mono fun ⦃a⦄ a ↦ trivial)
  exact Submodule.dense_iff_topologicalClosure_eq_top.mp fun x ↦ h_closure_mono trivial

--final theorem, closure of ridge functions in compact space of continuous functions given Ω doesn't give rise to any annihilators
theorem ridges_closed (Ω : Finset (Fin n → ℝ)) (h_annihilator : ∀m, (monoPoly K Ω m).dualAnnihilator = ⊥) :
  (ridges K Ω).topologicalClosure = ⊤ := by
  have polynomials : (polySubalg K).toSubmodule ≤ ridges K Ω := by
    have : ∀(m : ℕ), Submodule.map (polyHom K).toLinearMap (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) = monoRidges K Ω m := by
      exact fun m ↦ trivial_annihilator_implies_eq K Ω m (h_annihilator m)
    exact homogeneous_ridged_implies_polynomials K Ω this
  exact dense_of_contains_polySubalg K polynomials

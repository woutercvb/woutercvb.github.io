/-
23 February 2026,  Lean version v4.24.0.

An AI-assisted Lean formalization of Lemma 1 from the paper "The chromatic number of finite projective spaces" by Anurag Bishnoi, Wouter Cames van Batenburg, Ananthakrishnan Ravi.
See https://arxiv.org/abs/2512.01760

In the file below, Lemma 1 is called "theorem chi_subadditive". 
It compiles without errors and only depends on the standard axioms [propext, Classical.choice, Quot.sound], so theorem chi_subadditive is true. However, I'm not experienced enough with Lean to be sure that the statement of Lemma 1 has been formalized correctly. 

Lemma 1: for all prime powers q ≥ 2, for all integers t ≥ 2, and for all integers 1 ≤ d ≤ n−1,
χq(t; n) ≤ χq(t;n −d)+χq(t;d).

Here χq(t;n) denotes the chromatic number of the hypergraph with vertices = points of the projective space PG(n−1,q), and hyperedges = the sets of points of (t − 1)-dimensional projective subspaces.

Alternatively: 
Let V be the n-dimensional vector space over the finite field Fq.
Then χq(t;n) is the chromatic number of the hypergraph with vertices = the 1-dimensional vector subspaces of V, and  hyperedges = the maximal sets of vertices that lie in a common t-dimensional vector subspace of V.

The formalization was made with the help of Aristotle and Claude.
No AI was used for the original paper https://arxiv.org/abs/2512.01760
-/


import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128


noncomputable section

def proj_A (K : Type*) [Field K] (n d : ℕ) (hd : d ≤ n) : (Fin n → K) →ₗ[K] (Fin (n - d) → K) where
  toFun v := fun j => v ⟨j, by omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

def proj_B (K : Type*) [Field K] (n d : ℕ) (hd : d ≤ n) : (Fin n → K) →ₗ[K] (Fin d → K) where
  toFun v := fun j => v ⟨n - d + j, by omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

def IsScalarInvariant (K : Type*) [Field K] {n k : ℕ} (c : (Fin n → K) → Fin k) : Prop :=
  ∀ (a : K) (v : Fin n → K), a ≠ 0 → v ≠ 0 → c (a • v) = c v

def IsMonochromatic (K : Type*) [Field K] {n k : ℕ} (c : (Fin n → K) → Fin k) (S : Submodule K (Fin n → K)) : Prop :=
  ∃ i, ∀ v ∈ S, v ≠ 0 → c v = i

def IsValidColoring (K : Type*) [Field K] (n t : ℕ) {k : ℕ} (c : (Fin n → K) → Fin k) : Prop :=
  IsScalarInvariant K c ∧
  ∀ S : Submodule K (Fin n → K), Module.finrank K S = t → ¬IsMonochromatic K c S

noncomputable def chi (K : Type*) [Field K] (n t : ℕ) : ℕ :=
  sInf {k | ∃ c : (Fin n → K) → Fin k, IsValidColoring K n t c}

def combine_colorings (K : Type*) [Field K] {n d kA kB : ℕ} (hd : d ≤ n)
    (cA : (Fin (n - d) → K) → Fin kA) (cB : (Fin d → K) → Fin kB) :
    (Fin n → K) → Fin (kA + kB) :=
  fun v =>
    if _ : proj_B K n d hd v = 0 then
      Fin.castAdd kB (cA (proj_A K n d hd v))
    else
      Fin.natAdd kA (cB (proj_B K n d hd v))

lemma ker_proj_A_inf_ker_proj_B_eq_bot (K : Type*) [Field K] (n d : ℕ) (hd : d ≤ n) :
    LinearMap.ker (proj_A K n d hd) ⊓ LinearMap.ker (proj_B K n d hd) = ⊥ := by
  ext v
  simp [proj_A, proj_B];
  apply Iff.intro;
  · intro hv
    ext i
    by_cases hi : i.val < n - d;
    · simpa using congr_fun hv.1 ⟨ i, hi ⟩;
    · convert congr_fun hv.2 ⟨ i - ( n - d ), by rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt i, Nat.sub_add_cancel hd ] ⟩ using 1 ; simp +decide [ Nat.add_sub_of_le ( show n - d ≤ i from le_of_not_gt hi ) ];
  · intro hv
    simp [hv];
    exact ⟨ rfl, rfl ⟩

lemma finrank_map_proj_A_eq_of_le_ker_proj_B (K : Type*) [Field K] (n d : ℕ) (hd : d ≤ n)
    (S : Submodule K (Fin n → K)) (hS : S ≤ LinearMap.ker (proj_B K n d hd)) :
    Module.finrank K (S.map (proj_A K n d hd)) = Module.finrank K S := by
  have h_inj : LinearMap.ker (proj_A K n d hd) ⊓ S = ⊥ := by
    have h_inter : LinearMap.ker (proj_A K n d hd) ⊓ LinearMap.ker (proj_B K n d hd) = ⊥ := by
      exact ker_proj_A_inf_ker_proj_B_eq_bot K n d hd;
    exact eq_bot_iff.mpr ( le_trans ( inf_le_inf_left _ hS ) h_inter.le );
  have h_inj : LinearMap.ker (proj_A K n d hd ∘ₗ Submodule.subtype S) = ⊥ := by
    simp_all +decide [ Submodule.eq_bot_iff ];
  have := LinearMap.finrank_range_of_inj ( show Function.Injective ( proj_A K n d hd ∘ₗ S.subtype ) from LinearMap.ker_eq_bot.mp h_inj );
  convert this using 1;
  rw [ show LinearMap.range ( proj_A K n d hd ∘ₗ S.subtype ) = Submodule.map ( proj_A K n d hd ) S from ?_ ];
  aesop

lemma finrank_map_proj_B_eq_of_inf_ker_eq_bot (K : Type*) [Field K] (n d : ℕ) (hd : d ≤ n)
    (S : Submodule K (Fin n → K)) (hS : S ⊓ LinearMap.ker (proj_B K n d hd) = ⊥) :
    Module.finrank K (S.map (proj_B K n d hd)) = Module.finrank K S := by
  have h_inj : Function.Injective (proj_B K n d hd ∘ Submodule.subtype S) := by
    have h_kernel_trivial : LinearMap.ker (proj_B K n d hd ∘ₗ Submodule.subtype S) = ⊥ := by
      simp_all +decide [ Submodule.eq_bot_iff ];
    exact LinearMap.ker_eq_bot.mp h_kernel_trivial;
  have h_inj : LinearMap.range (LinearMap.comp (proj_B K n d hd) (Submodule.subtype S)) = S.map (proj_B K n d hd) := by
    ext; simp [LinearMap.range_comp];
  rw [ ← h_inj, LinearMap.finrank_range_of_inj ] ; aesop

lemma combine_colorings_is_scalar_invariant (K : Type*) [Field K] {n d kA kB : ℕ} (hd : d ≤ n)
    (cA : (Fin (n - d) → K) → Fin kA) (cB : (Fin d → K) → Fin kB)
    (hA : IsScalarInvariant K cA) (hB : IsScalarInvariant K cB) :
    IsScalarInvariant K (combine_colorings K hd cA cB) := by
  intros a v ha hv
  unfold combine_colorings
  by_cases h : proj_B K n d hd v = 0
  · rw [dif_pos h]
    have h_smul : proj_B K n d hd (a • v) = 0 := by
      rw [LinearMap.map_smul, h, smul_zero]
    rw [dif_pos h_smul]
    apply congr_arg
    rw [LinearMap.map_smul]
    apply hA a (proj_A K n d hd v) ha
    intro h_proj_A
    -- If proj_A v = 0 and proj_B v = 0, then v = 0, contradiction
    have h_v_zero : v = 0 := by
      have h_ker_A : v ∈ LinearMap.ker (proj_A K n d hd) := h_proj_A
      have h_ker_B : v ∈ LinearMap.ker (proj_B K n d hd) := h
      have h_inf : v ∈ LinearMap.ker (proj_A K n d hd) ⊓ LinearMap.ker (proj_B K n d hd) := ⟨h_ker_A, h_ker_B⟩
      rw [ker_proj_A_inf_ker_proj_B_eq_bot K n d hd] at h_inf
      exact h_inf
    contradiction
  · rw [dif_neg h]
    have h_smul : proj_B K n d hd (a • v) ≠ 0 := by
      rw [LinearMap.map_smul]
      intro h_zero
      rw [smul_eq_zero] at h_zero
      cases h_zero
      · contradiction
      · contradiction
    rw [dif_neg h_smul]
    apply congr_arg
    rw [LinearMap.map_smul]
    apply hB a (proj_B K n d hd v) ha h

lemma combine_colorings_monochromatic_A_implies_le_ker_proj_B (K : Type*) [Field K] {n d kA kB : ℕ} (hd : d ≤ n)
    (cA : (Fin (n - d) → K) → Fin kA) (cB : (Fin d → K) → Fin kB)
    (S : Submodule K (Fin n → K)) (i : Fin (kA + kB))
    (hi : i.val < kA)
    (h_mono : ∀ v ∈ S, v ≠ 0 → combine_colorings K hd cA cB v = i) :
    S ≤ LinearMap.ker (proj_B K n d hd) := by
  by_contra h_contra
  obtain ⟨v, hvS, hv_nonzero, hv_proj_B⟩ : ∃ v ∈ S, v ≠ 0 ∧ proj_B K n d hd v ≠ 0 := by
    obtain ⟨ v, hvS, hv ⟩ := Set.not_subset.mp h_contra; use v; aesop;
  have h_combine_nonzero : combine_colorings K hd cA cB v = Fin.natAdd kA (cB (proj_B K n d hd v)) := by
    simp [combine_colorings, hv_proj_B];
  simp_all +decide [ Fin.ext_iff ]

lemma combine_colorings_monochromatic_B_implies_inf_ker_proj_B_eq_bot (K : Type*) [Field K] {n d kA kB : ℕ} (hd : d ≤ n)
    (cA : (Fin (n - d) → K) → Fin kA) (cB : (Fin d → K) → Fin kB)
    (S : Submodule K (Fin n → K)) (i : Fin (kA + kB))
    (hi : kA ≤ i.val)
    (h_mono : ∀ v ∈ S, v ≠ 0 → combine_colorings K hd cA cB v = i) :
    S ⊓ LinearMap.ker (proj_B K n d hd) = ⊥ := by
  have h_contra : ∀ v ∈ S, v ≠ 0 → v ∉ LinearMap.ker (proj_B K n d hd) := by
    intro v hv hv' hv''; specialize h_mono v hv hv'; unfold combine_colorings at h_mono; simp_all +decide [ Fin.ext_iff ] ;
    linarith [ Fin.is_lt ( cA ( proj_A K n d hd v ) ), Fin.is_lt i ];
  exact eq_bot_iff.mpr fun v hv => by_contradiction fun hv' => h_contra v hv.1 hv' hv.2;

def IsProjectiveColoring (K : Type*) [Field K] {n k : ℕ} (c : (Fin n → K) → Fin k) : Prop :=
  ∀ v w : Fin n → K, v ≠ 0 → w ≠ 0 → c v = c w → ∃ a : K, v = a • w

lemma is_valid_of_projective (K : Type*) [Field K] (n t k : ℕ) (ht : 2 ≤ t)
    (c : (Fin n → K) → Fin k) (h_sc : IsScalarInvariant K c) (h_proj : IsProjectiveColoring K c) :
    IsValidColoring K n t c := by
  refine' ⟨ h_sc, _ ⟩;
  intro S hS h_mono
  obtain ⟨i, hi⟩ := h_mono
  have h_proj_mono : ∀ v ∈ S, v ≠ 0 → c v = i := by
    exact hi;
  obtain ⟨v, hv⟩ : ∃ v : Fin n → K, v ∈ S ∧ v ≠ 0 ∧ c v = i := by
    obtain ⟨ v, hv ⟩ := ( show ∃ v : Fin n → K, v ∈ S ∧ v ≠ 0 from by exact not_forall_not.mp fun h => by rw [ show S = ⊥ from eq_bot_iff.mpr fun x hx => by aesop ] at hS; aesop ) ; exact ⟨ v, hv.1, hv.2, hi v hv.1 hv.2 ⟩ ;
  contrapose! h_proj;
  unfold IsProjectiveColoring; simp_all +decide;
  obtain ⟨w, hw⟩ : ∃ w : Fin n → K, w ∈ S ∧ w ≠ 0 ∧ ¬∃ a : K, w = a • v := by
    by_cases h_subspace : S ≤ Submodule.span K {v};
    · have := hS ▸ Submodule.finrank_mono h_subspace; simp_all +decide [ finrank_span_singleton ] ; linarith;
    · simp_all +decide [ SetLike.not_le_iff_exists ];
      exact h_subspace.imp fun x hx => ⟨ hx.1, by rintro rfl; exact hx.2 ( Submodule.zero_mem _ ), fun a ha => hx.2 ( ha ▸ Submodule.mem_span_singleton.mpr ⟨ a, rfl ⟩ ) ⟩;
  exact ⟨ w, hw.2.1, v, hv.2.1, by rw [ h_proj_mono w hw.1 hw.2.1, hv.2.2 ], fun a ha => hw.2.2 ⟨ a, ha ⟩ ⟩

lemma exists_projective_coloring (K : Type*) [Field K] [Finite K] (n : ℕ) :
    ∃ k, ∃ c : (Fin n → K) → Fin k, IsScalarInvariant K c ∧ IsProjectiveColoring K c := by
  have h_finite : ∃ (s : Finset (Fin n → K)), (∀ v ∈ s, v ≠ 0) ∧ (∀ v : Fin n → K, v ≠ 0 → ∃ w ∈ s, ∃ a : K, v = a • w) := by
    have h_finite : Set.Finite {v : Fin n → K | v ≠ 0} := by
      exact Set.toFinite _;
    exact ⟨ h_finite.toFinset, fun v hv => h_finite.mem_toFinset.mp hv, fun v hv => ⟨ v, h_finite.mem_toFinset.mpr hv, 1, by simp +decide ⟩ ⟩;
  obtain ⟨s, hs⟩ := h_finite
  use s.card + 1;
  obtain ⟨f, hf⟩ : ∃ f : Fin s.card ≃ s, True := by
    exact ⟨ Fintype.equivOfCardEq ( by simp +decide ), trivial ⟩;
  refine' ⟨ fun v => if hv : v = 0 then Fin.last _ else Fin.castSucc ( f.symm ⟨ Classical.choose ( hs.2 v hv ), Classical.choose_spec ( hs.2 v hv ) |>.1 ⟩ ), _, _ ⟩ <;> simp +decide [ IsScalarInvariant, IsProjectiveColoring ];
  · intro a v ha hv; simp +decide [ ha, hv ] ;
    congr! 1;
    ext x; simp +decide ;
    exact fun hx => ⟨ fun ⟨ b, hb ⟩ => ⟨ b / a, by rw [ div_eq_inv_mul, MulAction.mul_smul, ← hb, smul_smul, inv_mul_cancel₀ ha, one_smul ] ⟩, fun ⟨ b, hb ⟩ => ⟨ a * b, by rw [ mul_smul, hb ] ⟩ ⟩;
  · intro v w hv hw h; have := Classical.choose_spec ( hs.2 v hv ) ; have := Classical.choose_spec ( hs.2 w hw ) ; simp_all +decide [ Fin.ext_iff ] ;
    obtain ⟨a, ha⟩ := this.right
    obtain ⟨b, hb⟩ := ‹Classical.choose ( hs.2 v hv ) ∈ s ∧ ∃ a : K, v = a • Classical.choose ( hs.2 v hv ) ›.right
    have h_eq : Classical.choose ( hs.2 v hv ) = Classical.choose ( hs.2 w hw ) := by
      exact Subtype.ext_iff.mp ( f.symm.injective ( Fin.ext h ) );
    exact ⟨ b / a, by rw [ hb, ha, h_eq, smul_smul, div_mul_cancel₀ _ ( by intro h; simp_all +singlePass ) ] ⟩

theorem chi_subadditive (K : Type*) [Field K] [Finite K] (n d t : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n - 1) (ht : 2 ≤ t) :
    chi K n t ≤ chi K (n - d) t + chi K d t := by
      -- By definition of chi, we know that there exist colorings cA and cB for n-d and d dimensions respectively.
      obtain ⟨cA, hcA⟩ : ∃ cA : (Fin (n - d) → K) → Fin (chi K (n - d) t), IsValidColoring K (n - d) t cA := by
        have h_inf : ∃ k, ∃ c : (Fin (n - d) → K) → Fin k, IsValidColoring K (n - d) t c := by
          obtain ⟨ k, c, hc ⟩ := exists_projective_coloring K ( n - d );
          exact ⟨ k, c, is_valid_of_projective K ( n - d ) t k ht c hc.1 hc.2 ⟩;
        exact Nat.sInf_mem h_inf |> fun ⟨ c, hc ⟩ => ⟨ c, hc ⟩
      obtain ⟨cB, hcB⟩ : ∃ cB : (Fin d → K) → Fin (chi K d t), IsValidColoring K d t cB := by
        have := Nat.sInf_mem ( show { k | ∃ c : ( Fin d → K ) → Fin k, IsValidColoring K d t c }.Nonempty from ?_ );
        · exact this;
        · obtain ⟨ k, c, hc ⟩ := exists_projective_coloring K d;
          exact ⟨ k, ⟨ c, is_valid_of_projective K d t k ht c hc.1 hc.2 ⟩ ⟩;
      refine' Nat.sInf_le ⟨ combine_colorings K ( show d ≤ n by omega ) cA cB, _, _ ⟩;
      · exact combine_colorings_is_scalar_invariant K ( show d ≤ n by omega ) cA cB hcA.1 hcB.1;
      · intro S hS h_mono
        obtain ⟨i, hi⟩ := h_mono
        by_cases hiA : i.val < chi K (n - d) t;
        · have hS_le_ker_proj_B : S ≤ LinearMap.ker (proj_B K n d (by omega)) := by
            apply combine_colorings_monochromatic_A_implies_le_ker_proj_B K ( show d ≤ n by omega ) cA cB S i hiA hi;
          have hS_map_proj_A : Module.finrank K (S.map (proj_A K n d (by omega))) = t := by
            rw [ finrank_map_proj_A_eq_of_le_ker_proj_B K n d ( by omega ) S hS_le_ker_proj_B, hS ];
          have hS_map_proj_A_monochromatic : IsMonochromatic K cA (S.map (proj_A K n d (by omega))) := by
            -- Since $S \leq \ker(\text{proj}_B)$, for any $v \in S$, we have $\text{proj}_B(v) = 0$. Therefore, $\text{combine\_colorings}(v) = \text{cA}(\text{proj}_A(v))$.
            have h_combine_eq_cA : ∀ v ∈ S, combine_colorings K (by omega) cA cB v = Fin.castAdd (chi K d t) (cA (proj_A K n d (by omega) v)) := by
              intro v hv; specialize hS_le_ker_proj_B hv; simp_all +decide [ combine_colorings ] ;
            use ⟨ i.val, hiA ⟩;
            rintro _ ⟨ v, hv, rfl ⟩ hv';
            specialize hi v hv (by
            exact fun h => hv' <| by simp +decide [ h ] ;);
            simp_all +decide [ Fin.ext_iff ];
          exact hcA.2 _ hS_map_proj_A hS_map_proj_A_monochromatic;
        · -- Since $i$ is in the second part of the combined coloring, the projection of $S$ onto the last $d$ coordinates must be a $t$-dimensional subspace of $Fin d → K$.
          have h_proj_B : Module.finrank K (S.map (proj_B K n d (by omega))) = t := by
            rw [ finrank_map_proj_B_eq_of_inf_ker_eq_bot ];
            · exact hS;
            · apply combine_colorings_monochromatic_B_implies_inf_ker_proj_B_eq_bot K ( show d ≤ n by omega ) cA cB S i ( by simpa using hiA ) hi;
          -- Since $cB$ is a valid coloring for $d$ dimensions, the projection of $S$ onto the last $d$ coordinates cannot be monochromatic.
          have h_proj_B_not_monochromatic : ¬IsMonochromatic K cB (S.map (proj_B K n d (by omega))) := by
            exact hcB.2 _ h_proj_B;
          refine' h_proj_B_not_monochromatic ⟨ ⟨ i.val - chi K ( n - d ) t, _ ⟩, _ ⟩ <;> simp_all +decide [ Fin.ext_iff ];
          · rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt i ];
          · intro v hv hv'; specialize hi v hv; simp_all +decide [ combine_colorings ] ;
            rw [ ← hi ( by aesop ), Fin.natAdd ] ; simp +decide;

#check chi_subadditive
#print axioms chi_subadditive


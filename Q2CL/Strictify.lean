import Q2CL.Defs
import Q2CL.ChainOfStates

namespace Q2CL

open K4
open Filter Topology Real

private lemma ev_pos_of_deriv (f : ℝ → ℝ) (d : ℝ) (h : HasDerivAt f d 0) (h0 : f 0 = 0)
    (hd : 0 < d) : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < f τ := by
  have ht := (hasDerivAt_iff_tendsto_slope.1 h).mono_left
    (nhdsWithin_mono _ (fun x (hx : (0:ℝ) < x) => ne_of_gt hx))
  filter_upwards [ht.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with τ h1 h2
  simp only [slope, h0, sub_zero, vsub_eq_sub, smul_eq_mul] at h1
  have h2' : (0:ℝ) < τ := h2
  have := mul_pos h1 h2'
  rwa [inv_mul_eq_div, div_mul_cancel₀ _ h2'.ne'] at this

private lemma hasDeriv_phi (u s v a b c p0 p1 p2 p3 : ℝ) :
    HasDerivAt (fun τ : ℝ => -(u * exp (τ * a)) * p0 - s * exp (τ * b) * p1 + p2
      + v * exp (τ * c) * p3) (-(u * a) * p0 - s * b * p1 + v * c * p3) 0 := by
  have e : ∀ k : ℝ, HasDerivAt (fun τ : ℝ => exp (τ * k)) k 0 := by
    intro k
    have := ((hasDerivAt_id (0:ℝ)).mul_const k).exp
    simpa using this
  have := (((((e a).const_mul u).neg.mul_const p0).sub
    (((e b).const_mul s).mul_const p1)).add_const p2).add (((e c).const_mul v).mul_const p3)
  convert this using 1

private lemma ev_phi_pos (u s v a b c p0 p1 p2 p3 : ℝ)
    (h : 0 < -u * p0 - s * p1 + p2 + v * p3 ∨
      (-u * p0 - s * p1 + p2 + v * p3 = 0 ∧ 0 < -(u * a) * p0 - s * b * p1 + v * c * p3)) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ),
      0 < -(u * exp (τ * a)) * p0 - s * exp (τ * b) * p1 + p2 + v * exp (τ * c) * p3 := by
  rcases h with h | ⟨h0, hd⟩
  · have hc : ContinuousAt (fun τ : ℝ => -(u * exp (τ * a)) * p0 - s * exp (τ * b) * p1 + p2
        + v * exp (τ * c) * p3) 0 := by fun_prop
    have := continuousAt_const.eventually_lt hc (by simpa using h)
    exact nhdsWithin_le_nhds this
  · refine ev_pos_of_deriv _ _ (hasDeriv_phi u s v a b c p0 p1 p2 p3) ?_ hd
    simp only [zero_mul, exp_zero, mul_one]
    linarith

private lemma ev_le_exp (A B α β : ℝ) (h : A < B ∨ (A = B ∧ 0 ≤ B ∧ α ≤ β)) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ), A * exp (τ * α) ≤ B * exp (τ * β) := by
  rcases h with h | ⟨rfl, hB, hab⟩
  · have hc1 : ContinuousAt (fun τ : ℝ => A * exp (τ * α)) 0 := by fun_prop
    have hc2 : ContinuousAt (fun τ : ℝ => B * exp (τ * β)) 0 := by fun_prop
    have := hc1.eventually_lt hc2 (by simpa using h)
    exact nhdsWithin_le_nhds (this.mono fun _ h => h.le)
  · filter_upwards [self_mem_nhdsWithin] with τ (hτ : (0:ℝ) < τ)
    apply mul_le_mul_of_nonneg_left _ hB
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hab hτ.le)

private lemma ev_lt_exp (A B α β : ℝ) (h : A < B) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ), A * exp (τ * α) < B * exp (τ * β) := by
  have hc1 : ContinuousAt (fun τ : ℝ => A * exp (τ * α)) 0 := by fun_prop
  have hc2 : ContinuousAt (fun τ : ℝ => B * exp (τ * β)) 0 := by fun_prop
  exact nhdsWithin_le_nhds (hc1.eventually_lt hc2 (by simpa using h))

/-- Strictification by the log-linear perturbation `U i * exp (τ * a i)`,
`S i * exp (τ * b i)`, `V i * exp (τ * c i)`, `τ → 0⁺`: a weak state chain whose equality
relations have the right first-order sign along a direction `(a, b, c)` that respects every
active nesting constraint yields a chain. -/
theorem strictify (n : ℕ) (p : ℕ → Lot 4) (U S V a b c : ℕ → ℝ)
    (hpos : ∀ i, i + 1 < n → 0 < S i ∧ S i < U i ∧ 1 < V i)
    (hnest : ∀ i, i + 2 < n →
      (U (i + 1) < U i ∨ (U (i + 1) = U i ∧ a (i + 1) ≤ a i)) ∧
      (S (i + 1) < S i ∨ (S (i + 1) = S i ∧ b (i + 1) ≤ b i)) ∧
      (U (i + 1) * V i < V (i + 1) * U i ∨
        (U (i + 1) * V i = V (i + 1) * U i ∧ a (i + 1) - a i ≤ c (i + 1) - c i)) ∧
      (S (i + 1) * V i < V (i + 1) * S i ∨
        (S (i + 1) * V i = V (i + 1) * S i ∧ b (i + 1) - b i ≤ c (i + 1) - c i)))
    (hrel : ∀ i, i + 1 < n →
      (0 < fval (U i) (S i) (V i) (p i) ∨
        (fval (U i) (S i) (V i) (p i) = 0 ∧
          0 < -(U i * a i) * p i 0 - S i * b i * p i 1 + V i * c i * p i 3)) ∧
      (fval (U i) (S i) (V i) (p (i + 1)) < 0 ∨
        (fval (U i) (S i) (V i) (p (i + 1)) = 0 ∧
          -(U i * a i) * p (i + 1) 0 - S i * b i * p (i + 1) 1 +
            V i * c i * p (i + 1) 3 < 0))) :
    ∃ W, IsChainFn n p W := by
  let Ut : ℝ → ℕ → ℝ := fun τ i => U i * exp (τ * a i)
  let St : ℝ → ℕ → ℝ := fun τ i => S i * exp (τ * b i)
  let Vt : ℝ → ℕ → ℝ := fun τ i => V i * exp (τ * c i)
  let P : ℕ → ℝ → Prop := fun i τ =>
    (i + 1 < n → (0 < St τ i ∧ St τ i < Ut τ i ∧ 1 < Vt τ i) ∧
      (0 < fval (Ut τ i) (St τ i) (Vt τ i) (p i) ∧
        fval (Ut τ i) (St τ i) (Vt τ i) (p (i + 1)) < 0)) ∧
    (i + 2 < n → Ut τ (i + 1) ≤ Ut τ i ∧ St τ (i + 1) ≤ St τ i ∧
      Ut τ (i + 1) * Vt τ i ≤ Vt τ (i + 1) * Ut τ i ∧
      St τ (i + 1) * Vt τ i ≤ Vt τ (i + 1) * St τ i)
  have hev : ∀ i ∈ Finset.range n, ∀ᶠ τ in 𝓝[>] (0:ℝ), P i τ := by
    intro i _
    have hA : ∀ᶠ τ in 𝓝[>] (0:ℝ), i + 1 < n → (0 < St τ i ∧ St τ i < Ut τ i ∧ 1 < Vt τ i) ∧
        (0 < fval (Ut τ i) (St τ i) (Vt τ i) (p i) ∧
          fval (Ut τ i) (St τ i) (Vt τ i) (p (i + 1)) < 0) := by
      by_cases hi : i + 1 < n
      · obtain ⟨hS, hSU, hV⟩ := hpos i hi
        obtain ⟨r1, r2⟩ := hrel i hi
        have e1 := ev_lt_exp (S i) (U i) (b i) (a i) hSU
        have e2 := ev_lt_exp 1 (V i) 0 (c i) hV
        have e3 := ev_phi_pos (U i) (S i) (V i) (a i) (b i) (c i)
          (p i 0) (p i 1) (p i 2) (p i 3) (by simpa [fval] using r1)
        have e4 := ev_phi_pos (U i) (S i) (V i) (a i) (b i) (c i)
          (-p (i + 1) 0) (-p (i + 1) 1) (-p (i + 1) 2) (-p (i + 1) 3) (by
            simp only [fval] at r2
            rcases r2 with r2 | ⟨r2, r3⟩
            · left; linarith
            · right; constructor <;> linarith)
        filter_upwards [e1, e2, e3, e4] with τ h1 h2 h3 h4 _
        refine ⟨⟨mul_pos hS (exp_pos _), h1, by simpa using h2⟩, ?_, ?_⟩
        · simp only [fval, Ut, St, Vt]; linarith
        · simp only [fval, Ut, St, Vt]; linarith
      · exact Eventually.of_forall fun _ h => absurd h hi
    have hB : ∀ᶠ τ in 𝓝[>] (0:ℝ), i + 2 < n → Ut τ (i + 1) ≤ Ut τ i ∧ St τ (i + 1) ≤ St τ i ∧
        Ut τ (i + 1) * Vt τ i ≤ Vt τ (i + 1) * Ut τ i ∧
        St τ (i + 1) * Vt τ i ≤ Vt τ (i + 1) * St τ i := by
      by_cases hi : i + 2 < n
      · obtain ⟨hS, hSU, hV⟩ := hpos i (by omega)
        obtain ⟨hS', hSU', hV'⟩ := hpos (i + 1) (by omega)
        obtain ⟨n1, n2, n3, n4⟩ := hnest i hi
        have e1 := ev_le_exp (U (i + 1)) (U i) (a (i + 1)) (a i) (by
          rcases n1 with h | ⟨h, h'⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, by linarith, h'⟩)
        have e2 := ev_le_exp (S (i + 1)) (S i) (b (i + 1)) (b i) (by
          rcases n2 with h | ⟨h, h'⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, by linarith, h'⟩)
        have e3 := ev_le_exp (U (i + 1) * V i) (V (i + 1) * U i) (a (i + 1) + c i)
          (c (i + 1) + a i) (by
          rcases n3 with h | ⟨h, h'⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, by nlinarith, by linarith⟩)
        have e4 := ev_le_exp (S (i + 1) * V i) (V (i + 1) * S i) (b (i + 1) + c i)
          (c (i + 1) + b i) (by
          rcases n4 with h | ⟨h, h'⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, by nlinarith, by linarith⟩)
        filter_upwards [e1, e2, e3, e4] with τ h1 h2 h3 h4 _
        refine ⟨h1, h2, ?_, ?_⟩
        · simp only [Ut, Vt]
          calc U (i + 1) * exp (τ * a (i + 1)) * (V i * exp (τ * c i))
              = U (i + 1) * V i * exp (τ * (a (i + 1) + c i)) := by
                rw [mul_add, exp_add]; ring
            _ ≤ V (i + 1) * U i * exp (τ * (c (i + 1) + a i)) := h3
            _ = _ := by rw [mul_add, exp_add]; ring
        · simp only [St, Vt]
          calc S (i + 1) * exp (τ * b (i + 1)) * (V i * exp (τ * c i))
              = S (i + 1) * V i * exp (τ * (b (i + 1) + c i)) := by
                rw [mul_add, exp_add]; ring
            _ ≤ V (i + 1) * S i * exp (τ * (c (i + 1) + b i)) := h4
            _ = _ := by rw [mul_add, exp_add]; ring
      · exact Eventually.of_forall fun _ h => absurd h hi
    filter_upwards [hA, hB] with τ h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨τ, hτ⟩ := ((Finset.eventually_all (Finset.range n)).2 hev).exists
  refine chainFn_of_states n p (Ut τ) (St τ) (Vt τ) (fun i hi => ?_) (fun i hi => ?_)
    (fun i hi => ?_)
  · exact ((hτ i (Finset.mem_range.2 (by omega))).1 hi).1
  · exact (hτ i (Finset.mem_range.2 (by omega))).2 hi
  · exact ((hτ i (Finset.mem_range.2 (by omega))).1 hi).2

end Q2CL

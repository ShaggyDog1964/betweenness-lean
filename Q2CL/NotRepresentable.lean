import Q2CL.Defs
import Q2CL.ChainOfRepresentable
import Q2CL.ChainNormal
import Q2CL.GadgetOmegaStep
import Q2CL.TransferMap
import Q2CL.TMemSimplex
import Q2CL.WCons
import Q2CL.CwBound
import Q2CL.JSpec
import Q2CL.WEnvelope

namespace Q2CL

open K4

/-- Proposition 71 (non-representability): `T(m, ns, ds)` is not representable. -/
theorem T_not_representable {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ¬ Representable (Tlist m ns ds) := by
  intro hRep
  obtain ⟨W, hW⟩ := chain_of_representable (4 * Jn m ns + 2) (Tpt m ns ds)
    (T_mem_simplex hA) hRep
  obtain ⟨hNorm, hMono, hFirst, hLast⟩ := chain_normal hA W hW
  have hmono : ∀ d i, 1 ≤ i → i + d ≤ 4 * Jn m ns →
      W i 3 / -W i 1 ≤ W (i + d) 3 / -W (i + d) 1 := by
    intro d
    induction d with
    | zero => intro i _ _; simp
    | succ d ih =>
      intro i hi hid
      have h1 := ih i hi (by omega)
      have h2 := (hMono (i + d) (by omega) (by omega)).1
      have e : i + (d + 1) = i + d + 1 := by omega
      rw [e]; exact le_trans h1 h2
  have ho1 : o1 m ns ≤ 25 / 4 := (w_cons hA).1
  -- one gadget step
  have hstep : ∀ j, j < Jn m ns → wA m ns j < W (4 * j + 1) 3 / -W (4 * j + 1) 1 →
      wB m ns j < W (4 * j + 3) 3 / -W (4 * j + 3) 1 := by
    intro j hj hIH
    obtain ⟨hs0, hs1, hcwA, -, -, -, -⟩ := cw_bound hA j hj
    obtain ⟨hSM, hTA⟩ := transfer_map hA j hj
    have hwA0 : o0 ≤ wA m ns j := ((w_envelope hA).1 j hj.le).1
    have ho0 : (0 : ℝ) < o0 := by unfold o0; norm_num
    have hc0 : 0 ≤ cOf (sig ns ds j) := by
      unfold cOf; apply div_nonneg hs0; linarith
    have hc1 : cOf (sig ns ds j) ≤ 1 / 11 := by
      unfold cOf
      rw [div_le_iff₀ (by linarith)]; linarith
    have hωle : W (4 * j + 1) 3 / -W (4 * j + 1) 1 ≤
        W (4 * Jn m ns) 3 / -W (4 * Jn m ns) 1 := by
      have := hmono (4 * Jn m ns - (4 * j + 1)) (4 * j + 1) (by omega) (by omega)
      have e : 4 * j + 1 + (4 * Jn m ns - (4 * j + 1)) = 4 * Jn m ns := by omega
      rw [e] at this; exact this
    have hωpos : 0 < W (4 * j + 1) 3 / -W (4 * j + 1) 1 := by linarith
    have hω6 : W (4 * j + 1) 3 / -W (4 * j + 1) 1 < 25 / 4 := by linarith
    have hcω : cOf (sig ns ds j) * (W (4 * j + 1) 3 / -W (4 * j + 1) 1) < 1 := by
      nlinarith
    have hlt := hSM ⟨by linarith, by linarith⟩ ⟨hωpos, hcω⟩ hIH
    rw [hTA] at hlt
    exact lt_trans hlt (gadget_omega_step hA W hW j hj)
  have hBA : ∀ j, wB m ns j = wA m ns (j + 1) := by
    intro j; unfold wB wA; rw [Finset.prod_range_succ, mul_assoc]
  have hJ2 : 2 ≤ Jn m ns := (J_spec hA).2.2.1
  have hclaim : ∀ j, j < Jn m ns → wA m ns j < W (4 * j + 1) 3 / -W (4 * j + 1) 1 := by
    intro j
    induction j with
    | zero =>
      intro _
      have e : wA m ns 0 = o0 := by unfold wA; simp
      rw [e]; simpa using hFirst
    | succ j ih =>
      intro hj
      have h3 := hstep j (by omega) (ih (by omega))
      have h4 := (hMono (4 * j + 3) (by omega) (by omega)).1
      have h5 := (hMono (4 * j + 3 + 1) (by omega) (by omega)).1
      rw [← hBA]
      have e : 4 * (j + 1) + 1 = 4 * j + 3 + 1 + 1 := by omega
      rw [e]
      exact lt_of_lt_of_le h3 (le_trans h4 h5)
  have h3 := hstep (Jn m ns - 1) (by omega) (hclaim (Jn m ns - 1) (by omega))
  have h4 := (hMono (4 * (Jn m ns - 1) + 3) (by omega) (by omega)).1
  have e1 : 4 * (Jn m ns - 1) + 3 + 1 = 4 * Jn m ns := by omega
  rw [e1] at h4
  have e2 : wB m ns (Jn m ns - 1) = o1 m ns := by
    rw [hBA]; unfold o1; congr 1; omega
  rw [e2] at h3
  linarith

end Q2CL

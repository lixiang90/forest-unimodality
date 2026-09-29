import ForestUnimodality.FlowVarianceSources
import ForestUnimodality.ExpEnclosure

namespace ForestUnimodality.FlowVarianceSources

def Source.BasicAccepts (s : Source) (b expHi : ℚ) : Prop :=
  match s with
  | .uniform i => b≤(NonnegativeSourceLibrary.parameters i).b
  | .support i => b≤(AffineSourceLibrary.domain i).b
  | .tilted i => b≤(TiltedSourceLibrary.domain0 i).b ∧ b*expHi≤(TiltedSourceLibrary.domain1 i).b
  | .marked _ => False

instance (s : Source) (b expHi : ℚ) : Decidable (s.BasicAccepts b expHi) := by
  cases s <;> unfold Source.BasicAccepts <;> infer_instance

def Source.basicCheck (s : Source) (b expHi : ℚ) : Bool := decide (s.BasicAccepts b expHi)

theorem Source.basic_sound {s : Source} {b expHi : ℚ} {start a finish : ℝ}
    (hc : s.basicCheck b expHi=true) (hb : (0:ℝ)≤b)
    (he : Real.exp (-start)≤(expHi:ℝ)) :
    s.needsMean=false ∧ s.Covers a b start finish := by
  have h : s.BasicAccepts b expHi := of_decide_eq_true hc
  cases s with
  | uniform i =>
    refine ⟨rfl,?_⟩
    change b≤(NonnegativeSourceLibrary.parameters i).b at h
    change (b:ℝ)≤((NonnegativeSourceLibrary.parameters i).b:ℝ)
    exact_mod_cast h
  | support i =>
    refine ⟨rfl,?_⟩
    change b≤(AffineSourceLibrary.domain i).b at h
    change (b:ℝ)≤((AffineSourceLibrary.domain i).b:ℝ)
    exact_mod_cast h
  | tilted i =>
    refine ⟨rfl,by exact_mod_cast h.1,?_⟩
    exact (mul_le_mul_of_nonneg_left he hb).trans (by exact_mod_cast h.2)
  | marked i => exact h.elim

#print axioms Source.basic_sound
end ForestUnimodality.FlowVarianceSources

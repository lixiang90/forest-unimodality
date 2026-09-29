import ForestUnimodality.BernsteinCertificate

/-! A recursive exact rectangle cover. Each internal node splits one full
rectangle into two closed halves; a successful tree cannot omit a region. -/
namespace ForestUnimodality.BernsteinCertificate

inductive Cover where
  | leaf (certificate : Certificate₂)
  | splitX (left right : Cover)
  | splitY (left right : Cover)

def Cover.check (p : BiPolynomial) (lx hx ly hy : ℚ) : Cover → Bool
  | .leaf c => boxCheck p lx hx ly hy c
  | .splitX l r => l.check p lx ((lx + hx) / 2) ly hy &&
      r.check p ((lx + hx) / 2) hx ly hy
  | .splitY l r => l.check p lx hx ly ((ly + hy) / 2) &&
      r.check p lx hx ((ly + hy) / 2) hy

theorem Cover.check_sound (tree : Cover) {p : BiPolynomial} {lx hx ly hy : ℚ}
    (hc : tree.check p lx hx ly hy = true) {x y : ℝ}
    (hxx : x ∈ Set.Icc (lx : ℝ) (hx : ℝ))
    (hyy : y ∈ Set.Icc (ly : ℝ) (hy : ℝ)) : 0 ≤ evalReal₂ p x y := by
  induction tree generalizing lx hx ly hy with
  | leaf c => exact boxCheck_sound hc hxx hyy
  | splitX l r ihl ihr =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hc
    by_cases hm : x ≤ (((lx + hx) / 2 : ℚ) : ℝ)
    · exact ihl hl ⟨hxx.1, hm⟩ hyy
    · exact ihr hr ⟨(lt_of_not_ge hm).le, hxx.2⟩ hyy
  | splitY l r ihl ihr =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hc
    by_cases hm : y ≤ (((ly + hy) / 2 : ℚ) : ℝ)
    · exact ihl hl hxx ⟨hyy.1, hm⟩
    · exact ihr hr hxx ⟨(lt_of_not_ge hm).le, hyy.2⟩

#print axioms Cover.check_sound
end ForestUnimodality.BernsteinCertificate

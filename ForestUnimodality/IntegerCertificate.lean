import ForestUnimodality.RowSemantics
import ForestUnimodality.LinearCertificate
import ForestUnimodality.FiniteAssembly

/-!
Executable integer witnesses for all finite LP certificate kinds. Exported
scales and multipliers are untrusted data: acceptance recomputes every raw row
coefficient, residual inequality, and the final signed integer bound.
-/

namespace ForestUnimodality
namespace FiniteRows

open Finset

structure WeightedRow where
  row : Row
  weight : ℕ
  deriving Repr

structure Certificate where
  objectiveScale : ℕ
  eta : ℤ
  rows : Array WeightedRow
  caps : Array ℤ
  deriving Repr

/-- Caps are indexed by the actual layer j; index zero is unused. -/
def Certificate.cap (cert : Certificate) (j : ℕ) : ℤ := cert.caps.getD j 0

def Certificate.residual (cert : Certificate) (n a k : ℕ) (kind : Kind)
    (jm : ℕ × ℕ) : ℤ :=
  (cert.objectiveScale : ℤ) * targetCoeff k kind jm - cert.eta * indicator jm.1 1 -
    ∑ i : Fin cert.rows.size, (cert.rows[i].weight : ℤ) * coeff n a cert.rows[i].row jm

def Certificate.bound (cert : Certificate) (n a k : ℕ) (kind : Kind) : ℤ :=
  (cert.objectiveScale : ℤ) * targetConstant a k kind + cert.eta * (n - a : ℕ) +
    (∑ i : Fin cert.rows.size, (cert.rows[i].weight : ℤ) * rhs n a cert.rows[i].row) +
    ∑ j ∈ Icc 1 (n - a), ((n - a).choose j : ℤ) * cert.cap j

def Certificate.Accepts (cert : Certificate) (n a k : ℕ) (kind : Kind) : Prop :=
  0 < cert.objectiveScale ∧
  cert.caps.size = n - a + 1 ∧
  (∀ i : Fin cert.rows.size, Valid n a k kind cert.rows[i].row) ∧
  (∀ j ∈ Icc 1 (n - a), 0 ≤ cert.cap j) ∧
  (∀ jm ∈ triangularIndices a (n - a), cert.residual n a k kind jm ≤ cert.cap jm.1) ∧
  (if kind = .positive then cert.bound n a k kind < 0 else cert.bound n a k kind ≤ 0)

instance (cert : Certificate) (n a k : ℕ) (kind : Kind) :
    Decidable (cert.Accepts n a k kind) := by
  unfold Certificate.Accepts
  infer_instance

def Certificate.check (cert : Certificate) (n a k : ℕ) (kind : Kind) : Bool :=
  decide (cert.Accepts n a k kind)

@[simp] theorem Certificate.check_eq_true_iff (cert : Certificate) (n a k : ℕ) (kind : Kind) :
    cert.check n a k kind = true ↔ cert.Accepts n a k kind := by
  simp [Certificate.check]

theorem Certificate.row_valid_of_check (cert : Certificate) (n a k : ℕ) (kind : Kind)
    (hcheck : cert.check n a k kind = true) (i : Fin cert.rows.size) :
    Valid n a k kind cert.rows[i].row :=
  ((cert.check_eq_true_iff n a k kind).mp hcheck).2.2.1 i

/-- Generic real target on the exact computable triangular support. -/
noncomputable def targetValue (a v k : ℕ) (kind : Kind) (x : ℕ × ℕ → ℝ) : ℝ :=
  (targetConstant a k kind : ℝ) +
    ∑ jm ∈ triangularIndices a v, (targetCoeff k kind jm : ℝ) * x jm

/-- Integer residual checks bound the scaled real affine target. Row validity
is a syntactic check; the mathematical row inequalities are explicit inputs. -/
theorem Certificate.scaled_target_le_bound
    (cert : Certificate) (n a k : ℕ) (kind : Kind)
    (hcheck : cert.check n a k kind = true) (x : ℕ × ℕ → ℝ)
    (hx : ∀ jm ∈ triangularIndices a (n - a), 0 ≤ x jm)
    (hfirst : (∑ jm ∈ (triangularIndices a (n - a)).filter (fun jm => jm.1 = 1), x jm) =
      (n - a : ℕ))
    (hmass : ∀ j ∈ Icc 1 (n - a),
      (∑ jm ∈ (triangularIndices a (n - a)).filter (fun jm => jm.1 = j), x jm) ≤
        ((n - a).choose j : ℝ))
    (hrows : ∀ i : Fin cert.rows.size,
      (∑ jm ∈ triangularIndices a (n - a),
        (coeff n a cert.rows[i].row jm : ℝ) * x jm) ≤ (rhs n a cert.rows[i].row : ℝ)) :
    (cert.objectiveScale : ℝ) * targetValue a (n - a) k kind x ≤
      (cert.bound n a k kind : ℝ) := by
  have hcert := (cert.check_eq_true_iff n a k kind).mp hcheck
  have hcap := hcert.2.2.2.1
  have hres := hcert.2.2.2.2.1
  have hcover : ∀ jm ∈ triangularIndices a (n - a), jm.1 ∈ Icc 1 (n - a) := by
    intro jm hjm
    obtain ⟨hj, hjv, _⟩ := mem_triangularIndices.mp hjm
    exact mem_Icc.mpr ⟨hj, hjv⟩
  have hresidual := LinearCertificate.residual_upper_by_layers
    (triangularIndices a (n - a)) (Icc 1 (n - a)) Prod.fst
    (fun jm => (cert.residual n a k kind jm : ℝ)) x
    (fun j => (cert.cap j : ℝ)) (fun j => ((n - a).choose j : ℝ))
    hcover hx (fun j hj => by exact_mod_cast hcap j hj)
    (fun jm hjm => by exact_mod_cast hres jm hjm) hmass
  have hequality : LinearCertificate.linear (triangularIndices a (n - a))
      (fun jm => (indicator jm.1 1 : ℝ)) x = (n - a : ℕ) := by
    simpa [LinearCertificate.linear, indicator, Finset.sum_filter] using hfirst
  have hdual := LinearCertificate.affine_upper_of_residual_bound
    (triangularIndices a (n - a)) (univ : Finset (Fin cert.rows.size))
    (fun i jm => (coeff n a cert.rows[i].row jm : ℝ))
    (fun i => (rhs n a cert.rows[i].row : ℝ))
    (fun i => (cert.rows[i].weight : ℝ))
    (fun jm => (cert.objectiveScale : ℝ) * (targetCoeff k kind jm : ℝ))
    (fun jm => (indicator jm.1 1 : ℝ))
    (fun jm => (cert.residual n a k kind jm : ℝ)) x
    ((cert.objectiveScale : ℝ) * (targetConstant a k kind : ℝ))
    (cert.eta : ℝ) (n - a : ℕ)
    (∑ j ∈ Icc 1 (n - a), (cert.cap j : ℝ) * ((n - a).choose j : ℝ))
    hx (fun i _ => Nat.cast_nonneg _) (fun i _ => hrows i) hequality
    (by
      intro jm hjm
      simp only [Certificate.residual, Int.cast_sub, Int.cast_mul, Int.cast_sum,
        Int.cast_natCast]
      linarith)
    hresidual
  simpa [targetValue, LinearCertificate.linear, Certificate.bound, mul_add,
    mul_sum, mul_assoc, mul_comm, mul_left_comm] using hdual

/-- The sign of the unscaled target follows from positivity of its integer
scale. This includes conditional kinds only when their row assumptions hold. -/
theorem Certificate.target_sign
    (cert : Certificate) (n a k : ℕ) (kind : Kind)
    (hcheck : cert.check n a k kind = true) (x : ℕ × ℕ → ℝ)
    (hx : ∀ jm ∈ triangularIndices a (n - a), 0 ≤ x jm)
    (hfirst : (∑ jm ∈ (triangularIndices a (n - a)).filter (fun jm => jm.1 = 1), x jm) =
      (n - a : ℕ))
    (hmass : ∀ j ∈ Icc 1 (n - a),
      (∑ jm ∈ (triangularIndices a (n - a)).filter (fun jm => jm.1 = j), x jm) ≤
        ((n - a).choose j : ℝ))
    (hrows : ∀ i : Fin cert.rows.size,
      (∑ jm ∈ triangularIndices a (n - a),
        (coeff n a cert.rows[i].row jm : ℝ) * x jm) ≤ (rhs n a cert.rows[i].row : ℝ)) :
    if kind = .positive then targetValue a (n - a) k kind x < 0
      else targetValue a (n - a) k kind x ≤ 0 := by
  have hcert := (cert.check_eq_true_iff n a k kind).mp hcheck
  have hscale : (0 : ℝ) < cert.objectiveScale := by exact_mod_cast hcert.1
  have hbound := cert.scaled_target_le_bound n a k kind hcheck x hx hfirst hmass hrows
  have hsign := hcert.2.2.2.2.2
  split_ifs with hkind
  · rw [if_pos hkind] at hsign
    have hb : (cert.bound n a k kind : ℝ) < 0 := by exact_mod_cast hsign
    nlinarith
  · rw [if_neg hkind] at hsign
    have hb : (cert.bound n a k kind : ℝ) ≤ 0 := by exact_mod_cast hsign
    nlinarith

theorem differenceCoeff_cast_eq (m j r : ℕ) (hr : 1 ≤ r) :
    (differenceCoeff m j r : ℝ) =
      (shiftedChoose m j r : ℝ) - (shiftedChoose m j (r - 1) : ℝ) := by
  cases r with
  | zero => omega
  | succ r => simp [differenceCoeff]

variable {V : Type*} [DecidableEq V]

/-- The generic target is the intended signed adjacent coefficient difference
when evaluated at genuine graph layers. -/
theorem targetValue_layers_eq_delta
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (k : ℕ) (kind : Kind) (hk : 1 ≤ targetIndex k kind) :
    targetValue I.card (S \ I).card k kind
        (fun jm => (layerCount G I (S \ I) jm.1 jm.2 : ℝ)) =
      (targetSign kind : ℝ) * ((countIndependent G S (targetIndex k kind) : ℝ) -
        (countIndependent G S (targetIndex k kind - 1) : ℝ)) := by
  rw [hI.countIndependent_delta_eq_triangular (targetIndex k kind) hk]
  simp only [targetValue, targetConstant, targetCoeff, Int.cast_mul,
    differenceCoeff_cast_eq _ _ _ hk, shiftedChoose_zero_shift]
  simp only [mul_add, mul_sum, mul_assoc, mul_comm]

/-- Apply the integer checker directly to genuine triangular layer counts.
The graph row inequalities are still explicit, ready for the row-soundness
module; neither syntactic Valid nor check=true is taken to prove them. -/
theorem Certificate.target_sign_for_layers
    (cert : Certificate) {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hav : (S \ I).card ≤ I.card)
    (hv : 1 ≤ (S \ I).card) (k : ℕ) (kind : Kind)
    (hcheck : cert.check S.card I.card k kind = true)
    (hrows : ∀ i : Fin cert.rows.size, RowHolds G S I cert.rows[i].row) :
    if kind = .positive then
      targetValue I.card (S \ I).card k kind
        (fun jm => (layerCount G I (S \ I) jm.1 jm.2 : ℝ)) < 0
    else
      targetValue I.card (S \ I).card k kind
        (fun jm => (layerCount G I (S \ I) jm.1 jm.2 : ℝ)) ≤ 0 := by
  have hdiff : S.card - I.card = (S \ I).card := (card_sdiff_of_subset hI.subset).symm
  have h := cert.target_sign S.card I.card k kind hcheck
    (fun jm => (layerCount G I (S \ I) jm.1 jm.2 : ℝ))
  rw [hdiff] at h
  apply h
  · intro jm hjm
    exact Nat.cast_nonneg _
  · exact_mod_cast hI.triangular_first_mass hav hv
  · intro j hj
    obtain ⟨hj1, hjv⟩ := mem_Icc.mp hj
    exact_mod_cast hI.triangular_layer_mass_le hav j hj1 hjv
  · intro i
    exact hrows i

/-- Once row semantics have been supplied, acceptance proves the coefficient
sign corresponding to the selected certificate kind. -/
theorem Certificate.graph_sign
    (cert : Certificate) {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hav : (S \ I).card ≤ I.card)
    (hv : 1 ≤ (S \ I).card) (k : ℕ) (hk : 1 ≤ k) (kind : Kind)
    (hcheck : cert.check S.card I.card k kind = true)
    (hrows : ∀ i : Fin cert.rows.size, RowHolds G S I cert.rows[i].row) :
    if kind = .positive then countIndependent G S (k - 1) < countIndependent G S k
      else countIndependent G S (k + 1) ≤ countIndependent G S k := by
  have hs := cert.target_sign_for_layers hI hav hv k kind hcheck hrows
  have hindex : 1 ≤ targetIndex k kind := by
    cases kind <;> simp [targetIndex] <;> omega
  rw [targetValue_layers_eq_delta hI k kind hindex] at hs
  cases kind with
  | positive =>
    simp only [targetSign, targetIndex, if_pos, Int.cast_neg, Int.cast_one] at hs ⊢
    have hh : (countIndependent G S (k - 1) : ℝ) < countIndependent G S k := by linarith
    exact_mod_cast hh
  | negative =>
    simp [targetSign, targetIndex] at hs ⊢
    exact_mod_cast hs
  | conditional =>
    simp [targetSign, targetIndex] at hs ⊢
    exact_mod_cast hs

/-- A conditional certificate requests its premise only while establishing
the conditional alternative. The premise is never exported as a graph fact. -/
theorem Certificate.graph_alternative
    (cert : Certificate) {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hav : (S \ I).card ≤ I.card)
    (hv : 1 ≤ (S \ I).card) (k : ℕ) (hk : 1 ≤ k) (kind : Kind)
    (hcheck : cert.check S.card I.card k kind = true)
    (hrows : (kind = .conditional → countIndependent G S k ≤ countIndependent G S (k - 1)) →
      ∀ i : Fin cert.rows.size, RowHolds G S I cert.rows[i].row) :
    CertificateAlternative (countIndependent G S) k := by
  cases kind with
  | positive =>
    apply Or.inl
    have hr := hrows (by intro h; cases h)
    simpa using cert.graph_sign hI hav hv k hk .positive hcheck hr
  | negative =>
    apply Or.inr
    apply Or.inl
    have hr := hrows (by intro h; cases h)
    simpa using cert.graph_sign hI hav hv k hk .negative hcheck hr
  | conditional =>
    apply Or.inr
    apply Or.inr
    intro hstep
    have hr := hrows (fun _ => hstep)
    simpa using cert.graph_sign hI hav hv k hk .conditional hcheck hr

#print axioms Certificate.scaled_target_le_bound
#print axioms Certificate.target_sign
#print axioms targetValue_layers_eq_delta
#print axioms Certificate.target_sign_for_layers
#print axioms Certificate.graph_sign
#print axioms Certificate.graph_alternative

end FiniteRows
end ForestUnimodality

import ForestUnimodality.ShortLegFinite

namespace ForestUnimodality.ShortLegData
open Finset

def spiderDenominator (legs : List ℕ) : ℚ :=
  (legs.map fun n => (pathData n).1).prod +
    2 * (legs.map fun n => (pathData n).2.2.1).prod

theorem spiderDenominator_pos (legs : List ℕ) : 0 < spiderDenominator legs := by
  have hp : 0 < (legs.map fun n => (pathData n).1).prod ∧
      0 < (legs.map fun n => (pathData n).2.2.1).prod := by
    induction legs with
    | nil => norm_num
    | cons n ns ih =>
      simpa using And.intro (mul_pos (pathData_positive n).1 ih.1)
        (mul_pos (pathData_positive n).2 ih.2)
  exact add_pos hp.1 (mul_pos (by norm_num) hp.2)

theorem spider_scalar_eq_ratio (legs : List ℕ) :
    spiderPotentialScalar (univ : Finset (Fin legs.length)) (fun i => legs[i]) =
      (spiderNumerator legs : ℝ) / (spiderDenominator legs : ℝ) := by
  have hD : (spiderDenominator legs : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast spiderDenominator_pos legs)
  unfold spiderPotentialScalar
  simp only [← pathData_cast, castState]
  simp only [Fin.getElem_fin]
  rw [Fin.prod_univ_fun_getElem legs (fun n => ((pathData n).1 : ℝ)),
    Fin.prod_univ_fun_getElem legs (fun n => ((pathData n).2.2.1 : ℝ)),
    Fin.sum_univ_fun_getElem legs (fun n => ((pathData n).2.1 : ℝ) / (pathData n).1),
    Fin.sum_univ_fun_getElem legs (fun n => ((pathData n).2.2.2 : ℝ) / (pathData n).2.2.1),
    Fin.sum_univ_fun_getElem legs (fun n => (n + 1) / 2),
    Fin.sum_univ_fun_getElem legs (fun n => n / 2), Fin.sum_univ_getElem]
  unfold spiderNumerator spiderDenominator at hD ⊢
  push_cast at hD ⊢
  simp only [List.map_map, Function.comp_def] at hD ⊢
  push_cast
  field_simp
  ring

/-- Every actual spider with one of the certified length multisets has
strictly positive adjusted mean. The graph witness is essential. -/
theorem spider_base_graph_positive {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {c : V} (legs : List ℕ)
    {B : Fin legs.length → Finset V} {root tip : Fin legs.length → V}
    (h : IsSpiderOn G S c univ B root tip (fun i => legs[i]))
    (hbase : legs ∈ spiderBases) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  rw [h.adjustedMean_eq_scalar, spider_scalar_eq_ratio]
  exact div_pos (by exact_mod_cast spider_base_positive legs hbase)
    (by exact_mod_cast spiderDenominator_pos legs)

theorem spider_base_graph_positive_of_perm {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {c : V} (legs base : List ℕ)
    {B : Fin legs.length → Finset V} {root tip : Fin legs.length → V}
    (h : IsSpiderOn G S c univ B root tip (fun i => legs[i]))
    (hbase : base ∈ spiderBases) (hp : legs.Perm base) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  rw [h.adjustedMean_eq_scalar, spider_scalar_eq_ratio, spiderNumerator_perm hp]
  exact div_pos (by exact_mod_cast spider_base_positive base hbase)
    (by exact_mod_cast spiderDenominator_pos legs)

theorem spider_scalar_eq_ratio_toList {ι : Type*} (s : Finset ι) (length : ι → ℕ) :
    spiderPotentialScalar s length =
      (spiderNumerator (s.toList.map length) : ℝ) /
        (spiderDenominator (s.toList.map length) : ℝ) := by
  rw [← spider_scalar_eq_ratio]
  let legs := s.toList.map length
  have hp (f : ℕ → ℝ) : (∏ i : Fin legs.length, f legs[i]) = ∏ i ∈ s, f (length i) := by
    simpa only [legs, Fin.getElem_fin, List.map_map, Function.comp_def, Finset.prod_map_toList]
      using Fin.prod_univ_fun_getElem legs f
  have hs (f : ℕ → ℝ) : (∑ i : Fin legs.length, f legs[i]) = ∑ i ∈ s, f (length i) := by
    simpa only [legs, Fin.getElem_fin, List.map_map, Function.comp_def, Finset.sum_map_toList]
      using Fin.sum_univ_fun_getElem legs f
  have hn (f : ℕ → ℕ) : (∑ i : Fin legs.length, f legs[i]) = ∑ i ∈ s, f (length i) := by
    simpa only [legs, Fin.getElem_fin, List.map_map, Function.comp_def, Finset.sum_map_toList]
      using Fin.sum_univ_fun_getElem legs f
  unfold spiderPotentialScalar
  dsimp only
  rw [hp (fun n => (pathBranchStatistics n).1), hp (fun n => (pathBranchStatistics n).2.2.1),
    hs (fun n => (pathBranchStatistics n).2.1 / (pathBranchStatistics n).1),
    hs (fun n => (pathBranchStatistics n).2.2.2 / (pathBranchStatistics n).2.2.1),
    hn (fun n => (n + 1) / 2), hn (fun n => n / 2), hn (fun n => n)]

theorem spider_graph_positive_of_numerator {V ι : Type*} [DecidableEq V] [DecidableEq ι]
    {G : SimpleGraph V} {S : Finset V} {c : V} {s : Finset ι}
    {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length)
    (hnum : 0 < spiderNumerator (s.toList.map length)) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  rw [h.adjustedMean_eq_scalar, spider_scalar_eq_ratio_toList]
  exact div_pos (by exact_mod_cast hnum)
    (by exact_mod_cast spiderDenominator_pos (s.toList.map length))

#print axioms spider_scalar_eq_ratio
#print axioms spider_base_graph_positive
end ForestUnimodality.ShortLegData

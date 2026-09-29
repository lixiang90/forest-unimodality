import ForestUnimodality.MessageVarianceSource
import ForestUnimodality.RootedSourceMessages

/-! The sharp additive log bonus is supplied by a real original forest leaf
kept as a source root. The isolated-vertex case is included. -/
namespace ForestUnimodality
open Finset MarginalSelectionBound
variable {V : Type*} [DecidableEq V]

theorem SourceMessages.leaf_log_bonus
    {G : SimpleGraph V} {S : Finset V} {activity b : ℝ} {a : V→ℝ}
    {parent : V→Option V} {p d : V→ℝ}
    (h : SourceMessages G S (fun _=>activity) a parent p d)
    (hactivity : 0<activity) (hhi : activity≤b)
    {root : V} (hr : root∈S) (hdegree : degreeOn G S root≤1) :
    Real.log (1+activity/(1+b))≤-Real.log (1-p root) := by
  classical
  have hb := hactivity.trans_le hhi
  have hb1 : 0<1+b := by linarith
  have hp1 := sub_pos.mpr (h.probability root hr).2
  have hc : (sourceChildren S parent root).card≤1 := by
    apply le_trans (card_le_card (show sourceChildren S parent root⊆S.filter (G.Adj root) from ?_))
      (show (S.filter (G.Adj root)).card≤1 from hdegree)
    intro y hy
    have hh := mem_filter.mp hy
    exact mem_filter.mpr ⟨hh.1,(h.parent_mem y hh.1 root hh.2).2.symm⟩
  have hprod : 1/(1+b)≤sourceChildProduct S parent p root := by
    by_cases he : sourceChildren S parent root=∅
    · simp only [sourceChildProduct,he,prod_empty]
      exact (div_le_one hb1).mpr (by linarith)
    · obtain ⟨y,hy⟩ := nonempty_iff_ne_empty.mpr he
      have hsingle : sourceChildren S parent root={y} := by
        apply eq_singleton_iff_unique_mem.mpr
        exact ⟨hy,fun x hx=>card_le_one.mp hc x hx y hy⟩
      rw [sourceChildProduct,hsingle,prod_singleton]
      have hpy := h.probability_le_bound (fun _ _=>⟨hactivity,hhi⟩) (mem_filter.mp hy).1
      apply (div_le_iff₀ hb1).mpr
      have := (le_div_iff₀ hb1).mp hpy
      nlinarith
  have hratio : activity/(1+b)≤p root/(1-p root) := by
    rw [h.odds_eq hr]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hprod hactivity.le
  have hinv : 1+p root/(1-p root)=1/(1-p root) := by field_simp; ring
  have hh : 1+activity/(1+b)≤1/(1-p root) := by linarith
  calc
    Real.log (1+activity/(1+b))≤Real.log (1/(1-p root)) :=
      Real.log_le_log (by positivity) hh
    _ = -Real.log (1-p root) := by rw [Real.log_div one_ne_zero hp1.ne']; simp

/-- Full stage-80 log source inequality, including its strictly useful
one-component root bonus, for every nonempty finite forest. -/
theorem forest_message_variance_with_log_bonus
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hS : S.Nonempty)
    {lower b activity : ℝ} (hlower : 0<lower) (hactivity : 0<activity)
    (hhi : activity≤b) (P : MessageSourceParameters) (hP : P.Admissible b)
    (hlo : P.w=0 ∨ lower≤activity) (hvalid : MessageSourceRowValid P lower b) :
    hardCoreVariance G S activity ≤
      P.CJ*hardCoreMarginalSelectionScore G S activity b+
      P.Cmu*hardCoreMean G S activity+
      (P.Dn-P.ell*Real.log (activity/lower))*(S.card:ℝ)-
      P.ell*Real.log (1+activity/(1+b)) := by
  classical
  obtain ⟨root,hr,hleaf⟩ := exists_closedNeighborhoodIn_card_le_two G hG S hS
  have hdegree : degreeOn G S root≤1 := by
    rw [card_closedNeighborhoodIn_eq_degree_add_one G S hr] at hleaf
    change (S.filter (G.Adj root)).card≤1
    omega
  let act : V→ℝ := fun _=>activity
  obtain ⟨parent,p,d,hm,hroot,hmean,hvar⟩ := exists_rooted_forest_source_messages_moments
    G hG S root act (fun _=>1) (fun _ _=>hactivity.le)
  have hresponse : (∑x∈S,p x*d x)=∑x∈S,heterogeneousMarginal G S act x := by
    rw [←hmean,heterogeneousMean_marked_eq_sum_marginals]
    simp
  have hbound := hm.message_variance_sum_bound hlower (fun _ _=>⟨hactivity,hhi⟩)
    P hP (hlo.imp_right (fun he _ _=>he)) hresponse hvalid
  have hcard : markedSum (fun _ : V=> (1:ℝ))=(fun J:Finset V=>(J.card:ℝ)) := by
    funext J; simp [markedSum]
  rw [←hvar,hcard] at hbound
  have hbonus := hm.leaf_log_bonus hactivity hhi hr hdegree
  have hroots : Real.log (1+activity/(1+b))≤
      -(∑x∈sourceRoots S parent,Real.log (1-p x)) := by
    have hmem : root∈sourceRoots S parent := mem_filter.mpr ⟨hr,hroot⟩
    have hrest : (∑x∈(sourceRoots S parent).erase root,Real.log (1-p x))≤0 := by
      apply sum_nonpos
      intro x hx
      have hb := hm.probability x (mem_filter.mp (mem_of_mem_erase hx)).1
      exact Real.log_nonpos (by linarith) (by linarith)
    have hsplit := sum_erase_add (sourceRoots S parent) (fun x=>Real.log (1-p x)) hmem
    linarith
  have hlog : (S.card:ℝ)*Real.log (activity/lower)+Real.log (1+activity/(1+b))≤
      ∑x∈S,sourceLogReference lower (p x) := by
    unfold sourceLogReference
    rw [hm.log_mass_identity (fun _ _=>hactivity) lower]
    simp only [act,sum_const,nsmul_eq_mul,Real.log_div hactivity.ne' hlower.ne']
    nlinarith
  have hmu : (∑x∈S,heterogeneousMarginal G S act x)=hardCoreMean G S activity := by
    simp only [act,heterogeneousMarginal_common]
    exact (hardCoreMean_eq_sum_vertex_marginals G S activity).symm
  have hscore : (∑x∈S,heterogeneousMarginal G S act x*
      selectionFraction (b/(1+b)) (heterogeneousMarginal G S act x))=
      hardCoreMarginalSelectionScore G S activity b := by
    simp only [act,heterogeneousMarginal_common,hardCoreMarginalSelectionScore]
  rw [hmu,hscore] at hbound
  simp only [act,heterogeneousVariance_common_card] at hbound
  nlinarith [mul_le_mul_of_nonneg_left hlog hP.2.1]

theorem IsMaximumMarginalIndependentOn.variance_le_mass_with_log_bonus
    {G : SimpleGraph V} {S I : Finset V} {lower b activity : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I activity) (hG : G.IsAcyclic)
    (hS : S.Nonempty) (hlower : 0<lower) (hactivity : 0<activity) (hhi : activity≤b)
    (P : MessageSourceParameters) (hP : P.Admissible b)
    (hCJ : 0≤P.CJ) (hCmu : 0≤P.Cmu) (hlo : P.w=0 ∨ lower≤activity)
    (hvalid : MessageSourceRowValid P lower b) :
    hardCoreVariance G S activity ≤
      (P.CJ+2*P.Cmu)*hardCoreOccupiedMass G S I activity+
      (P.Dn-P.ell*Real.log (activity/lower))*(S.card:ℝ)-
      P.ell*Real.log (1+activity/(1+b)) := by
  have hh := forest_message_variance_with_log_bonus G hG S hS
    hlower hactivity hhi P hP hlo hvalid
  have hs := mul_le_mul_of_nonneg_left (hI.forest_selection_bound hG hactivity hhi) hCJ
  have hhalf := hI.half_mean hG.isBipartite
  have hmu : hardCoreMean G S activity≤2*hardCoreOccupiedMass G S I activity := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hmu hCmu]

#print axioms SourceMessages.leaf_log_bonus
#print axioms forest_message_variance_with_log_bonus
#print axioms IsMaximumMarginalIndependentOn.variance_le_mass_with_log_bonus
end ForestUnimodality

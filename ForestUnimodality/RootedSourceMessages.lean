import ForestUnimodality.ForestSourceMessages
import ForestUnimodality.TreePathDecomposition

/-! Root-preserving elimination. In particular an original forest leaf can
be kept as a root of the exact source-moment message system. -/
namespace ForestUnimodality
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

theorem exists_degree_le_one_ne_of_isAcyclic
    {W : Type*} [Fintype W] [Nontrivial W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (hG : G.IsAcyclic) (root : W) :
    ∃ v, v≠root ∧ G.degree v≤1 := by
  classical
  obtain ⟨T,hGT,_,hT⟩ := (connected_top (V:=W)).exists_isTree_le_of_le_of_isAcyclic
    (show G≤⊤ from le_top) hG
  by_contra hn
  have hd : ∀v∈(univ.erase root : Finset W),2≤T.degree v := by
    intro v hv
    have hne := (mem_erase.mp hv).1
    have hn' : ¬G.degree v≤1 := fun hh=>hn ⟨v,hne,hh⟩
    exact (by omega : 2≤G.degree v).trans (degree_le_of_le hGT)
  have hs : 2*(univ.erase root : Finset W).card≤∑v∈univ.erase root,T.degree v := by
    calc
      _ = ∑_v∈(univ.erase root : Finset W),2 := by simp; omega
      _ ≤ _ := sum_le_sum hd
  have hroot := hT.preconnected.degree_pos_of_nontrivial root
  have hsum := T.sum_degrees_eq_twice_card_edges
  have hedge := hT.card_edgeFinset
  have hsplit := sum_erase_add (univ : Finset W) (fun v=>T.degree v) (mem_univ root)
  have hcard : (univ.erase root : Finset W).card+1=Fintype.card W := by
    simp only [card_erase_of_mem (mem_univ root),card_univ]
    have := Fintype.card_pos (α:=W)
    omega
  omega

theorem exists_leaf_ne_on (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (S : Finset V) (root : V) (hsize : 1<S.card) :
    ∃v∈S,v≠root ∧ (S.filter (G.Adj v)).card≤1 := by
  classical
  by_cases hr : root∈S
  · letI : Nontrivial (↑S : Set V) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by simpa using hsize)
    obtain ⟨v,hvr,hv⟩ := exists_degree_le_one_ne_of_isAcyclic
      (G.induce (↑S : Set V)) (hG.induce _) ⟨root,hr⟩
    refine ⟨v.val,v.property,?_,?_⟩
    · intro he; exact hvr (Subtype.ext he)
    · rw [←degreeOn_eq_degree_induce G S v.property] at hv
      convert hv using 1
      unfold degreeOn
      congr 1
      ext x
      simp
  · obtain ⟨v,hv,hsmall⟩ := exists_closedNeighborhoodIn_card_le_two G hG S
      (card_pos.mp (by omega))
    refine ⟨v,hv,(fun he=>hr (he ▸ hv)),?_⟩
    rw [card_closedNeighborhoodIn_eq_degree_add_one G S hv] at hsmall
    omega

inductive RootedSourceElimination (G : SimpleGraph V) (root : V) :
    Finset V → (V→ℝ) → (V→ℝ) → List (V×ℝ×ℝ) → Prop
  | nil (activity a : V→ℝ) : RootedSourceElimination G root ∅ activity a []
  | isolated {S : Finset V} {activity a : V→ℝ} {v : V} {rest : List (V×ℝ×ℝ)}
      (hv : v∈S) (hiso : ∀x∈S,¬G.Adj v x)
      (tail : RootedSourceElimination G root (S.erase v) activity a rest) :
      RootedSourceElimination G root S activity a ((v,activity v/(1+activity v),a v)::rest)
  | leaf {S : Finset V} {activity a : V→ℝ} {v u : V} {rest : List (V×ℝ×ℝ)}
      (hv : v∈S) (hu : u∈S) (hadj : G.Adj v u)
      (hleaf : ∀x∈S,G.Adj v x→x=u) (hne : v≠root)
      (tail : RootedSourceElimination G root (S.erase v) (leafReducedActivities activity v u)
        (leafReducedMarks activity a v u) rest) :
      RootedSourceElimination G root S activity a ((v,activity v/(1+activity v),a v)::rest)

theorem RootedSourceElimination.toElimination
    {G : SimpleGraph V} {root : V} {S : Finset V} {activity a : V→ℝ}
    {trace : List (V×ℝ×ℝ)} (h : RootedSourceElimination G root S activity a trace) :
    SourceElimination G S activity a trace := by
  induction h with
  | nil => exact .nil _ _
  | isolated hv hi _ ih => exact .isolated hv hi ih
  | leaf hv hu ha hl _ _ ih => exact .leaf hv hu ha hl ih

theorem exists_rootedSourceElimination (G : SimpleGraph V) (hG : G.IsAcyclic)
    (root : V) (S : Finset V) (activity a : V→ℝ) :
    ∃trace,RootedSourceElimination G root S activity a trace := by
  classical
  induction S using Finset.strongInductionOn generalizing activity a with
  | _ S ih =>
    by_cases hS : S=∅
    · subst S; exact ⟨[],.nil activity a⟩
    have hnon := nonempty_iff_ne_empty.mpr hS
    by_cases hsmall : S.card≤1
    · obtain ⟨v,hv⟩ := hnon
      have hi : ∀x∈S,¬G.Adj v x := by
        intro x hx ha
        have he := card_le_one.mp hsmall v hv x hx
        exact ha.ne he
      obtain ⟨rest,ht⟩ := ih (S.erase v) (erase_ssubset hv) activity a
      exact ⟨_,.isolated hv hi ht⟩
    obtain ⟨v,hv,hne,hdegree⟩ := exists_leaf_ne_on G hG S root (by omega)
    by_cases he : ∃u∈S,G.Adj v u
    · obtain ⟨u,hu,hadj⟩ := he
      have hl : ∀x∈S,G.Adj v x→x=u := by
        intro x hx ha
        exact card_le_one.mp hdegree x (mem_filter.mpr ⟨hx,ha⟩)
          u (mem_filter.mpr ⟨hu,hadj⟩)
      obtain ⟨rest,ht⟩ := ih (S.erase v) (erase_ssubset hv)
        (leafReducedActivities activity v u) (leafReducedMarks activity a v u)
      exact ⟨_,.leaf hv hu hadj hl hne ht⟩
    · have hi : ∀x∈S,¬G.Adj v x := by simpa only [not_exists,not_and] using he
      obtain ⟨rest,ht⟩ := ih (S.erase v) (erase_ssubset hv) activity a
      exact ⟨_,.isolated hv hi ht⟩


theorem RootedSourceElimination.messages
    {G : SimpleGraph V} {root : V} {S : Finset V} {activity a : V→ℝ}
    {trace : List (V×ℝ×ℝ)} (h : RootedSourceElimination G root S activity a trace)
    (hactivity : ∀x∈S,0≤activity x) :
    ∃parent p d,SourceMessages G S activity a parent p d ∧
      (∀r∈trace,p r.1=r.2.1 ∧ d r.1=r.2.2) ∧ parent root=none := by
  classical
  induction h with
  | nil =>
      refine ⟨fun _=>none,fun _=>0,fun _=>0,?_,?_,rfl⟩
      · constructor <;> simp
      · simp
  | @isolated S activity a v rest hv hiso tail ih =>
      obtain ⟨parent,p,d,hm,hagree,hroot⟩ :=
        ih (fun x hx=>hactivity x (mem_of_mem_erase hx))
      have hden : 1+activity v≠0 := ne_of_gt (by linarith [hactivity v hv])
      refine ⟨Function.update parent v none,
        Function.update p v (activity v/(1+activity v)),Function.update d v (a v),?_,?_,?_⟩
      · apply SourceMessages.extend hv none (by simp) hactivity
        · simpa only [sourceReducedActivity_none,sourceReducedMark_none] using hm
        · intro x hx
          simpa only [sourceReducedActivity_none] using
            heterogeneousMarginal_isolated_retained G S activity hv hiso hden (mem_erase.mp hx).1
        · simpa only [sourceParentMass,sub_zero,mul_one] using
            heterogeneousMarginal_isolated_removed G S activity hv hiso hactivity
      · intro r hr
        rcases List.mem_cons.mp hr with rfl|hr
        · simp only [Function.update_self,and_self]
        · simpa only [Function.update_of_ne (mem_erase.mp (tail.toElimination.mem hr)).1]
            using hagree r hr
      · by_cases he : root=v
        · simp [he]
        · rw [Function.update_of_ne he,hroot]
  | @leaf S activity a v u rest hv hu hadj hleaf hne tail ih =>
      obtain ⟨parent,p,d,hm,hagree,hroot⟩ :=
        ih (leafReducedActivities_nonneg activity S hv hactivity)
      have hden : 1+activity v≠0 := ne_of_gt (by linarith [hactivity v hv])
      refine ⟨Function.update parent v (some u),
        Function.update p v (activity v/(1+activity v)),Function.update d v (a v),?_,?_,?_⟩
      · refine SourceMessages.extend hv (some u) ?_ hactivity ?_ ?_ ?_
        · intro y hy
          have he : u=y := Option.some.inj hy
          subst y
          exact ⟨mem_erase.mpr ⟨hadj.ne.symm,hu⟩,hadj⟩
        · rw [sourceReducedActivity_some,sourceReducedMark_some]
          exact hm
        · intro x hx
          rw [sourceReducedActivity_some]
          exact heterogeneousMarginal_leaf_retained G S activity hv hadj hleaf hden (mem_erase.mp hx).1
        · rw [sourceParentMass,heterogeneousMarginal_leaf_removed G S activity hv hadj hleaf hactivity,
            heterogeneousMarginal_leaf_retained G S activity hv hadj hleaf hden hadj.ne.symm]
      · intro r hr
        rcases List.mem_cons.mp hr with rfl|hr
        · simp only [Function.update_self,and_self]
        · simpa only [Function.update_of_ne (mem_erase.mp (tail.toElimination.mem hr)).1]
            using hagree r hr
      · rw [Function.update_of_ne hne.symm,hroot]

/-- Exact first and second source moments with any prescribed vertex kept as
a root. No connectedness or preselected orientation is assumed. -/
theorem exists_rooted_forest_source_messages_moments
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (root : V)
    (activity a : V→ℝ) (hactivity : ∀x∈S,0≤activity x) :
    ∃parent p d,SourceMessages G S activity a parent p d ∧ parent root=none ∧
      heterogeneousMean G S activity (markedSum a)=∑x∈S,p x*d x ∧
      heterogeneousVariance G S activity (markedSum a)=
        ∑x∈S,heterogeneousMarginal G S activity x*(1-p x)*d x^2 := by
  obtain ⟨trace,ht⟩ := exists_rootedSourceElimination G hG root S activity a
  obtain ⟨parent,p,d,hm,hagree,hroot⟩ := ht.messages hactivity
  refine ⟨parent,p,d,hm,hroot,?_,?_⟩
  · rw [ht.toElimination.mean_identity hactivity,
      ←ht.toElimination.sum_vertices (fun x=>p x*d x)]
    congr 1
    apply List.map_congr_left
    intro r hr
    rw [(hagree r hr).1,(hagree r hr).2]
  · rw [ht.toElimination.variance_identity hactivity,sourceVarianceSum,
      ←ht.toElimination.sum_vertices (fun x=>heterogeneousMarginal G S activity x*(1-p x)*d x^2)]
    congr 1
    apply List.map_congr_left
    intro r hr
    rw [(hagree r hr).1,(hagree r hr).2]

#print axioms exists_degree_le_one_ne_of_isAcyclic
#print axioms exists_rootedSourceElimination
#print axioms exists_rooted_forest_source_messages_moments
end ForestUnimodality

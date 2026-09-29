import ForestUnimodality.UnitActivitySmallForest
import ForestUnimodality.UnitActivityTreeBranches
import ForestUnimodality.UnitActivityFanDensity
import ForestUnimodality.ForestComponentsMean

/-! Global unit-activity mean density, retaining positive intercepts during
the forest induction so that disconnected components close the same bound. -/
namespace ForestUnimodality.UnitActivityForestDensity
open Finset
variable {V : Type*} [DecidableEq V]

theorem exists_disconnected_split (G : SimpleGraph V) (S : Finset V)
    (hS : S.Nonempty) (hconn : ¬(G.induce (S : Set V)).Connected) :
    ∃ A B : Finset V, A ⊆ S ∧ B ⊆ S ∧ A.Nonempty ∧ B.Nonempty ∧
      A.card < S.card ∧ B.card < S.card ∧ Disjoint A B ∧ A ∪ B = S ∧
      ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b := by
  classical
  obtain ⟨x, hx⟩ := hS
  letI : Nonempty (S : Set V) := ⟨⟨x, hx⟩⟩
  have hp : ¬(G.induce (S : Set V)).Preconnected := fun hp => hconn { preconnected := hp }
  obtain ⟨u, hu⟩ := not_forall.mp hp
  obtain ⟨v, huv⟩ := not_forall.mp hu
  let A : Finset V := S.filter fun a => ∃ ha : a ∈ S,
    (G.induce (S : Set V)).Reachable u ⟨a, ha⟩
  let B : Finset V := S \ A
  have hAS : A ⊆ S := filter_subset _ _
  have hBS : B ⊆ S := sdiff_subset
  have huA : u.val ∈ A := mem_filter.mpr ⟨u.property, ⟨u.property, .rfl⟩⟩
  have hvA : v.val ∉ A := by
    intro hv
    obtain ⟨_, hvS, hr⟩ := mem_filter.mp hv
    exact huv hr
  have hvB : v.val ∈ B := mem_sdiff.mpr ⟨v.property, hvA⟩
  have huB : u.val ∉ B := fun hu => (mem_sdiff.mp hu).2 huA
  have hltA : A.card < S.card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hAS, ?_⟩
    intro he
    exact hvA (he.symm ▸ v.property)
  have hltB : B.card < S.card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hBS, ?_⟩
    intro he
    exact huB (he.symm ▸ u.property)
  refine ⟨A, B, hAS, hBS, ⟨u.val, huA⟩, ⟨v.val, hvB⟩,
    hltA, hltB, disjoint_sdiff_self_right, union_sdiff_of_subset hAS, ?_⟩
  intro a ha b hb hab
  obtain ⟨_, haS, hra⟩ := mem_filter.mp ha
  have hbS := hBS hb
  have hadj : (G.induce (S : Set V)).Adj ⟨a, haS⟩ ⟨b, hbS⟩ := hab
  exact (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨hbS, ⟨hbS, hra.trans hadj.reachable⟩⟩)

theorem mean_lower_of_degree_le_two (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (hS : S.Nonempty) (hconn : (G.induce (S : Set V)).Connected)
    (hdegrees : ∀ x ∈ S, degreeOn G S x ≤ 2) :
    276393 / 1000000 * (S.card : ℝ) + 113880 / 1000000 ≤ hardCoreMean G S 1 ∧
      (S.card ≠ 2 → 276393 / 1000000 * (S.card : ℝ) + 144420 / 1000000 ≤ hardCoreMean G S 1) := by
  classical
  letI : Nonempty (S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  obtain ⟨v, hv⟩ := exists_degree_le_one_of_isAcyclic
    (G.induce (S : Set V)) (hG.induce (S : Set V))
  have hd : degreeOn G S v.val ≤ 1 := by
    rwa [degreeOn_eq_degree_induce G S v.property]
  obtain ⟨u, n, hp⟩ := exists_pendantPath_to_of_connected_degree_le_two
    G S v.property hconn hdegrees hd
  exact ⟨hp.unitActivity_mean_lower, hp.unitActivity_mean_lower_except_two⟩

/-- Both positive-intercept estimates hold for every finite induced forest.
The exceptional two-vertex case is retained only in the stronger estimate. -/
theorem mean_density_bounds (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) :
    (0 < S.card → 276393 / 1000000 * (S.card : ℝ) + 113880 / 1000000 ≤ hardCoreMean G S 1) ∧
      (0 < S.card → S.card ≠ 2 →
        276393 / 1000000 * (S.card : ℝ) + 144420 / 1000000 ≤ hardCoreMean G S 1) := by
  classical
  refine S.strongInductionOn ?_
  intro S ih
  by_cases hpos : 0 < S.card
  · by_cases htwo : S.card = 2
    · constructor
      · intro _
        have h := UnitActivitySmallForest.mean_ge_two_thirds_of_card_two G S htwo
        norm_num [htwo]
        linarith
      · exact fun _ hne => (hne htwo).elim
    have hrec (T : Finset V) (hTS : T ⊆ S) (hlt : T.card < S.card) :=
      ih T (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, by
        intro he
        subst T
        exact (lt_irrefl _ hlt)⟩)
    have hstrong : 276393 / 1000000 * (S.card : ℝ) + 144420 / 1000000 ≤ hardCoreMean G S 1 := by
      by_cases hconn : (G.induce (S : Set V)).Connected
      · by_cases hdegrees : ∀ x ∈ S, degreeOn G S x ≤ 2
        · exact (mean_lower_of_degree_le_two G hG S (card_pos.mp hpos) hconn hdegrees).2 htwo
        · push Not at hdegrees
          obtain ⟨c, hc, hdeg⟩ := hdegrees
          obtain ⟨root, hfan⟩ := exists_rootedFan_of_tree G hG S hc hconn
          apply hfan.unitActivity_density_lower
          · rw [← hfan.unitActivity_degree_center]
            omega
          · intro i _
            exact deletedCenterBranch_connected G S c i
          · exact hG
          · intro T hTS hlt hn hne
            exact (hrec T hTS hlt).2 hn hne
      · obtain ⟨A, B, hAS, hBS, hA, hB, hltA, hltB, hdis, hunion, hcross⟩ :=
          exists_disconnected_split G S (card_pos.mp hpos) hconn
        have hmuA := (hrec A hAS hltA).1 (card_pos.mpr hA)
        have hmuB := (hrec B hBS hltB).1 (card_pos.mpr hB)
        have hmu := hardCoreMean_disjoint_union G A B hdis hcross (by norm_num : (0 : ℝ) ≤ 1)
        have hcard : (A.card : ℝ) + B.card = S.card := by
          exact_mod_cast ((card_union_of_disjoint hdis).symm.trans (congrArg Finset.card hunion))
        rw [hunion] at hmu
        linarith
    exact ⟨fun _ => by linarith, fun _ _ => hstrong⟩
  · exact ⟨fun hp => (hpos hp).elim, fun hp _ => (hpos hp).elim⟩

theorem mean_lower (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (hS : S.Nonempty) :
    276393 / 1000000 * (S.card : ℝ) + 113880 / 1000000 ≤ hardCoreMean G S 1 :=
  (mean_density_bounds G hG S).1 (card_pos.mpr hS)

theorem mean_lower_except_two (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (hS : S.Nonempty) (hne : S.card ≠ 2) :
    276393 / 1000000 * (S.card : ℝ) + 144420 / 1000000 ≤ hardCoreMean G S 1 :=
  (mean_density_bounds G hG S).2 (card_pos.mpr hS) hne

/-- The unqualified density inequality includes the empty forest. -/
theorem mean_density_lower (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) :
    276393 / 1000000 * (S.card : ℝ) ≤ hardCoreMean G S 1 := by
  by_cases hS : S.Nonempty
  · have h := mean_lower G hG S hS
    linarith
  · have hc : S.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hS)
    rw [UnitActivitySmallForest.mean_eq_zero_of_card_zero G S hc, hc]
    norm_num

#print axioms exists_disconnected_split
#print axioms mean_lower_of_degree_le_two
#print axioms mean_density_bounds
#print axioms mean_lower
#print axioms mean_lower_except_two
#print axioms mean_density_lower
end ForestUnimodality.UnitActivityForestDensity

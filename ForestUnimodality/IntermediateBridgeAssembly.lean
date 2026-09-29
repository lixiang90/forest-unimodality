import ForestUnimodality.IntermediateBridgeParentData.Links
import ForestUnimodality.IntermediateBridgeRankData.Covers
import ForestUnimodality.Stage170Geometry.Complete
import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteCoverage
import ForestUnimodality.Stage350Unimodality

/-! Final assembly with precisely stated remaining finite obligations.
This file does not discharge all rectangle and parent proofs. Its target
theorem is conditional, and is not a proof of CompleteTarget by itself. -/
namespace ForestUnimodality.IntermediateBridgeAssembly
universe u
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def RequiredRectangle (i : CellKey) : Prop :=
  ∃b : Band CellKey,
    (b∈cover59.bands ∨ b∈cover80.bands ∨ b∈cover99.bands ∨ b∈cover130.bands) ∧ i∈b.cells

def RectanglesValid : Prop :=
  ∀i : CellKey,RequiredRectangle i→Rectangle.ForestValid.{u} (rectangle i)

def ParentsValid : Prop := ∀i : Fin 130,ParentComplete.{u} i

theorem no_weak_valley_below170 (hp : ParentsValid.{u}) (hc : RectanglesValid.{u})
    {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (z : ℝ) (k : ℕ)
    (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤169) (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/13:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hhalf : 2*k≤S.card) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases hn130 : 130≤S.card
  · exact cover130.no_weak_valley rectangle cover130_checked
      IntermediateBridgeRankData.cover130_rank (IntermediateBridgeParentData.cover130_parents hp)
      (fun b hb i hi=>hc i ⟨b,Or.inr (Or.inr (Or.inr hb)),hi⟩)
      G S z k hG (by omega) (by omega) hn130 hN hz hk
      (by norm_num [cover130];exact hq) hrank hmean hhalf
  by_cases hn99 : 99≤S.card
  · exact cover99.no_weak_valley rectangle cover99_checked
      IntermediateBridgeRankData.cover99_rank (IntermediateBridgeParentData.cover99_parents hp)
      (fun b hb i hi=>hc i ⟨b,Or.inr (Or.inr (Or.inl hb)),hi⟩)
      G S z k hG (by omega) (by omega) hn99 (by change S.card≤129;omega) hz hk
      (by norm_num [cover99];exact hq) hrank hmean hhalf
  by_cases hn80 : 80≤S.card
  · exact cover80.no_weak_valley rectangle cover80_checked
      IntermediateBridgeRankData.cover80_rank (IntermediateBridgeParentData.cover80_parents hp)
      (fun b hb i hi=>hc i ⟨b,Or.inr (Or.inl hb),hi⟩)
      G S z k hG (by omega) (by omega) hn80 (by change S.card≤98;omega) hz hk
      (by norm_num [cover80];exact hq) hrank hmean hhalf
  exact cover59.no_weak_valley rectangle cover59_checked
    IntermediateBridgeRankData.cover59_rank (IntermediateBridgeParentData.cover59_parents hp)
    (fun b hb i hi=>hc i ⟨b,Or.inl hb,hi⟩)
    G S z k hG (by omega) (by omega) hn (by change S.card≤79;omega) hz hk
    (by norm_num [cover59];exact hq) hrank hmean hhalf

theorem no_weak_valley_intermediate (hp : ParentsValid.{u}) (hc : RectanglesValid.{u})
    {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (z : ℝ) (k : ℕ)
    (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/13:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hhalf : 2*k≤S.card) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases hn170 : 170≤S.card
  · obtain ⟨i,_,hqi⟩ := FiniteRectangleCover.chainCheck_sound
      (fun i : Fin 130=>((Stage170Geometry.strip i).qlo,(Stage170Geometry.strip i).qhi))
      (List.finRange 130) Stage170Geometry.horizontal_checked (by norm_num;exact hq)
    obtain ⟨B,hB⟩ := exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
    change IsMaximumMarginalIndependentOn G S B z at hB
    have hlo := (Stage170Geometry.strip i).actual_mean_lower (Stage170Geometry.window i) 170
      (Stage170Geometry.window_valid i) (Stage170Geometry.sources_checked i) hB hG hz hn170 hqi hrank
    exact hp i G S B z k hB hG (by omega) hN hz hk hqi hrank hmean hlo
  · exact no_weak_valley_below170 hp hc G S z k hG hn (by omega) hz hk hq hrank hmean hhalf

theorem countIndependent_unimodal_of_domains (hp : ParentsValid.{u}) (hc : RectanglesValid.{u})
    {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (hG : G.IsAcyclic) :
    WeaklyUnimodal (countIndependent G S) := by
  by_cases hsmall : S.card≤60
  · exact countIndependent_unimodal_of_isAcyclic_card_le_sixty G hG S hsmall
  by_cases hlarge : 350≤S.card
  · exact countIndependent_unimodal_of_card_ge350 G S hG hlarge
  obtain ⟨I,hI⟩ := exists_maximumIndependentOn G S
  apply weaklyUnimodal_of_no_central_weak_valley (countIndependent G S)
    ((S.card+3)/4) ((S.card+2*I.card)/6+1)
    (countIndependent_le_succ_of_quarter G hG S)
    (hI.countIndependent_succ_le_of_matching_tail hG)
  intro k hkL hkU hkpos hvalley
  obtain ⟨z,⟨hz,hmean⟩,_⟩ := hI.existsUnique_central_activity hG k hkL hkU hkpos
  have hz0 : 0<z := lt_of_lt_of_le (by norm_num) hz.1
  have hrank : (S.card:ℝ)/4≤hardCoreMean G S z := by
    have hk : S.card≤4*k := by omega
    have hkR : (S.card:ℝ)≤4*(k:ℝ) := by exact_mod_cast hk
    rw [hmean]
    linarith
  have hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/13:ℝ) := by
    constructor
    · apply (le_div_iff₀ (by positivity : (0:ℝ)<1+z)).mpr
      linarith [hz.1]
    · apply (div_le_iff₀ (by positivity : (0:ℝ)<1+z)).mpr
      linarith [hz.2]
  have hhalf := FiniteMarginalSupport.central_rank_half (Finset.card_le_card hI.subset) hkU
  exact no_weak_valley_intermediate hp hc G S z k hG (by omega) (by omega)
    hz0 hkpos hq hrank hmean hhalf hvalley

theorem completeTarget_of_domains (hp : ParentsValid.{0}) (hc : RectanglesValid.{0}) : CompleteTarget := by
  intro n G hG
  classical
  have h := countIndependent_unimodal_of_domains hp hc G Finset.univ hG
  simpa only [WeaklyUnimodal,countIndependent_univ_eq_independentCount] using h

#print axioms no_weak_valley_below170
#print axioms no_weak_valley_intermediate
#print axioms countIndependent_unimodal_of_domains
#print axioms completeTarget_of_domains
end ForestUnimodality.IntermediateBridgeAssembly

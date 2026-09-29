import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeForestData.Stage130Additional035_038
import ForestUnimodality.IntermediateBridgeForestData.Stage59Initial
import ForestUnimodality.IntermediateBridgeForestData.Stage80Additional039_039
import ForestUnimodality.IntermediateBridgeForestData.Stage99Additional036_036
import ForestUnimodality.IntermediateBridgeForestData.Stage99Additional037_040
import ForestUnimodality.IntermediateBridgeParentData.Actual030_039
import ForestUnimodality.IntermediateBridgeRankData.Batch128_143
import ForestUnimodality.Stage170Windows.Strip035.Complete

/-! Actual refined activity cover. Rank, integer mean and half-rank hypotheses remain explicit. -/
namespace ForestUnimodality.RefinedBridgeActivityData.Strip035
universe u
open IntermediateBridgeCover IntermediateBridgeCoverData IntermediateBridgeForestData
variable {V : Type u} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def cover59 : ActivityCover CellKey where
  qlo := (1733/3648)
  qhi := (869/1824)
  lowerOrder := 59
  orderCap := 79
  bands := [band140]

theorem cover59_checked : cover59.check rectangle=true := by decide +kernel
#print axioms cover59_checked

theorem cover59_ranks : ∀b∈cover59.bands,Band.RankValid.{0,u} b := by
  simp only [cover59,List.forall_mem_cons,IntermediateBridgeRankData.band140_rank]
  simp

theorem cover59_parents : ∀b∈cover59.bands,Band.ParentValid.{u,0} b := by
  have hband140 : Band.ParentValid.{u,0} band140 :=
    band140.parent_of_check 35 (by decide +kernel) IntermediateBridgeParentData.parent035_complete
  simp only [cover59,List.forall_mem_cons,hband140]
  simp

theorem cover59_cells : ∀b∈cover59.bands,∀i∈b.cells,Rectangle.ForestValid.{u} (rectangle i) := by
  intro b hb i hi
  have h : b=band140 := by
    simpa only [cover59,List.mem_cons,List.not_mem_nil,or_false] using hb
  rcases h with rfl
  · have h : i=(59,41) ∨ i=(59,42) ∨ i=(99,36) ∨ i=(99,37) ∨ i=(130,35) := by
      simpa only [band140,List.mem_cons,List.not_mem_nil,or_false] using hi
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact @stage59_cell041
    · exact @stage59_cell042
    · exact @stage99_cell036
    · exact @stage99_cell037
    · exact @stage130_cell035

#print axioms cover59_ranks
#print axioms cover59_parents
#print axioms cover59_cells

def cover80 : ActivityCover CellKey where
  qlo := (1733/3648)
  qhi := (869/1824)
  lowerOrder := 80
  orderCap := 98
  bands := [band141]

theorem cover80_checked : cover80.check rectangle=true := by decide +kernel
#print axioms cover80_checked

theorem cover80_ranks : ∀b∈cover80.bands,Band.RankValid.{0,u} b := by
  simp only [cover80,List.forall_mem_cons,IntermediateBridgeRankData.band141_rank]
  simp

theorem cover80_parents : ∀b∈cover80.bands,Band.ParentValid.{u,0} b := by
  have hband141 : Band.ParentValid.{u,0} band141 :=
    band141.parent_of_check 35 (by decide +kernel) IntermediateBridgeParentData.parent035_complete
  simp only [cover80,List.forall_mem_cons,hband141]
  simp

theorem cover80_cells : ∀b∈cover80.bands,∀i∈b.cells,Rectangle.ForestValid.{u} (rectangle i) := by
  intro b hb i hi
  have h : b=band141 := by
    simpa only [cover80,List.mem_cons,List.not_mem_nil,or_false] using hb
  rcases h with rfl
  · have h : i=(80,39) ∨ i=(99,36) ∨ i=(99,37) ∨ i=(130,35) := by
      simpa only [band141,List.mem_cons,List.not_mem_nil,or_false] using hi
    rcases h with rfl | rfl | rfl | rfl
    · exact @stage80_cell039
    · exact @stage99_cell036
    · exact @stage99_cell037
    · exact @stage130_cell035

#print axioms cover80_ranks
#print axioms cover80_parents
#print axioms cover80_cells

def cover99 : ActivityCover CellKey where
  qlo := (1733/3648)
  qhi := (869/1824)
  lowerOrder := 99
  orderCap := 129
  bands := [band142]

theorem cover99_checked : cover99.check rectangle=true := by decide +kernel
#print axioms cover99_checked

theorem cover99_ranks : ∀b∈cover99.bands,Band.RankValid.{0,u} b := by
  simp only [cover99,List.forall_mem_cons,IntermediateBridgeRankData.band142_rank]
  simp

theorem cover99_parents : ∀b∈cover99.bands,Band.ParentValid.{u,0} b := by
  have hband142 : Band.ParentValid.{u,0} band142 :=
    band142.parent_of_check 35 (by decide +kernel) IntermediateBridgeParentData.parent035_complete
  simp only [cover99,List.forall_mem_cons,hband142]
  simp

theorem cover99_cells : ∀b∈cover99.bands,∀i∈b.cells,Rectangle.ForestValid.{u} (rectangle i) := by
  intro b hb i hi
  have h : b=band142 := by
    simpa only [cover99,List.mem_cons,List.not_mem_nil,or_false] using hb
  rcases h with rfl
  · have h : i=(99,36) ∨ i=(99,37) ∨ i=(130,35) := by
      simpa only [band142,List.mem_cons,List.not_mem_nil,or_false] using hi
    rcases h with rfl | rfl | rfl
    · exact @stage99_cell036
    · exact @stage99_cell037
    · exact @stage130_cell035

#print axioms cover99_ranks
#print axioms cover99_parents
#print axioms cover99_cells

def cover130 : ActivityCover CellKey where
  qlo := (1733/3648)
  qhi := (869/1824)
  lowerOrder := 130
  orderCap := 169
  bands := [band143]

theorem cover130_checked : cover130.check rectangle=true := by decide +kernel
#print axioms cover130_checked

theorem cover130_ranks : ∀b∈cover130.bands,Band.RankValid.{0,u} b := by
  simp only [cover130,List.forall_mem_cons,IntermediateBridgeRankData.band143_rank]
  simp

theorem cover130_parents : ∀b∈cover130.bands,Band.ParentValid.{u,0} b := by
  have hband143 : Band.ParentValid.{u,0} band143 :=
    band143.parent_of_check 35 (by decide +kernel) IntermediateBridgeParentData.parent035_complete
  simp only [cover130,List.forall_mem_cons,hband143]
  simp

theorem cover130_cells : ∀b∈cover130.bands,∀i∈b.cells,Rectangle.ForestValid.{u} (rectangle i) := by
  intro b hb i hi
  have h : b=band143 := by
    simpa only [cover130,List.mem_cons,List.not_mem_nil,or_false] using hb
  rcases h with rfl
  · have h : i=(130,35) := by
      simpa only [band143,List.mem_cons,List.not_mem_nil,or_false] using hi
    rcases h with rfl
    · exact @stage130_cell035

#print axioms cover130_ranks
#print axioms cover130_parents
#print axioms cover130_cells

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc ((1733/3648):ℝ) ((869/1824):ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hhalf : 2*k≤S.card) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases hn170 : 170≤S.card
  · exact Stage170Windows.Strip035.no_weak_valley k hG hn170 hN hz hq hrank hmean
  have hnR : (59:ℝ)≤S.card := by exact_mod_cast hn
  have hkR : (1:ℝ)≤(k:ℝ) := by linarith
  have hk : 1≤k := by exact_mod_cast hkR
  by_cases hn130 : 130≤S.card
  · exact cover130.no_weak_valley rectangle cover130_checked
      cover130_ranks cover130_parents cover130_cells
      G S z k hG (by omega) hN (by change 130≤S.card; omega)
      (by change S.card≤169; omega) hz hk
      (by simpa only [cover130,Rat.cast_div,Rat.cast_ofNat] using hq) hrank hmean hhalf
  by_cases hn99 : 99≤S.card
  · exact cover99.no_weak_valley rectangle cover99_checked
      cover99_ranks cover99_parents cover99_cells
      G S z k hG (by omega) hN (by change 99≤S.card; omega)
      (by change S.card≤129; omega) hz hk
      (by simpa only [cover99,Rat.cast_div,Rat.cast_ofNat] using hq) hrank hmean hhalf
  by_cases hn80 : 80≤S.card
  · exact cover80.no_weak_valley rectangle cover80_checked
      cover80_ranks cover80_parents cover80_cells
      G S z k hG (by omega) hN (by change 80≤S.card; omega)
      (by change S.card≤98; omega) hz hk
      (by simpa only [cover80,Rat.cast_div,Rat.cast_ofNat] using hq) hrank hmean hhalf
  exact cover59.no_weak_valley rectangle cover59_checked
    cover59_ranks cover59_parents cover59_cells
    G S z k hG (by omega) hN (by change 59≤S.card; omega)
    (by change S.card≤79; omega) hz hk
    (by simpa only [cover59,Rat.cast_div,Rat.cast_ofNat] using hq) hrank hmean hhalf

#print axioms no_weak_valley
end ForestUnimodality.RefinedBridgeActivityData.Strip035

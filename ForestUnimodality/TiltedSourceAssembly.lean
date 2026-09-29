import ForestUnimodality.TiltedSourceCells

/-! Finite probability covers imply full scalar validity for two independent
activity caps, including all three mark states and both leaf endpoints. -/
namespace ForestUnimodality.TiltedSource
open SelectionSource

def sourceDomain (D0 D1 : Domain) (s : Fin 3) : Domain := if s=2 then D1 else D0
def parentCap (D0 D1 : Domain) (s : Fin 3) : ℚ := if s=1 then D1.b else D0.b

theorem sourceRowValid_of_checked (P : Parameters) (D0 D1 : Domain)
    (cells : Fin 3→List Cell) (hP : P.check=true) (hD0 : D0.check=true) (hD1 : D1.check=true)
    (hleaf : ∀s,leafCheck P s (sourceDomain D0 D1 s) (parentCap D0 D1 s)=true)
    (hchecks : ∀s,(cells s).all (fun c=>c.check P s (sourceDomain D0 D1 s) (parentCap D0 D1 s))=true)
    (hcover : ∀s,SourceIntervalCoverage.check Cell.left Cell.right 0
      (probabilityCap (sourceDomain D0 D1 s)) (cells s)=true) :
    TiltedSourceRowValid P.toReal (tiltedMarkCap D0.b D1.b) := by
  intro a pa hs p r z hp hpq hr hr1 hend
  obtain ⟨s,rfl,rfl⟩ : ∃s:Fin 3,a=(sourceMark s:ℝ) ∧ pa=(parentMark s:ℝ) := by
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨0,by norm_num [sourceMark,Fin.ext_iff],by norm_num [parentMark,Fin.ext_iff]⟩
    · exact ⟨1,by norm_num [sourceMark,Fin.ext_iff],by norm_num [parentMark,Fin.ext_iff]⟩
    · exact ⟨2,by norm_num [sourceMark,Fin.ext_iff],by norm_num [parentMark,Fin.ext_iff]⟩
  have hd : (sourceDomain D0 D1 s).Valid := by
    unfold sourceDomain
    split_ifs
    · exact ParametricSource.Domain.check_sound hD1
    · exact ParametricSource.Domain.check_sound hD0
  have hc : tiltedMarkCap (D0.b:ℝ) D1.b (sourceMark s)=((sourceDomain D0 D1 s).b:ℝ) := by
    fin_cases s <;> simp [tiltedMarkCap,sourceMark,sourceDomain]
  have hpc : tiltedMarkCap (D0.b:ℝ) D1.b (parentMark s)=(parentCap D0 D1 s:ℝ) := by
    fin_cases s <;> simp [tiltedMarkCap,parentMark,parentCap]
  have hq : (probabilityCap (sourceDomain D0 D1 s):ℝ)=
      ((sourceDomain D0 D1 s).b:ℝ)/(1+((sourceDomain D0 D1 s).b:ℝ)) := by
    simp only [probabilityCap,Rat.cast_div,Rat.cast_add,Rat.cast_one]
  rw [hc] at hpq hend
  rw [hpc] at hr
  by_cases he : p=(probabilityCap (sourceDomain D0 D1 s):ℝ)
  · have hz := hend (he.trans hq)
    subst p
    subst z
    exact leafCheck_sound (tiltedMarkCap D0.b D1.b) (hleaf s) hd hr hr1
  · have hpq' : p<((sourceDomain D0 D1 s).b:ℝ)/(1+((sourceDomain D0 D1 s).b:ℝ)) :=
      lt_of_le_of_ne hpq (fun hh=>he (hh.trans hq.symm))
    obtain ⟨cell,hmem,hlo,hhi⟩ := SourceIntervalCoverage.check_sound Cell.left Cell.right (hcover s)
      (p:=p) (by simpa only [Rat.cast_zero] using hp) (hq.symm ▸ hpq)
    exact Cell.check_sound (tiltedMarkCap D0.b D1.b)
      ((List.all_eq_true.mp (hchecks s)) cell hmem) hd hP hc hp hlo hhi hpq' hr hr1

#print axioms sourceRowValid_of_checked
end ForestUnimodality.TiltedSource

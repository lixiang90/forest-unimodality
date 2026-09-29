import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell091.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell091
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(38608920848500761529188899351/500000000000000000000000000000), (86363953492236814274114214467/500000000000000000000000000000)]
def R : ℚ := (503797271022727272727272727273/500000000000000000000000000000)
def D : ℚ := (5771073659/3200000000)
def vmax : ℚ := (5720/23409)
def mlo : ℚ := (715981153846153846153846153846143551/8000000000000000000000000000000000)
def mhi : ℚ := (1575/16)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (72755371502669757621061894409722930119305678061557819804334437728951653760687004306850155236893805781/149817600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (19450420375214694246324143/2500000000000000000000000)) (.exp (-27643259697864400432855047990673987515220030707967632149636735401/4000000000000000000000000000000000000000000000000000000000000000) (498472515230576787517/500000000000000000000000) (199389006092230715007/200000000000000000000000) { parts := 7, inner := (-27643259697864400432855047990673987515220030707967632149636735401/28000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (46574559676951051203086851507/125000000000000000000000000000), innerHi := (372596477415608409624694812057/1000000000000000000000000000000) }))) (.mul (.rat (1222257271167163494851593/50000000000000000000000)) (.exp (-61834963072087282249535226944329232792888958423191384259682952317/4000000000000000000000000000000000000000000000000000000000000000) (96677228468665403/500000000000000000000000) (193354456937330807/1000000000000000000000000) { parts := 16, inner := (-61834963072087282249535226944329232792888958423191384259682952317/64000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (190268608059889504164018035847/500000000000000000000000000000), innerHi := (76107443223955801665607214339/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (306830928150137478209278396394748668496847033739623185899/650250000000000000000000000000000000000000000000000000000)) (.mul (.rat (19450420375214694246324143/2500000000000000000000000)) (.exp (-2432362013455547976338900659113/320000000000000000000000000000) (499885596836827978369/1000000000000000000000000) (49988559683682797837/100000000000000000000000) { parts := 8, inner := (-2432362013455547976338900659113/2560000000000000000000000000000), terms := 40, innerLo := (386686337690603373885957308959/1000000000000000000000000000000), innerHi := (2416789610566271086787233181/6250000000000000000000000000) }))) (.mul (.rat (1222257271167163494851593/50000000000000000000000)) (.exp (-5440929070010919299269195511421/320000000000000000000000000000) (10319838720186529/250000000000000000000000) (41279354880746117/1000000000000000000000000) { parts := 18, inner := (-604547674445657699918799501269/640000000000000000000000000000), terms := 40, innerLo := (388832841407927068468388911449/1000000000000000000000000000000), innerHi := (7776656828158541369367778229/20000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM (R * vmax : ℚ) 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage170KernelData.Cell091

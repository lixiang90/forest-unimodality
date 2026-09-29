import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell025.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell025
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(150106131172842912568870679403/1000000000000000000000000000000), (242127876457005104422077399473/1000000000000000000000000000000)]
def R : ℚ := (53922541/50000000)
def D : ℚ := (883742337164179104477611940299/500000000000000000000000000000)
def vmax : ℚ := (20/81)
def mlo : ℚ := (189/8)
def mhi : ℚ := (225/8)
def alpha : ℚ := (53922541/202500000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (34220103992857715933838690949706260855472947430334644010281/120000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (42815190588108809066625327/10000000000000000000000000)) (.exp (-28370058791667310475516558407167/8000000000000000000000000000000) (28832347387264409974137/1000000000000000000000000) (14416173693632204987069/500000000000000000000000) { parts := 4, inner := (-28370058791667310475516558407167/32000000000000000000000000000000), terms := 40, innerLo := (412069053852207511964010102079/1000000000000000000000000000000), innerHi := (1287715793288148474887531569/3125000000000000000000000000) }))) (.mul (.rat (9352978475897618437784331/500000000000000000000000)) (.exp (-45762168650373964735772628500397/8000000000000000000000000000000) (409852744319152220999/125000000000000000000000) (3278821954553217767993/1000000000000000000000000) { parts := 6, inner := (-15254056216791321578590876166799/16000000000000000000000000000000), terms := 40, innerLo := (385436618382478826971111170233/1000000000000000000000000000000), innerHi := (192718309191239413485555585117/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (2647314937400560070079470146636608693638992490047806287183/14400000000000000000000000000000000000000000000000000000000)) (.mul (.rat (42815190588108809066625327/10000000000000000000000000)) (.exp (-1350955180555586213119836114627/320000000000000000000000000000) (1834145669825940335681/125000000000000000000000) (14673165358607522685449/1000000000000000000000000) { parts := 5, inner := (-1350955180555586213119836114627/1600000000000000000000000000000), terms := 40, innerLo := (214918977996433687405846062467/500000000000000000000000000000), innerHi := (85967591198573474962338424987/200000000000000000000000000000) }))) (.mul (.rat (9352978475897618437784331/500000000000000000000000)) (.exp (-2179150888113045939798696595257/320000000000000000000000000000) (220572429669662579511/200000000000000000000000) (275715537087078224389/250000000000000000000000) { parts := 7, inner := (-2179150888113045939798696595257/2240000000000000000000000000000), terms := 40, innerLo := (378009777268413359692096412817/1000000000000000000000000000000), innerHi := (189004888634206679846048206409/500000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage80KernelData.Cell025

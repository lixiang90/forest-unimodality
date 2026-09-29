import ForestUnimodality.BridgeFlowData.Stage99.Cell180Term01.Batch000

import ForestUnimodality.BridgeFlowData.Stage99.Cell180Term01.Batch001

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell180Term01
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows

theorem rows_length : rows.length=24 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (17841806671924039454184518956798668083/5000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (189152410215202898072602544621203439929/80000000000000000000000000000000000000)

def table : Table :=
  ⟨24, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-16094379124341003/20000000000000000), 64, (22360679774997897798153581898290983597734739829101/50000000000000000000000000000000000000000000000000), (44721359549995795596307163796581967195469479658203/100000000000000000000000000000000000000000000000000)⟩, (500000000000000037300379666613095211081123950617811785964012179580325707313597791129061366686468201/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (2000000000000000149201518666452380844324495802471336586575148709912495443581984328450636405705189209/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

theorem header_checked : table.headerCheck=true := by decide +kernel

theorem connections_checked : (List.range table.n).all table.connectionCheck=true := by decide +kernel

theorem table_rows_checked : (List.range table.n).all (fun i=>(table.row i).check table.environment)=true := by

  apply List.all_eq_true.mpr
  intro i hi
  apply check_getD rows Batch000.row000 environment rows_checked i
  rw [rows_length]
  exact List.mem_range.mp hi

#print axioms header_checked

#print axioms connections_checked

#print axioms table_rows_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell180Term01

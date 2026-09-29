import ForestUnimodality.BridgeFlowData.Stage80.Cell101Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell101Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=12 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (2867027378545325767873090144897408067/500000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (15861864682743601795024709126933659867819/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨12, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-11184338897989661/15000000000000000), 64, (11860970639574931204082035377527703789810507112517/25000000000000000000000000000000000000000000000000), (47443882558299724816328141510110815159242028450069/100000000000000000000000000000000000000000000000000)⟩, (1668632478845359800856989141846614688169449935107954187943199113817503153698842910998618601209801099102363635688071297957125372069437413258260292413/15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (106792478646103027254847305078183340042844795846915820794341360494844207649030419486429965589211598067022286147572687409387554659363636725209851678509/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell101Term01

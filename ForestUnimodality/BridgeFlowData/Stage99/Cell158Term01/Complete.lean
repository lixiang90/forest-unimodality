import ForestUnimodality.BridgeFlowData.Stage99.Cell158Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell158Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=10 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (1581382121734983958940426009190485803/2500000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (1137916866930038828750826383066679172851/625000000000000000000000000000000000000)

def table : Table :=
  ⟨10, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-2925519798392569/3750000000000000), 64, (358080058375053495189889914574599735141213975863/781250000000000000000000000000000000000000000000), (9166849494401369476861181813109753219615077782093/20000000000000000000000000000000000000000000000000)⟩, (45913500688889019096964850053898615567750100668588344973769200326368360277256273988133384605633000246361687647691291250615584008088066608060647/476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (770300718373639873417904233761868715481106072938701497385232012008677218958876666117994189646114954653597144420473631174852150193844509218406358357/8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell158Term01
